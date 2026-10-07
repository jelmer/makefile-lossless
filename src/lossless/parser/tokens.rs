use super::*;

/// A token's kind and text.
type Token = (SyntaxKind, String);

/// A token's start and end.
type TokenRange = (rowan::TextSize, rowan::TextSize);

/// Reverse `tokens`, which start at `start`, into the order of the parser's
/// token stack, along with their positions in the same order.
pub(super) fn token_stack(
    start: rowan::TextSize,
    mut tokens: Vec<Token>,
) -> (Vec<Token>, Vec<TokenRange>) {
    let mut position = start;
    let mut positions: Vec<_> = tokens
        .iter()
        .map(|(_, text)| {
            let start = position;
            position += rowan::TextSize::of(text.as_str());
            (start, position)
        })
        .collect();
    tokens.reverse();
    positions.reverse();
    (tokens, positions)
}

impl Parser<'_> {
    /// Text range of the current token, or an empty range at the end of
    /// the text if all tokens have been consumed.
    pub(super) fn current_range(&self) -> rowan::TextRange {
        debug_assert_eq!(self.tokens.len(), self.token_positions.len());
        match self.token_positions.last() {
            Some(&(start, end)) => rowan::TextRange::new(start, end),
            None => rowan::TextRange::empty(rowan::TextSize::of(self.original_text)),
        }
    }

    /// Remove the current token without adding it to the tree.
    pub(super) fn pop_token(&mut self) -> Option<(SyntaxKind, String)> {
        self.token_positions.pop();
        self.tokens.pop()
    }

    /// Replace the current token with `tokens`, given in forward order.
    pub(super) fn replace_current_token(&mut self, tokens: Vec<(SyntaxKind, String)>) {
        let start = self.current_range().start();
        self.pop_token();
        let (tokens, positions) = token_stack(start, tokens);
        self.tokens.extend(tokens);
        self.token_positions.extend(positions);
    }

    /// Whether the current token's text is `text`.
    pub(super) fn at_text(&self, text: &str) -> bool {
        self.current_text() == Some(text)
    }

    /// Returns true if the current token is an unescaped BACKSLASH
    /// immediately followed by a NEWLINE (a line continuation). A backslash
    /// preceded by an odd run of backslashes is itself escaped (`\\`) and
    /// does not continue the line.
    pub(super) fn is_line_continuation(&self) -> bool {
        !self.pending_backslash_escape
            && self.current() == Some(BACKSLASH)
            && self.tokens.len() >= 2
            && self.tokens[self.tokens.len() - 2].0 == NEWLINE
    }

    /// Skip to the end of the logical line, for error recovery, so that
    /// the rest of the line isn't parsed as a new item.
    pub(super) fn skip_logical_line(&mut self) {
        while self.current().is_some() && self.current() != Some(NEWLINE) {
            if !self.consume_line_continuation() {
                self.bump();
            }
        }
        if self.current() == Some(NEWLINE) {
            self.bump();
        }
    }

    /// Consume a backslash-newline line continuation and any indentation on
    /// the continued line, so the caller keeps reading the logical line.
    /// Returns false if the current position is not a line continuation.
    pub(super) fn consume_line_continuation(&mut self) -> bool {
        if !self.is_line_continuation() {
            return false;
        }
        self.bump(); // backslash
        self.bump_continued_newline();
        if self.current() == Some(INDENT) {
            self.bump();
        }
        true
    }

    /// Consume the first `len` bytes of the current token, leaving the
    /// rest as the current token. If the rest starts an expression, it
    /// is lexed again so that the expression starts with a `$` token.
    pub(super) fn bump_token_head(&mut self, len: usize) {
        let kind = self.current().unwrap();
        self.bump_token_head_as(len, kind);
    }

    /// As [`Self::bump_token_head`], but adding the head to the tree as
    /// `kind`.
    pub(super) fn bump_token_head_as(&mut self, len: usize, kind: SyntaxKind) {
        let text = &mut self.tokens.last_mut().unwrap().1;
        let tail = text.split_off(len);
        let head = std::mem::replace(text, tail);
        self.token_positions.last_mut().unwrap().0 += rowan::TextSize::of(head.as_str());
        self.pending_backslash_escape = false;
        self.builder.token(kind.into(), &head);

        let Some(tail) = self.current_text().filter(|tail| tail.starts_with('$')) else {
            return;
        };
        let pieces = lex_non_recipe_line(tail, self.variant);
        self.replace_current_token(pieces);
    }

    pub(super) fn bump_n(&mut self, count: usize) {
        for _ in 0..count {
            self.bump();
        }
    }

    /// Consume `count` tokens as a single token of the given kind.
    pub(super) fn bump_merged(&mut self, kind: SyntaxKind, count: usize) {
        let mut text = String::new();
        for _ in 0..count {
            text.push_str(&self.pop_token().unwrap().1);
        }
        self.pending_backslash_escape = false;
        self.builder.token(kind.into(), &text);
    }

    /// Consume the next `len` tokens, minus trailing whitespace, as a
    /// single IDENTIFIER token. Returns false if that leaves nothing.
    pub(super) fn bump_as_identifier(&mut self, len: usize) -> bool {
        let trailing_ws = self.tokens[self.tokens.len() - len..]
            .iter()
            .take_while(|(kind, _)| *kind == WHITESPACE)
            .count();
        let mut name = String::new();
        for _ in 0..len - trailing_ws {
            let (_, text) = self.pop_token().unwrap();
            name.push_str(&text);
        }
        if name.is_empty() {
            return false;
        }
        self.pending_backslash_escape = false;
        self.builder.token(IDENTIFIER.into(), &name);
        true
    }

    /// Advance one token, adding it to the current branch of the tree
    /// builder. A NEWLINE token ends the logical line.
    pub(super) fn bump(&mut self) {
        let range = self.current_range();
        let (kind, text) = self.pop_token().unwrap();
        // Track backslash-run parity: each backslash flips the flag, any
        // other token clears it. See `pending_backslash_escape`.
        self.pending_backslash_escape =
            escapes_next(kind == BACKSLASH, self.pending_backslash_escape);
        self.builder.token(kind.into(), text.as_str());
        if kind == NEWLINE {
            self.line_ends.push(range);
        }
    }

    /// Advance past a NEWLINE token that continues the logical line.
    pub(super) fn bump_continued_newline(&mut self) {
        let (kind, text) = self.pop_token().unwrap();
        assert_eq!(kind, NEWLINE);
        self.pending_backslash_escape = false;
        self.builder.token(kind.into(), text.as_str());
    }

    /// Advance one token, adding it to the tree as `kind`.
    pub(super) fn bump_as(&mut self, kind: SyntaxKind) {
        let (_, text) = self.pop_token().unwrap();
        self.pending_backslash_escape = false;
        self.builder.token(kind.into(), text.as_str());
    }

    /// Peek at the first unprocessed token
    pub(super) fn current(&self) -> Option<SyntaxKind> {
        self.tokens.last().map(|(kind, _)| *kind)
    }

    /// The kind and text of the first unprocessed token.
    pub(super) fn current_token(&self) -> Option<(SyntaxKind, &str)> {
        self.tokens
            .last()
            .map(|(kind, text)| (*kind, text.as_str()))
    }

    /// The text of the first unprocessed token.
    pub(super) fn current_text(&self) -> Option<&str> {
        self.tokens.last().map(|(_, text)| text.as_str())
    }

    /// Whether the current token is of kind `kind` with text `text`.
    pub(super) fn at(&self, kind: SyntaxKind, text: &str) -> bool {
        self.current_token() == Some((kind, text))
    }

    /// Kind of the first non-whitespace token after the current one.
    pub(super) fn peek_past_ws(&self) -> Option<SyntaxKind> {
        self.tokens
            .iter()
            .rev()
            .skip(1)
            .map(|(kind, _)| *kind)
            .find(|kind| *kind != WHITESPACE)
    }

    pub(super) fn expect_eol(&mut self) {
        // Skip any whitespace before looking for a newline. A line
        // continuation is whitespace too.
        self.skip_ws_and_continuations();

        // GNU Make allows a comment at the end of a directive line.
        if self.current() == Some(COMMENT) {
            self.bump();
        }

        match self.current() {
            Some(NEWLINE) => {
                self.bump();
            }
            None => {
                // End of file is also acceptable
            }
            n => {
                self.error(
                    ParseErrorKind::ExtraneousText,
                    format!("expected newline, got {:?}", n),
                );
                self.skip_logical_line();
            }
        }
    }

    // Helper to check if we're at EOF
    pub(super) fn is_at_eof(&self) -> bool {
        self.current().is_none()
    }

    pub(super) fn skip_ws(&mut self) {
        while self.current() == Some(WHITESPACE) {
            self.bump()
        }
    }

    pub(super) fn skip_ws_and_continuations(&mut self) {
        loop {
            self.skip_ws();
            if !self.consume_line_continuation() {
                break;
            }
        }
    }
}
