use super::*;

/// A token of the input, with its text borrowed from it.
#[derive(Clone, Copy, Debug)]
pub(super) struct Token<'a> {
    pub(super) kind: SyntaxKind,
    pub(super) text: &'a str,
    /// The offset of `text` in the input.
    pub(super) start: rowan::TextSize,
}

impl Token<'_> {
    pub(super) fn range(&self) -> rowan::TextRange {
        rowan::TextRange::at(self.start, rowan::TextSize::of(self.text))
    }
}

/// Reverse `tokens` from the lexer, which start at `start` in the input,
/// into the order of the parser's token stack.
pub(super) fn token_stack<'a>(
    start: rowan::TextSize,
    tokens: Vec<(SyntaxKind, &'a str)>,
) -> Vec<Token<'a>> {
    let mut position = start;
    let mut tokens: Vec<_> = tokens
        .into_iter()
        .map(|(kind, text)| {
            let token = Token {
                kind,
                text,
                start: position,
            };
            position += rowan::TextSize::of(text);
            token
        })
        .collect();
    tokens.reverse();
    tokens
}

impl<'a> Parser<'a> {
    /// Text range of the current token, or an empty range at the end of
    /// the text if all tokens have been consumed.
    pub(super) fn current_range(&self) -> rowan::TextRange {
        match self.tokens.last() {
            Some(token) => token.range(),
            None => rowan::TextRange::empty(rowan::TextSize::of(self.original_text)),
        }
    }

    /// Remove the current token without adding it to the tree.
    pub(super) fn pop_token(&mut self) -> Option<Token<'a>> {
        self.tokens.pop()
    }

    /// Replace the current token with `tokens`, which make up its text,
    /// given in forward order.
    pub(super) fn replace_current_token(&mut self, tokens: Vec<(SyntaxKind, &'a str)>) {
        let start = self.pop_token().unwrap().start;
        self.tokens.extend(token_stack(start, tokens));
    }

    /// The kind and text of each token from the current one to the end
    /// of the input.
    pub(super) fn upcoming(&self) -> impl Iterator<Item = (SyntaxKind, &'a str)> + Clone + '_ {
        self.upcoming_from(self.tokens.len())
    }

    /// Like [`Self::upcoming`], starting at the token at `end - 1` in the
    /// token stack.
    pub(super) fn upcoming_from(
        &self,
        end: usize,
    ) -> impl Iterator<Item = (SyntaxKind, &'a str)> + Clone + '_ {
        self.tokens[..end]
            .iter()
            .rev()
            .map(|token| (token.kind, token.text))
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
            && self.tokens[self.tokens.len() - 2].kind == NEWLINE
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
        let token = self.tokens.last_mut().unwrap();
        let (head, tail) = token.text.split_at(len);
        token.text = tail;
        token.start += rowan::TextSize::of(head);
        self.pending_backslash_escape = false;
        self.builder.token(kind.into(), head);

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
        let text = self.pop_tokens(count);
        self.pending_backslash_escape = false;
        self.builder.token(kind.into(), text);
    }

    /// The text of the next `count` tokens.
    pub(super) fn next_tokens_text(&self, count: usize) -> &'a str {
        let rest = self.tokens.len() - count;
        match (self.tokens.last(), self.tokens.get(rest)) {
            (Some(first), Some(last)) => &self.original_text[first.range().cover(last.range())],
            _ => "",
        }
    }

    /// Remove the next `count` tokens without adding them to the tree,
    /// returning their text.
    pub(super) fn pop_tokens(&mut self, count: usize) -> &'a str {
        let text = self.next_tokens_text(count);
        self.tokens.truncate(self.tokens.len() - count);
        text
    }

    /// Consume the next `len` tokens, minus trailing whitespace, as a
    /// single IDENTIFIER token. Returns false if that leaves nothing.
    pub(super) fn bump_as_identifier(&mut self, len: usize) -> bool {
        let trailing_ws = self.tokens[self.tokens.len() - len..]
            .iter()
            .take_while(|token| token.kind == WHITESPACE)
            .count();
        let name = self.pop_tokens(len - trailing_ws);
        if name.is_empty() {
            return false;
        }
        self.pending_backslash_escape = false;
        self.builder.token(IDENTIFIER.into(), name);
        true
    }

    /// Advance one token, adding it to the current branch of the tree
    /// builder. A NEWLINE token ends the logical line.
    pub(super) fn bump(&mut self) {
        let token = self.pop_token().unwrap();
        // Track backslash-run parity: each backslash flips the flag, any
        // other token clears it. See `pending_backslash_escape`.
        self.pending_backslash_escape =
            escapes_next(token.kind == BACKSLASH, self.pending_backslash_escape);
        self.builder.token(token.kind.into(), token.text);
        if token.kind == NEWLINE {
            self.line_ends.push(token.range());
        }
    }

    /// Advance past a NEWLINE token that continues the logical line.
    pub(super) fn bump_continued_newline(&mut self) {
        let token = self.pop_token().unwrap();
        assert_eq!(token.kind, NEWLINE);
        self.pending_backslash_escape = false;
        self.builder.token(token.kind.into(), token.text);
    }

    /// Advance one token, adding it to the tree as `kind`.
    pub(super) fn bump_as(&mut self, kind: SyntaxKind) {
        let token = self.pop_token().unwrap();
        self.pending_backslash_escape = false;
        self.builder.token(kind.into(), token.text);
    }

    /// Peek at the first unprocessed token
    pub(super) fn current(&self) -> Option<SyntaxKind> {
        self.tokens.last().map(|token| token.kind)
    }

    /// The kind and text of the first unprocessed token.
    pub(super) fn current_token(&self) -> Option<(SyntaxKind, &'a str)> {
        self.tokens.last().map(|token| (token.kind, token.text))
    }

    /// The text of the first unprocessed token.
    pub(super) fn current_text(&self) -> Option<&'a str> {
        self.tokens.last().map(|token| token.text)
    }

    /// Whether the current token is of kind `kind` with text `text`.
    pub(super) fn at(&self, kind: SyntaxKind, text: &str) -> bool {
        self.current_token() == Some((kind, text))
    }

    /// Kind of the first non-whitespace token after the current one.
    pub(super) fn peek_past_ws(&self) -> Option<SyntaxKind> {
        self.upcoming()
            .skip(1)
            .map(|(kind, _)| kind)
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
