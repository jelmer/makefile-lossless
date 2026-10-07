use super::*;

/// The logical line starting with `tokens`, as BSD make sees it when
/// parsing an expression: up to the end of the line or a comment, with each
/// line continuation and the indentation after it replaced by a space.
/// `escaped` is whether the first token is escaped by a backslash.
///
/// Returns the text, the source position of each token and its offset in
/// the text, and the source position of the end of the line, if there are
/// any tokens.
pub(crate) fn bsd_logical_line<S: AsRef<str>>(
    tokens: impl Iterator<Item = (SyntaxKind, S, rowan::TextRange)>,
    mut escaped: bool,
) -> (
    String,
    Vec<(rowan::TextSize, usize)>,
    Option<rowan::TextSize>,
) {
    let mut text = String::new();
    let mut starts = vec![];
    let mut end = None;
    let mut tokens = tokens.peekable();
    while let Some((kind, token, range)) = tokens.next() {
        let token = token.as_ref();
        starts.push((range.start(), text.len()));
        end = Some(range.end());
        match kind {
            NEWLINE | COMMENT => {
                end = Some(range.start());
                break;
            }
            BACKSLASH if !escaped && tokens.peek().is_some_and(|(k, _, _)| *k == NEWLINE) => {
                end = tokens.next().map(|(_, _, range)| range.end());
                if let Some((_, _, range)) = tokens.next_if(|(k, _, _)| *k == INDENT) {
                    end = Some(range.end());
                }
                text.push(' ');
                escaped = false;
                continue;
            }
            // A quoted string spanning lines. Its line continuation is not
            // replaced, so stop here.
            _ if token.contains('\n') => {
                end = Some(range.start());
                break;
            }
            _ => {}
        }
        escaped = kind == BACKSLASH && !escaped;
        text.push_str(token);
    }
    (text, starts, end)
}

impl Parser<'_> {
    /// Run `f`, which adds the children of a `kind` node, and add that
    /// node with the variable references in it as EXPR nodes, found as
    /// make finds them in text of the given context.
    pub(super) fn with_references(
        &mut self,
        kind: SyntaxKind,
        context: TextContext,
        f: impl FnOnce(&mut Self),
    ) {
        let outer = std::mem::replace(&mut self.builder, GreenNodeBuilder::new());
        self.builder.start_node(kind.into());
        f(self);
        self.builder.finish_node();
        let node = std::mem::replace(&mut self.builder, outer).finish();
        emit_node_with_references(&mut self.builder, &node, context, self.variant);
    }

    /// The offset of the current token in the rest of the logical line
    /// as BSD make sees it when parsing an expression, which is kept in
    /// `bsd_line`. The line is built once for all the expressions on it,
    /// so that a long line takes linear time.
    fn bsd_line_offset(&mut self) -> usize {
        let pos = self.current_range().start();
        if let Some(line) = self.bsd_line.as_ref().filter(|line| {
            line.token_edits == self.token_edits
                && line.starts.first().is_some_and(|(start, _)| *start <= pos)
                && pos < line.end
        }) {
            let i = line.starts.partition_point(|(start, _)| *start <= pos) - 1;
            let (start, offset) = line.starts[i];
            return offset + usize::from(pos - start);
        }
        self.bsd_line = Some(self.bsd_logical_line());
        0
    }

    /// The rest of the logical line, as BSD make sees it when parsing an
    /// expression; see [`bsd_logical_line`].
    pub(super) fn bsd_logical_line(&self) -> BsdLine {
        let tokens = self
            .tokens
            .iter()
            .rev()
            .zip(self.token_positions.iter().rev())
            .map(|((kind, token), &(start, end))| {
                (*kind, token.as_str(), rowan::TextRange::new(start, end))
            });
        let (text, starts, end) = bsd_logical_line(tokens, self.pending_backslash_escape);
        BsdLine {
            exprs: crate::reference::BsdExprLine::new(crate::reference::UnescapedHash::new(&text)),
            text,
            starts,
            end: end.unwrap_or_else(|| self.current_range().start()),
            token_edits: self.token_edits,
        }
    }

    /// Consume the tokens making up the next `len` bytes of the logical
    /// line from [`Self::bsd_logical_line`], splitting the last token if
    /// needed.
    fn bump_logical_bytes(&mut self, mut len: usize) {
        while len > 0 {
            if self.consume_line_continuation() {
                len -= 1;
                continue;
            }
            let token_len = self.current_text().expect("text comes from tokens").len();
            if token_len > len {
                self.bump_token_head(len);
                return;
            }
            len -= token_len;
            self.bump();
        }
    }

    /// Parse a BSD make expression, finding its end the way make does,
    /// which depends on its modifiers: the closing brace may appear
    /// unbalanced in a modifier as in `${X:S,},x,}`, and a `$` need not
    /// start a nested expression as in `${X:S/$/x/}`. Returns false
    /// without consuming anything if the expression is malformed.
    fn parse_bsd_variable_reference(&mut self) -> bool {
        let offset = self.bsd_line_offset();
        let mut line = self.bsd_line.take().expect("set by bsd_line_offset");
        let found = line.exprs.extent_at(offset);
        if let Some((end, nested)) = &found {
            self.emit_bsd_expr(&mut line.exprs, offset, *end, nested);
        }
        self.bsd_line = Some(line);
        found.is_some()
    }

    /// Add an EXPR node for the expression at `offset` in `line` of
    /// length `len`, which starts at the current token, with nodes for
    /// the expressions at `nested`, relative to `offset`. Each nested
    /// expression is parsed in the context of the rest of the line, as
    /// make parses it.
    fn emit_bsd_expr(
        &mut self,
        line: &mut crate::reference::BsdExprLine,
        offset: usize,
        len: usize,
        nested: &[std::ops::Range<usize>],
    ) {
        self.builder.start_node(EXPR.into());
        let mut pos = 0;
        for span in nested {
            self.bump_logical_bytes(span.start - pos);
            let inner_nested = match line.extent_at(offset + span.start) {
                Some((end, inner_nested)) if end == span.len() => inner_nested,
                _ => vec![],
            };
            self.emit_bsd_expr(line, offset + span.start, span.len(), &inner_nested);
            pos = span.end;
        }
        self.bump_logical_bytes(len - pos);
        self.builder.finish_node();
    }

    pub(super) fn parse_variable_reference(&mut self) {
        if self.reference_depth >= crate::reference::MAX_DEPTH {
            self.record_error(
                ParseErrorKind::TooDeeplyNested,
                "variable reference nested too deeply".to_string(),
            );
            self.parse_variable_reference_as_text();
            return;
        }
        self.reference_depth += 1;
        self.parse_variable_reference_inner();
        self.reference_depth -= 1;
    }

    /// Add the variable reference at the current `$` as an EXPR node
    /// without looking at what it contains, ending it at the brace that
    /// matches its opening one.
    fn parse_variable_reference_as_text(&mut self) {
        self.builder.start_node(EXPR.into());
        self.bump(); // Consume $
        let (open, close) = match self.current() {
            Some(LPAREN) => (LPAREN, RPAREN),
            Some(LBRACE) => (LBRACE, RBRACE),
            _ => {
                self.builder.finish_node();
                return;
            }
        };
        let mut depth = 0;
        loop {
            if self.consume_line_continuation() {
                continue;
            }
            if self.at_reference_end() {
                self.record_error(
                    ParseErrorKind::UnclosedReference,
                    "unclosed variable reference".to_string(),
                );
                break;
            }
            match self.current() {
                Some(kind) if kind == open => depth += 1,
                Some(kind) if kind == close => depth -= 1,
                _ => {}
            }
            self.bump();
            if depth == 0 {
                break;
            }
        }
        self.builder.finish_node();
    }

    fn parse_variable_reference_inner(&mut self) {
        if self.variant == Some(MakefileVariant::BSDMake) && self.parse_bsd_variable_reference() {
            return;
        }
        self.builder.start_node(EXPR.into());
        self.bump(); // Consume $

        if self.current() == Some(LPAREN) || self.current() == Some(LBRACE) {
            let is_brace = self.current() == Some(LBRACE);
            self.bump(); // Consume ( or {

            if is_brace {
                // For ${...}, consume until the matching }, allowing
                // balanced braces inside as in `${:UVAR{value}}`.
                let mut depth = 0;
                loop {
                    if self.consume_line_continuation() {
                        continue;
                    }
                    match self.current() {
                        Some(DOLLAR) => self.parse_variable_reference(),
                        Some(RBRACE) if depth == 0 => {
                            self.bump();
                            break;
                        }
                        Some(LBRACE) => {
                            depth += 1;
                            self.bump();
                        }
                        Some(RBRACE) => {
                            depth -= 1;
                            self.bump();
                        }
                        // Like `$(...)`, a reference can't span lines.
                        _ if self.at_reference_end() => {
                            self.record_error(
                                ParseErrorKind::UnclosedReference,
                                "unclosed variable reference".to_string(),
                            );
                            break;
                        }
                        _ => self.bump(),
                    }
                }
            } else {
                // Start by checking if this is a function like $(shell ...)
                // Common makefile functions
                let known_functions = [
                    "shell", "wildcard", "call", "eval", "file", "abspath", "dir",
                ];
                let is_function = matches!(
                    self.current_token(),
                    Some((IDENTIFIER, name)) if known_functions.contains(&name)
                );

                if self.at_nmake_substitution() {
                    // nmake's substitution strings can't invoke macros,
                    // so the reference ends at the first `)`.
                    loop {
                        match self.current() {
                            Some(RPAREN) => {
                                self.bump();
                                break;
                            }
                            Some(NEWLINE) | None => {
                                self.record_error(
                                    ParseErrorKind::UnclosedReference,
                                    "unclosed variable reference".to_string(),
                                );
                                break;
                            }
                            Some(_) => self.bump(),
                        }
                    }
                } else if is_function {
                    // Preserve the function name
                    self.bump();

                    // Parse the rest of the function call, handling nested variable references
                    self.consume_balanced_parens(1);
                } else {
                    // Handle regular variable references
                    self.parse_parenthesized_expr_internal(true);
                }
            }
        } else if !self.at_reference_end()
            && !matches!(self.current(), Some(RPAREN | RBRACE))
            && !self.is_line_continuation()
            && !(self.variant == Some(MakefileVariant::BSDMake)
                && self
                    .current_text()
                    .is_some_and(|text| text.starts_with(':')))
        {
            // Single character variable like $X or $$. A `)` or `}` is
            // left alone: make finds the end of an enclosing reference
            // before looking at what it contains. BSD make does not take
            // `:` as a name either, so `$:` is a lone `$` and a `:`. Only
            // the first character of a token such as `XY` or a run of
            // whitespace is the name, except for nmake's `$**`, which
            // the lexer reads as one token.
            let text = self
                .current_text()
                .expect("not at the end of the reference");
            let first_len = if self.variant == Some(MakefileVariant::NMake) && text == "**" {
                2
            } else {
                text.chars().next().unwrap().len_utf8()
            };
            if text.len() > first_len {
                self.bump_token_head(first_len);
            } else {
                self.bump();
            }
            // The backslash in `$\` is a name, so it doesn't escape
            // what follows.
            self.pending_backslash_escape = false;
        }
        // A `$` at the end of a line is accepted by both GNU and BSD
        // make; it expands to nothing. Make joins continued lines before
        // expanding them, so this includes a `$` before a backslash-newline.

        self.builder.finish_node();
    }

    /// Whether a variable reference ends before the current token: at
    /// the end of the line, or at the quote that ends a quoted `ifeq`
    /// argument.
    fn at_reference_end(&self) -> bool {
        match self.current_token() {
            None | Some((NEWLINE, _)) => true,
            Some((QUOTE, text)) => self.argument_quote.as_deref() == Some(text),
            _ => false,
        }
    }

    /// Whether the tokens after `$(` are an nmake macro substitution,
    /// `name:string1=string2`.
    fn at_nmake_substitution(&self) -> bool {
        let n = self.tokens.len();
        self.variant == Some(MakefileVariant::NMake)
            && n >= 2
            && matches!(self.tokens[n - 1].0, IDENTIFIER | TEXT)
            && self.tokens[n - 2].0 == OPERATOR
            && self.tokens[n - 2].1.starts_with(':')
    }

    // Helper method to parse a conditional comparison (ifeq/ifneq)
    // Supports both syntaxes: (arg1,arg2) and "arg1" "arg2"
    pub(super) fn parse_parenthesized_expr(&mut self) {
        self.builder.start_node(EXPR.into());

        // Check if we have parenthesized or quoted syntax
        if self.current() == Some(LPAREN) {
            // Parenthesized syntax: ifeq (arg1,arg2)
            let start = self.current_range().start();
            self.bump(); // Consume opening paren
            if self.parse_parenthesized_expr_internal(false) == Some(false) {
                // As in `ifeq ()` or `ifeq (a)`.
                let range = rowan::TextRange::new(start, self.current_range().start());
                let line = self.line_at(start);
                self.push_error(
                    ParseErrorKind::InvalidConditional,
                    "invalid syntax in conditional: expected two arguments separated by a comma"
                        .to_string(),
                    range,
                    line,
                );
            }
        } else if self.current() == Some(QUOTE) {
            // Quoted syntax: ifeq "arg1" "arg2" or ifeq 'arg1' 'arg2'
            self.parse_quoted_comparison();
        } else {
            self.record_error(
                ParseErrorKind::InvalidConditional,
                "expected opening parenthesis or quote".to_string(),
            );
            self.skip_invalid_condition();
        }

        self.builder.finish_node();

        // A trailing comment is not part of the condition.
        self.expect_eol();
    }

    /// Parse the rest of a parenthesized expression, after its opening
    /// parenthesis. Returns `None` if it is not closed on the line, and
    /// otherwise whether it contains a comma outside of nested
    /// parentheses and variable references.
    fn parse_parenthesized_expr_internal(&mut self, is_variable_ref: bool) -> Option<bool> {
        let mut paren_count = 1;
        let mut top_level_comma = false;
        // Each nested LPAREN opens an EXPR node that the matching RPAREN
        // closes. If EOF arrives before those RPARENs do, we must still
        // close them or the green tree ends up unbalanced (rowan panics
        // in GreenNodeBuilder::finish).
        let mut open_nested = 0u32;

        while paren_count > 0 {
            if self.consume_line_continuation() {
                continue;
            }
            match self.current() {
                Some(LPAREN) => {
                    paren_count += 1;
                    self.bump();
                    // Start a new expression node for nested parentheses
                    self.builder.start_node(EXPR.into());
                    open_nested += 1;
                }
                Some(RPAREN) => {
                    paren_count -= 1;
                    self.bump();
                    if paren_count > 0 {
                        self.builder.finish_node();
                        open_nested -= 1;
                    }
                }
                Some(DOLLAR) => {
                    // Handle variable references
                    self.parse_variable_reference();
                }
                Some(COMMA) => {
                    top_level_comma |= paren_count == 1;
                    self.bump();
                }
                // Leave the newline for the caller, like GNU make,
                // which does not let the reference span lines.
                _ if self.at_reference_end() => {
                    if is_variable_ref {
                        self.record_error(
                            ParseErrorKind::UnclosedReference,
                            "unclosed variable reference".to_string(),
                        );
                    } else {
                        self.record_error(
                            ParseErrorKind::UnclosedParenthesis,
                            "unclosed parenthesis".to_string(),
                        );
                    }
                    break;
                }
                _ => self.bump(),
            }
        }

        for _ in 0..open_nested {
            self.builder.finish_node();
        }
        (paren_count == 0).then_some(top_level_comma)
    }

    // Helper to handle nested parentheses and collect tokens until matching closing parenthesis
    fn consume_balanced_parens(&mut self, start_paren_count: usize) -> usize {
        let mut paren_count = start_paren_count;

        while paren_count > 0 {
            if self.consume_line_continuation() {
                continue;
            }
            match self.current() {
                Some(LPAREN) => {
                    paren_count += 1;
                    self.bump();
                }
                Some(RPAREN) => {
                    paren_count -= 1;
                    self.bump();
                }
                Some(DOLLAR) => {
                    // Handle nested variable references
                    self.parse_variable_reference();
                }
                _ if self.at_reference_end() => {
                    self.record_error(
                        ParseErrorKind::UnclosedReference,
                        "unclosed variable reference".to_string(),
                    );
                    break;
                }
                _ => self.bump(),
            }
        }

        paren_count
    }
}
