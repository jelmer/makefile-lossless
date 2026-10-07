use super::*;

/// Tracks rule context across the branches of a conditional. Only one
/// branch is taken, so each branch starts in the context from before the
/// conditional, and the context after it is the join of those at the end
/// of every path.
#[derive(Clone, Copy)]
pub(super) struct ConditionalRuleContext {
    outer: RuleContext,
    branches: Option<RuleContext>,
    has_else: bool,
}

impl ConditionalRuleContext {
    pub(super) fn new(outer: RuleContext) -> Self {
        Self {
            outer,
            branches: None,
            has_else: false,
        }
    }

    fn add_branch(&mut self, in_rule: RuleContext) {
        self.branches = Some(self.branches.map_or(in_rule, |b| b.join(in_rule)));
    }

    /// Start the next branch, given the rule context at the end of the
    /// previous one. Returns the rule context for the new branch.
    pub(super) fn next_branch(&mut self, in_rule: RuleContext, is_final_else: bool) -> RuleContext {
        self.add_branch(in_rule);
        self.has_else |= is_final_else;
        self.outer
    }

    /// Returns the rule context after the conditional, given the one at the
    /// end of its last branch.
    pub(super) fn end(mut self, in_rule: RuleContext) -> RuleContext {
        self.add_branch(in_rule);
        if !self.has_else {
            // No branch may be taken at all.
            self.add_branch(self.outer);
        }
        self.branches.expect("a branch was added")
    }

    /// A context for a BSD make `.for` loop, after which the rule context is
    /// the one at the end of its body.
    pub(super) fn for_loop() -> Self {
        Self {
            outer: RuleContext::Outside,
            branches: None,
            has_else: true,
        }
    }
}

impl Parser<'_> {
    /// Parse the arguments of `ifeq "a" "b"`. Each argument ends at the
    /// next quote of the kind that opened it; GNU make looks for it
    /// after stripping comments, and backslashes do not escape it.
    pub(super) fn parse_quoted_comparison(&mut self) {
        for (i, which) in ["first", "second"].into_iter().enumerate() {
            if i > 0 {
                self.skip_ws_and_continuations();
            }
            if self.current() != Some(QUOTE) {
                self.record_error(
                    ParseErrorKind::InvalidConditional,
                    format!("expected {which} quoted argument"),
                );
                self.skip_invalid_condition();
                return;
            }
            if !self.parse_quoted_argument() {
                self.record_error(
                    ParseErrorKind::InvalidConditional,
                    "invalid syntax in conditional: unterminated quoted argument".to_string(),
                );
                return;
            }
        }
    }

    /// Put the rest of an invalid `ifeq` condition, up to the end of the
    /// line or a comment, in an ERROR node.
    pub(super) fn skip_invalid_condition(&mut self) {
        if matches!(self.current(), None | Some(NEWLINE | COMMENT)) {
            return;
        }
        self.builder.start_node(ERROR.into());
        while !matches!(self.current(), None | Some(NEWLINE | COMMENT)) {
            if !self.consume_line_continuation() {
                self.bump();
            }
        }
        self.builder.finish_node();
    }

    /// Parse a quoted argument of `ifeq`, starting at its opening quote.
    /// Returns whether the closing quote was found on the logical line.
    /// Like GNU make, which finds the closing quote before expanding the
    /// argument, end the argument at a quote inside a variable reference
    /// too, leaving the reference unterminated.
    fn parse_quoted_argument(&mut self) -> bool {
        let quote = self
            .current_text()
            .expect("at the opening quote")
            .to_string();
        self.bump();
        self.argument_quote = Some(quote.clone());
        let found = self.parse_quoted_argument_rest(&quote);
        self.argument_quote = None;
        found
    }

    fn parse_quoted_argument_rest(&mut self, quote: &str) -> bool {
        loop {
            if self.consume_line_continuation() {
                continue;
            }
            match self.current_token() {
                Some((QUOTE, text)) if text == quote => {
                    self.bump();
                    return true;
                }
                None | Some((NEWLINE | COMMENT, _)) => return false,
                Some((DOLLAR, _)) => self.parse_variable_reference(),
                Some(_) => self.bump(),
            }
        }
    }

    fn parse_conditional_keyword(&mut self) -> Option<String> {
        let token = match self.current_token() {
            Some((IDENTIFIER, token)) => token.to_string(),
            _ => {
                self.error(
                    ParseErrorKind::InvalidConditional,
                    "expected conditional keyword (ifdef, ifndef, ifeq, or ifneq)".to_string(),
                );
                return None;
            }
        };
        if !is_gnu_conditional_start(&token) {
            // Reached for an `else` or `endif` outside of a conditional.
            let kind = match token.as_str() {
                "else" => ParseErrorKind::ElseWithoutIf,
                "endif" => ParseErrorKind::ExtraneousEndif,
                _ => ParseErrorKind::InvalidConditional,
            };
            self.error(kind, format!("unknown conditional directive: {}", token));
            return None;
        }

        self.bump();
        Some(token)
    }

    fn parse_simple_condition(&mut self) {
        self.builder.start_node(EXPR.into());

        // Skip any leading whitespace
        self.skip_ws();

        // GNU make accepts an empty condition and treats the variable as
        // undefined, so no name is required. It does require the
        // expanded argument to be at most a single word. A literal after
        // whitespace always survives expansion as a second word; anything
        // involving references is left to the evaluator.
        let mut seen_word = false;
        let mut after_separator = false;
        let mut reported_extra_word = false;

        loop {
            match self.current() {
                None | Some(NEWLINE | COMMENT) => break,
                // Leave whitespace before a trailing comment out of the
                // condition.
                Some(WHITESPACE)
                    if matches!(self.peek_past_ws(), None | Some(NEWLINE | COMMENT)) =>
                {
                    break
                }
                Some(WHITESPACE) => {
                    after_separator = seen_word;
                    self.skip_ws();
                }
                Some(BACKSLASH) if self.is_line_continuation() => {
                    after_separator = seen_word;
                    self.consume_line_continuation();
                }
                Some(DOLLAR) => {
                    seen_word = true;
                    self.parse_variable_reference();
                }
                Some(_) => {
                    if after_separator && !reported_extra_word {
                        reported_extra_word = true;
                        self.record_error(
                            ParseErrorKind::InvalidConditional,
                            "invalid syntax in conditional: expected a single variable name"
                                .to_string(),
                        );
                    }
                    seen_word = true;
                    self.bump();
                }
            }
        }

        self.builder.finish_node();

        // A trailing comment is not part of the condition.
        self.expect_eol();
    }

    /// Whether the `else` at `end - 1` in the token stack is an
    /// `else ifdef` etc. rather than a final `else`. As for other
    /// conditional keywords, whitespace must follow, so GNU make takes
    /// `else ifdef:` as an `else` with extraneous text.
    pub(super) fn is_else_if_at(&self, end: usize) -> bool {
        let mut next = end - 1;
        while next > 0 && self.tokens[next - 1].kind == WHITESPACE {
            next -= 1;
        }
        self.keyword_at(next, GNU_CONDITIONAL_STARTS)
    }

    /// Parse a nested conditional, or the `else` or `endif` of the one
    /// being parsed. Returns false if `token` is none of those.
    fn handle_conditional_token(&mut self, token: &str) -> bool {
        match token {
            token
                if is_gnu_conditional_start(token)
                    && matches!(self.variant, None | Some(MakefileVariant::GNUMake)) =>
            {
                self.parse_conditional();
                true
            }
            "else" => {
                self.builder.start_node(CONDITIONAL_ELSE.into());
                self.bump();
                self.skip_ws();

                // Check if this is "else <conditional>" (else ifdef, else ifeq, etc.)
                // Like CONDITIONAL_IF, the node includes the newline.
                if self.at_keyword(&["ifdef", "ifndef"]) {
                    self.bump();
                    self.skip_ws_and_continuations();
                    self.parse_simple_condition();
                } else if self.at_keyword(&["ifeq", "ifneq"]) {
                    self.bump();
                    self.skip_ws_and_continuations();
                    self.parse_parenthesized_expr();
                } else {
                    self.parse_directive_line_end("else", false);
                }

                self.builder.finish_node(); // finish CONDITIONAL_ELSE
                true
            }
            "endif" => {
                self.builder.start_node(CONDITIONAL_ENDIF.into());
                self.bump();
                self.parse_directive_line_end("endif", false);
                self.builder.finish_node(); // finish CONDITIONAL_ENDIF
                true
            }
            _ => false,
        }
    }

    pub(super) fn parse_conditional(&mut self) {
        if matches!(self.current_token(), Some((IDENTIFIER, t)) if is_gnu_conditional_start(t))
            && self.nesting_depth >= crate::reference::MAX_DEPTH
        {
            self.parse_too_deeply_nested_block();
            return;
        }
        self.builder.start_node(CONDITIONAL.into());

        // Start the initial conditional (ifdef/ifndef/ifeq/ifneq)
        self.builder.start_node(CONDITIONAL_IF.into());

        // Parse the conditional keyword
        let Some(token) = self.parse_conditional_keyword() else {
            self.skip_logical_line();
            self.builder.finish_node(); // finish CONDITIONAL_IF
            self.builder.finish_node(); // finish CONDITIONAL
            return;
        };

        // GNU make rejects `ifeq(a,b)`, which is still read as a
        // conditional for error recovery.
        if matches!(token.as_str(), "ifeq" | "ifneq")
            && matches!(self.current(), Some(LPAREN | QUOTE))
        {
            self.record_error(
                ParseErrorKind::MissingSeparator,
                format!("`{token}` must be followed by whitespace"),
            );
        }

        // Skip whitespace after keyword
        self.skip_ws_and_continuations();

        // Parse the condition based on keyword type
        match token.as_str() {
            "ifdef" | "ifndef" => {
                self.parse_simple_condition();
            }
            "ifeq" | "ifneq" => {
                self.parse_parenthesized_expr();
            }
            _ => unreachable!("Invalid conditional token"),
        }

        self.builder.finish_node(); // finish CONDITIONAL_IF

        self.nesting_depth += 1;
        let mut rule_context = ConditionalRuleContext::new(self.in_rule);
        let mut seen_final_else = false;
        let mut seen_endif = false;

        while !seen_endif && !self.is_at_eof() {
            let start = (self.current_range().start(), self.token_edits);
            match self.current() {
                Some(IDENTIFIER) => {
                    if let Some((name, count)) = self.directive() {
                        self.parse_directive(name, count);
                        continue;
                    }
                    if !self.at_conditional_keyword() {
                        self.parse_normal_content();
                        continue;
                    }
                    let token = self
                        .current_text()
                        .expect("at a conditional keyword")
                        .to_string();
                    match token.as_str() {
                        "else" => {
                            if seen_final_else {
                                self.record_error(
                                    ParseErrorKind::DuplicateElse,
                                    "only one `else` per conditional".to_string(),
                                );
                            }
                            let is_final = !self.is_else_if_at(self.tokens.len());
                            seen_final_else |= is_final;
                            self.in_rule = rule_context.next_branch(self.in_rule, is_final);
                        }
                        "endif" => {
                            self.in_rule = rule_context.end(self.in_rule);
                            seen_endif = true;
                        }
                        _ => {}
                    }
                    if !self.handle_conditional_token(&token) {
                        self.parse_normal_content();
                    }
                }
                Some(INDENT) => self.parse_indented_line(),
                Some(WHITESPACE) => self.bump(),
                Some(COMMENT) => self.parse_comment(),
                Some(NEWLINE) => self.bump(),
                Some(DOLLAR) => self.parse_normal_content(),
                Some(BACKSLASH) if self.is_variable_assignment_line() => self.parse_assignment(),
                Some(_) => {
                    // Be more tolerant of unexpected tokens in conditionals
                    self.bump();
                }
                None => unreachable!("loop condition excludes EOF"),
            }
            if self.current().is_some() && (self.current_range().start(), self.token_edits) == start
            {
                debug_assert!(false, "no progress in conditional body");
                self.error(
                    ParseErrorKind::Other,
                    "unexpected token in conditional".to_string(),
                );
            }
        }

        if !seen_endif {
            self.record_unterminated_error(
                ParseErrorKind::MissingEndif,
                "unterminated conditional (missing endif)".to_string(),
            );
        }

        self.nesting_depth -= 1;
        self.builder.finish_node();
    }

    /// Report text after a complete BSD make condition, such as `junk`
    /// in `.if 1 junk`, which make rejects as a malformed conditional.
    ///
    /// TODO: Report other syntax errors in the condition. BSD make only
    /// finds them in the branches it evaluates, and some real makefiles
    /// contain them, such as an unclosed `exists(` in an `.elif`.
    pub(super) fn check_bsd_condition(&mut self, line: &BsdLine) {
        let Err(error) = crate::bsd_condition::parse_bsd_condition(&line.text) else {
            return;
        };
        if !matches!(
            error.kind(),
            BsdConditionErrorKind::UnexpectedText | BsdConditionErrorKind::UnbalancedParenthesis
        ) {
            return;
        }
        let position = |text_offset: usize| {
            let i = line
                .starts
                .partition_point(|(_, offset)| *offset <= text_offset)
                - 1;
            let (start, offset) = line.starts[i];
            start + rowan::TextSize::try_from(text_offset - offset).unwrap()
        };
        let condition = line.text.trim_end();
        let start = position(error.offset);
        let range = rowan::TextRange::new(start, position(condition.len()));
        let line_number = self.line_at(start);
        self.push_error(
            ParseErrorKind::InvalidConditional,
            format!("Malformed conditional ({condition})"),
            range,
            line_number,
        );
    }

    /// Parse one line inside a BSD `.if` or `.for` body.
    pub(super) fn parse_block_item(&mut self) {
        match self.current() {
            Some(INDENT) => self.parse_indented_line(),
            Some(NEWLINE) => self.bump(),
            _ => {
                self.parse_token();
            }
        }
    }

    /// Parse a BSD `.if`/`.ifdef`/`.ifndef`/`.ifmake`/`.ifnmake` block,
    /// including any `.elif*`/`.else` branches and the closing `.endif`,
    /// or the equivalent nmake `!IF` ... `!ENDIF` block.
    ///
    /// Uses the same node kinds as GNU conditionals: `.elif*` and `.else`
    /// become CONDITIONAL_ELSE nodes and `.endif` a CONDITIONAL_ENDIF.
    pub(super) fn parse_block_conditional(&mut self, name: &str, count: usize) {
        if self.nesting_depth >= crate::reference::MAX_DEPTH {
            self.parse_too_deeply_nested_block();
            return;
        }
        self.builder.start_node(CONDITIONAL.into());
        self.builder.start_node(CONDITIONAL_IF.into());
        self.bump_n(count);
        self.parse_directive_argument(Some(name));
        self.builder.finish_node();

        let mut rule_context = ConditionalRuleContext::new(self.in_rule);
        self.block_conditional_depth += 1;
        self.nesting_depth += 1;

        loop {
            if self.is_at_eof() {
                let message = format!(
                    "unterminated {} (missing {})",
                    self.directive_display("if"),
                    self.directive_display("endif")
                );
                self.record_unterminated_error(ParseErrorKind::MissingEndif, message);
                break;
            }
            let Some((name, count)) = self.directive() else {
                self.parse_block_item();
                continue;
            };
            if is_bsd_elif(name) || name == "else" {
                self.in_rule = rule_context.next_branch(self.in_rule, name == "else");
            } else if name == "endif" {
                self.in_rule = rule_context.end(self.in_rule);
            }
            match name {
                _ if is_bsd_elif(name) => {
                    self.builder.start_node(CONDITIONAL_ELSE.into());
                    self.bump_n(count);
                    self.parse_directive_argument(Some(name));
                    self.builder.finish_node();
                }
                "else" => {
                    self.builder.start_node(CONDITIONAL_ELSE.into());
                    self.bump_n(count);
                    self.parse_bare_directive_end(name);
                    self.builder.finish_node();
                }
                "endif" => {
                    self.builder.start_node(CONDITIONAL_ENDIF.into());
                    self.bump_n(count);
                    self.parse_bare_directive_end(name);
                    self.builder.finish_node();
                    break;
                }
                // A `.for` body is plain text to make, so `.endfor` ends
                // the loop even if a conditional inside it is still open.
                "endfor" if self.for_depth > 0 => {
                    self.record_error(
                        ParseErrorKind::MissingEndif,
                        "unterminated .if (missing .endif)".to_string(),
                    );
                    self.in_rule = rule_context.end(self.in_rule);
                    break;
                }
                _ => self.parse_block_item(),
            }
        }

        self.block_conditional_depth -= 1;
        self.nesting_depth -= 1;
        self.builder.finish_node();
    }

    /// Add the conditional or loop starting at the current line, up to
    /// the line that closes it, as an ERROR node without looking at
    /// what it contains, as it is nested too deeply to parse
    /// recursively.
    pub(super) fn parse_too_deeply_nested_block(&mut self) {
        self.record_error(
            ParseErrorKind::TooDeeplyNested,
            "conditionals and loops nested too deeply".to_string(),
        );
        self.builder.start_node(ERROR.into());
        let mut depth = 0;
        loop {
            if self.is_define_line() {
                self.skip_define_lines();
                if self.is_at_eof() {
                    break;
                }
                continue;
            }
            match self.block_delimiter() {
                Some(true) => depth += 1,
                Some(false) => depth -= 1,
                None => {}
            }
            self.skip_logical_line();
            if depth == 0 || self.is_at_eof() {
                break;
            }
        }
        self.builder.finish_node();
    }

    /// Whether the current line opens (true) or closes (false) a
    /// conditional or loop, if it does either.
    fn block_delimiter(&self) -> Option<bool> {
        if let Some((name, _)) = self.directive() {
            return match name {
                _ if is_bsd_if(name) || name == "for" => Some(true),
                "endif" | "endfor" => Some(false),
                _ => None,
            };
        }
        let end = self.tokens.len()
            - self
                .upcoming()
                .take_while(|(kind, _)| *kind == WHITESPACE)
                .count();
        if !self.conditional_line_at(end) {
            return None;
        }
        match self.tokens[end - 1].text {
            "endif" => Some(false),
            token => is_gnu_conditional_start(token).then_some(true),
        }
    }
}
