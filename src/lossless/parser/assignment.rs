use super::*;

impl Parser<'_> {
    /// For nmake, consume a caret at the end of a line of a macro
    /// definition, which continues the value with a newline, and the
    /// line break and indentation after it.
    fn consume_nmake_caret_newline(&mut self) -> bool {
        let n = self.tokens.len();
        if self.variant != Some(MakefileVariant::NMake)
            || n < 2
            || self.tokens[n - 1] != (TEXT, "^".to_string())
            || self.tokens[n - 2].0 != NEWLINE
        {
            return false;
        }
        self.bump(); // caret
        self.bump_continued_newline();
        if self.current() == Some(INDENT) {
            self.bump();
        }
        true
    }

    /// Whether the current token is an `export`/`unexport`/`override`/
    /// `private` modifier. A keyword directly followed by an operator is the
    /// variable name itself, as in `override := 1`.
    fn at_assignment_prefix_keyword(&self) -> bool {
        let enabled = match self.current_token() {
            Some((IDENTIFIER, "export")) if self.is_bsd_make() => true,
            Some((IDENTIFIER, word)) => {
                self.gnu_directives_enabled() && is_assignment_modifier(word)
            }
            _ => false,
        };
        enabled && self.peek_past_ws() != Some(OPERATOR)
    }

    pub(super) fn parse_assignment(&mut self) {
        self.in_rule = RuleContext::Outside;
        self.builder.start_node(VARIABLE.into());

        // Handle `export`/`unexport`/`override`/`private` modifiers, in
        // any order.
        self.skip_ws();
        // BSD make takes everything between a gmake-style `export` and
        // the `=` as the name, so `export override A = 1` exports a
        // variable named "override A".
        let bsd_gmake_export = self.is_bsd_make() && self.at_gmake_export();
        let mut is_export_directive = false;
        // Without an assignment only `export` and `unexport` can start
        // the line; GNU make rejects `override export X`.
        let bare_needs_export = self.at_assignment_prefix_keyword()
            && !matches!(self.current_text(), Some("export" | "unexport"));
        while self.at_assignment_prefix_keyword() {
            is_export_directive |= matches!(self.current_text(), Some("export" | "unexport"));
            self.bump();
            self.skip_ws_and_continuations();
            if bsd_gmake_export {
                break;
            }
        }

        // `undefine NAME`, unless followed by an operator as in
        // `undefine = 1`, which assigns to a variable named "undefine".
        let is_undefine = self.gnu_directives_enabled()
            && self.at(IDENTIFIER, "undefine")
            && self.peek_past_ws() != Some(OPERATOR);
        if is_undefine {
            self.bump();
            self.skip_ws_and_continuations();
        }

        // A bare "export"/"unexport" with no names applies to all
        // variables.
        let export_all =
            is_export_directive && matches!(self.current(), Some(NEWLINE | COMMENT) | None);
        if is_undefine && matches!(self.current(), Some(NEWLINE | COMMENT) | None) {
            self.record_error(
                ParseErrorKind::ExpectedVariableName,
                "empty variable name".to_string(),
            );
            self.expect_eol();
            self.builder.finish_node();
            return;
        }
        let has_name = if bsd_gmake_export {
            self.bump_gmake_export_name()
        } else {
            export_all || self.parse_variable_name()
        };
        if !has_name {
            self.error(
                ParseErrorKind::ExpectedVariableName,
                "expected variable name".to_string(),
            );
            self.builder.finish_node();
            return;
        }

        if is_undefine {
            // GNU make takes the rest of the line as a single name, so
            // `undefine A B` undefines the variable "A B" and
            // `undefine A = b` the variable "A = b".
            loop {
                match self.current() {
                    None | Some(NEWLINE | COMMENT) => break,
                    Some(DOLLAR) => self.parse_variable_reference(),
                    _ if self.consume_line_continuation() => {}
                    _ => self.bump(),
                }
            }
            self.expect_eol();
            self.builder.finish_node();
            return;
        }

        // BSD make's `:sh` modifier, as in `VAR :sh= cmd`. Together with
        // a following `=` it forms the shell assignment operator `:sh=`;
        // before any other operator it is ignored.
        self.skip_ws();
        if let Some((count, shell)) = self.sunsh_modifier() {
            if shell {
                self.bump_merged(OPERATOR, count);
                self.skip_ws();
                self.parse_assignment_value();
                self.builder.finish_node();
                return;
            }
            self.bump_n(count - 1);
        }

        // Skip whitespace and parse operator
        self.skip_ws_and_continuations();

        // A bare "export"/"unexport" directive may list several variables.
        // With an operator, as in `export A B = x`, GNU make exports each
        // word, including "=" and "x"; that is almost certainly a mistake,
        // so leave it to the operator check below to report.
        if is_export_directive && !self.has_assignment_operator_on_line() {
            loop {
                match self.current() {
                    Some(IDENTIFIER) => self.bump(),
                    Some(BACKSLASH) if !self.is_line_continuation() => self.bump(),
                    Some(DOLLAR) => self.parse_variable_reference(),
                    _ => break,
                }
                self.skip_ws_and_continuations();
            }
        }
        match self.current_token() {
            Some((OPERATOR, _)) if self.at_assignment_operator() => {
                self.bump();
                self.skip_ws();
                self.parse_assignment_value();
            }
            Some((OPERATOR, op)) => {
                let msg = format!("invalid assignment operator: {}", op);
                self.error(ParseErrorKind::ExpectedAssignmentOperator, msg);
            }
            Some((NEWLINE | COMMENT, _)) | None if bare_needs_export => {
                self.record_error(
                    ParseErrorKind::ExpectedAssignmentOperator,
                    "expected assignment operator".to_string(),
                );
                self.expect_eol();
            }
            // Bare "export VARNAME" without assignment operator is valid GNU Make
            Some((NEWLINE, _)) => {
                self.bump();
            }
            Some((COMMENT, _)) if is_export_directive => self.expect_eol(),
            None => {
                // EOF after export VARNAME is fine
            }
            _ => {
                self.error(
                    ParseErrorKind::ExpectedAssignmentOperator,
                    "expected assignment operator".to_string(),
                );
                self.skip_logical_line();
            }
        }

        self.builder.finish_node();
    }

    /// Parse a variable name, which may be built from several parts such
    /// as `CFLAGS.${PROG}` or `a\b`. Returns false if there is no name.
    pub(super) fn parse_variable_name(&mut self) -> bool {
        // Without a variant, only names that BSD make would accept get
        // its nesting rules: GNU make's name in `x{ = 1` is `x{`.
        if self.is_bsd_make() || (self.bsd_directives_enabled() && self.is_bsd_assignment_line()) {
            return self.parse_bsd_variable_name();
        }
        let at_name = |this: &Self| match this.current_token() {
            // A backslash is part of the name unless it continues the line.
            Some((BACKSLASH, _)) => !this.is_line_continuation(),
            Some((kind, text)) => Self::is_gnu_name_token(kind, text),
            None => false,
        };
        if !at_name(self) {
            return false;
        }
        while at_name(self) {
            if self.current() == Some(DOLLAR) {
                self.parse_variable_reference();
            } else {
                self.bump();
            }
        }
        true
    }

    /// Parse a variable name as BSD make does: it may contain almost any
    /// character, as in `EXP.[A-]`, and be empty, as in `!= command` to
    /// run a command while parsing. Returns false if there is no name and
    /// no assignment operator.
    pub(super) fn parse_bsd_variable_name(&mut self) -> bool {
        if matches!(self.current(), None | Some(NEWLINE | COMMENT | WHITESPACE))
            || self.is_line_continuation()
        {
            return false;
        }
        // Like `Parse_IsVar`, let the level go negative, so that the name
        // in `a}b{ = 1` is `a}b{`.
        let mut level = 0isize;
        loop {
            match self.current() {
                None | Some(NEWLINE | COMMENT) => return true,
                // A backslash is part of the name unless it continues
                // the line.
                Some(BACKSLASH) if self.is_line_continuation() => return true,
                Some(WHITESPACE) if level == 0 => return true,
                Some(OPERATOR)
                    if level == 0
                        && self.is_bsd_make()
                        && self.current_text().is_some_and(is_colons_before_subst) =>
                {
                    let len = self.current_text().expect("checked in the guard").len();
                    self.bump_token_head(len - ":=".len());
                    return true;
                }
                Some(OPERATOR) if level == 0 && self.at_assignment_operator() => return true,
                Some(OPERATOR)
                    if level == 0 && self.sunsh_modifier().is_some_and(|(_, shell)| shell) =>
                {
                    return true
                }
                Some(DOLLAR) => {
                    // Parse_IsVar counts the parentheses and braces in
                    // expressions too, although make may end an
                    // expression before its braces balance, as in
                    // `${:UVAR{value}}`.
                    let start = usize::from(self.current_range().start());
                    self.parse_variable_reference();
                    let end = usize::from(self.current_range().start());
                    level += self.original_text[start..end]
                        .chars()
                        .map(|c| match c {
                            '(' | '{' => 1,
                            ')' | '}' => -1,
                            _ => 0,
                        })
                        .sum::<isize>();
                }
                Some(kind) => {
                    match kind {
                        LPAREN | LBRACE => level += 1,
                        RPAREN | RBRACE => level -= 1,
                        _ => {}
                    }
                    self.bump();
                }
            }
        }
    }

    /// Parse an assignment's value through the end of the logical line,
    /// creating nested EXPR nodes for variable references. A trailing
    /// `# comment` is left as a sibling COMMENT token, not bundled into
    /// the EXPR.
    pub(super) fn parse_assignment_value(&mut self) {
        self.builder.start_node(EXPR.into());
        while self.current().is_some()
            && self.current() != Some(NEWLINE)
            && self.current() != Some(COMMENT)
        {
            // The value may continue on the next physical line.
            if self.consume_line_continuation() || self.consume_nmake_caret_newline() {
                continue;
            }
            if self.current() == Some(DOLLAR) {
                self.parse_variable_reference();
            } else {
                self.bump();
            }
        }
        self.builder.finish_node();

        // Optional trailing comment.
        if self.current() == Some(COMMENT) {
            self.bump();
        }

        // Expect newline
        if self.current() == Some(NEWLINE) {
            self.bump();
        } else if !self.is_at_eof() {
            self.error(
                ParseErrorKind::ExtraneousText,
                "expected newline after variable value".to_string(),
            );
        }
    }

    /// If the current token starts BSD make's `:sh` assignment modifier,
    /// as in `VAR :sh= cmd`, return the number of tokens up to and
    /// including the assignment operator that follows it, and whether
    /// they form the shell assignment operator `:sh=`. The modifier may
    /// be repeated, as in `VAR :sh :sh=`. As in BSD make, it may also be
    /// followed by a group of parentheses and braces, as in
    /// `VAR :sh(comment)=`, after which the operator is a plain `=`.
    pub(super) fn sunsh_modifier(&self) -> Option<(usize, bool)> {
        if !self.bsd_directives_enabled() {
            return None;
        }
        let mut tokens = self.tokens.iter().rev().enumerate();
        let mut seen = false;
        let mut shell = false;
        let mut level = 0usize;
        loop {
            let (i, (kind, text)) = tokens.next()?;
            match (*kind, text.as_str()) {
                (NEWLINE, _) => return None,
                (LPAREN | LBRACE, _) if seen => {
                    level += 1;
                    shell = false;
                }
                (RPAREN | RBRACE, _) if level > 0 => level -= 1,
                _ if level > 0 => {}
                (OPERATOR, ":") => match tokens.next()? {
                    (_, (IDENTIFIER, name)) if name == "sh" => {
                        seen = true;
                        shell = true;
                    }
                    _ => return None,
                },
                (WHITESPACE, _) if seen => {}
                (OPERATOR, op) if seen && ASSIGNMENT_OPERATORS.contains(&op) => {
                    return Some((i + 1, shell && op == "="));
                }
                _ => return None,
            }
        }
    }

    /// Skip the lines of the `define` block starting at the current
    /// line, up to and including its `endef` line, finding its end as
    /// [`Self::parse_define`] does.
    pub(super) fn skip_define_lines(&mut self) {
        self.skip_logical_line();
        let mut depth: usize = 1;
        while !self.is_at_eof() {
            match self.first_token_on_line() {
                Some("endef") => depth -= 1,
                Some("define") => depth += 1,
                _ => {}
            }
            self.skip_logical_line();
            if depth == 0 {
                break;
            }
        }
    }

    /// Parse a `define`/`endef` multi-line variable definition.
    ///
    /// Produces a `VARIABLE` node structured like a regular assignment:
    ///
    /// - the `define` keyword itself (kept as an `IDENTIFIER` token);
    /// - the variable's name, with any variable references in it as
    ///   EXPR nodes;
    /// - the assignment operator (defaults to `=` if absent);
    /// - an `EXPR` node containing the verbatim body (without the
    ///   surrounding newlines that bracket it);
    /// - the closing `endef` token.
    ///
    /// Because the body is wrapped in an `EXPR` node, the existing
    /// `VariableDefinition::name()` / `assignment_operator()` /
    /// `raw_value()` accessors work transparently for `define` blocks.
    pub(super) fn parse_define(&mut self) {
        self.in_rule = RuleContext::Outside;
        // GNU make reports a missing endef at the define line.
        let start = self.current_range();
        self.builder.start_node(VARIABLE.into());

        // Consume any `override`/`export`/`unexport`/`private` modifiers and the
        // `define` keyword itself.
        while matches!(self.current_token(), Some((IDENTIFIER, t)) if is_assignment_modifier(t)) {
            self.bump();
            self.skip_ws_and_continuations();
        }
        self.bump();
        // Optional whitespace then the variable name.
        self.skip_ws_and_continuations();
        self.parse_define_name();
        self.skip_ws_and_continuations();
        // Optional assignment operator (e.g. `:=`, `+=`, `?=`).
        if self.current() == Some(OPERATOR) {
            self.bump();
        }
        self.parse_directive_line_end("define", false);

        // The body of the define lives in an EXPR node so that
        // `raw_value()` returns it. We consume token-by-token until we
        // see an `endef` line at depth 0, tracking nested `define`.
        let mut depth: usize = 1;
        self.with_references(EXPR, TextContext::DefineBody, |p| {
            while !p.is_at_eof() {
                match p.first_token_on_line() {
                    Some("endef") => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                        p.bump_endef_keyword();
                        p.parse_directive_line_end("endef", true);
                        continue;
                    }
                    Some("define") => depth += 1,
                    _ => {}
                }
                // Consume one line into the EXPR body. Like make, join
                // continued lines, so a continued line hides an `endef`.
                p.skip_logical_line();
            }
        });

        // Consume the closing `endef` line itself (if we found it).
        if depth == 0 {
            self.bump_endef_keyword();
            self.parse_directive_line_end("endef", false);
        } else {
            self.builder.start_node(ERROR.into());
            let line = self.line_at(start.start());
            self.push_error(
                ParseErrorKind::MissingEndef,
                "missing `endef` for `define`".to_string(),
                start,
                line,
            );
            self.builder.finish_node();
        }

        self.builder.finish_node();
    }

    /// Parse the name in a `define` header.
    ///
    /// GNU make takes everything up to the assignment operator (or the end
    /// of the line), minus surrounding whitespace, as the name. An
    /// operator only counts after a single word, so `define A B =` names
    /// the variable "A B =".
    fn parse_define_name(&mut self) {
        let mut depth = 0;
        let mut multiword = false;
        if !self.parse_define_name_part(&mut depth, &mut multiword) {
            self.record_error(
                ParseErrorKind::ExpectedVariableName,
                "empty variable name in `define`".to_string(),
            );
            return;
        }
        loop {
            self.skip_ws();
            if !self.consume_line_continuation() {
                return;
            }
            self.skip_ws_and_continuations();
            match self.current() {
                None | Some(NEWLINE | COMMENT) => return,
                Some(OPERATOR) if depth == 0 && !multiword => return,
                _ => {}
            }
            multiword |= depth == 0;
            let bumped = self.parse_define_name_part(&mut depth, &mut multiword);
            debug_assert!(bumped, "name part after a continuation is empty");
        }
    }

    /// Parse the part of a `define` name up to the next line
    /// continuation, operator or end of line, leaving trailing
    /// whitespace. As in an ordinary assignment's name, variable
    /// references become EXPR nodes. Each word between them is merged
    /// into a single IDENTIFIER token, so that `\n` (BACKSLASH +
    /// IDENTIFIER) reads as one word and the `=` in a name like `A B =`
    /// is not mistaken for the assignment operator. Returns false if the
    /// part is empty.
    fn parse_define_name_part(&mut self, depth: &mut usize, multiword: &mut bool) -> bool {
        let mut word = String::new();
        let mut parsed = false;
        while let Some(kind) = self.current() {
            let at_end = match kind {
                NEWLINE | COMMENT => true,
                OPERATOR => *depth == 0 && !*multiword,
                _ => self.is_line_continuation(),
            };
            if at_end {
                break;
            }
            match kind {
                DOLLAR => {
                    self.flush_define_name_word(&mut word);
                    self.parse_variable_reference();
                }
                WHITESPACE if *depth == 0 => {
                    if self.define_name_part_ends_after_ws(*multiword) {
                        break;
                    }
                    self.flush_define_name_word(&mut word);
                    *multiword = true;
                    self.bump();
                }
                _ => {
                    match kind {
                        LPAREN | LBRACE => *depth += 1,
                        RPAREN | RBRACE => *depth = depth.saturating_sub(1),
                        _ => {}
                    }
                    let (_, text) = self.pop_token().unwrap();
                    self.pending_backslash_escape =
                        escapes_next(kind == BACKSLASH, self.pending_backslash_escape);
                    word.push_str(&text);
                }
            }
            parsed = true;
        }
        self.flush_define_name_word(&mut word);
        parsed
    }

    /// Add the text collected by [`Self::parse_define_name_part`] as an
    /// IDENTIFIER token.
    fn flush_define_name_word(&mut self, word: &mut String) {
        if !word.is_empty() {
            self.builder.token(IDENTIFIER.into(), &std::mem::take(word));
        }
    }

    /// Whether the part of a `define` name ends at the whitespace at the
    /// current position, because a line continuation, the end of the
    /// line or, after a single word, an operator follows it.
    fn define_name_part_ends_after_ws(&self, multiword: bool) -> bool {
        let mut rest = self
            .tokens
            .iter()
            .rev()
            .map(|(kind, _)| *kind)
            .skip_while(|kind| *kind == WHITESPACE);
        match rest.next() {
            None | Some(NEWLINE | COMMENT) => true,
            Some(OPERATOR) => !multiword,
            Some(BACKSLASH) => rest.next() == Some(NEWLINE),
            Some(_) => false,
        }
    }

    /// Consume a gmake-style `export` name in BSD make, which is
    /// everything up to the operator, as a single IDENTIFIER token.
    /// Returns false if the name is empty.
    fn bump_gmake_export_name(&mut self) -> bool {
        let mut tokens = self.tokens.iter().rev().peekable();
        let mut len = 0;
        let mut escaped = false;
        while let Some((kind, _)) = tokens.peek() {
            let at_continuation = *kind == BACKSLASH
                && !escaped
                && matches!(tokens.clone().nth(1), Some((NEWLINE, _)));
            if at_continuation || matches!(*kind, OPERATOR | NEWLINE | COMMENT) {
                break;
            }
            escaped = *kind == BACKSLASH && !escaped;
            tokens.next();
            len += 1;
        }
        self.bump_as_identifier(len)
    }

    /// Consume an `endef` keyword and any indentation before it.
    fn bump_endef_keyword(&mut self) {
        while matches!(self.current(), Some(WHITESPACE | INDENT)) {
            self.bump();
        }
        self.bump();
    }

    /// Whether the current line starts a `define` block, optionally
    /// preceded by modifiers such as `override define NAME`. `define = 1`
    /// instead assigns to a variable named "define".
    pub(super) fn is_define_line(&self) -> bool {
        if !self.gnu_directives_enabled() {
            return false;
        }
        let mut tokens = self.tokens.iter().rev().peekable();
        loop {
            Self::skip_ws_and_continuation_tokens(&mut tokens);
            match tokens.next() {
                // As for other directives, `define:` is a rule.
                Some((IDENTIFIER, text)) if text == "define" => {
                    let mut after = tokens.clone();
                    match after.next() {
                        None | Some((WHITESPACE | NEWLINE | COMMENT, _)) => {}
                        Some((BACKSLASH, _)) if matches!(after.next(), Some((NEWLINE, _))) => {}
                        _ => return false,
                    }
                    Self::skip_ws_and_continuation_tokens(&mut tokens);
                    return !matches!(
                        tokens.next(),
                        Some((OPERATOR, op)) if ASSIGNMENT_OPERATORS.contains(&op.as_str())
                    );
                }
                Some((IDENTIFIER, text)) if is_assignment_modifier(text) => {}
                _ => return false,
            }
        }
    }

    /// Return the text of the first non-whitespace token on the current
    /// line, if it is an identifier followed by whitespace, a line
    /// continuation or the end of the line. Used to detect
    /// `define`/`endef` in a define body, where make does not strip
    /// comments first, so `endef#c` is not `endef`.
    fn first_token_on_line(&self) -> Option<&str> {
        let mut tokens = self
            .tokens
            .iter()
            .rev()
            .skip_while(|(kind, _)| matches!(*kind, WHITESPACE | INDENT));
        let (kind, text) = tokens.next()?;
        if *kind != IDENTIFIER {
            return None;
        }
        match tokens.next().map(|(kind, _)| *kind) {
            None | Some(WHITESPACE | NEWLINE) => Some(text.as_str()),
            Some(BACKSLASH) if matches!(tokens.next(), Some((NEWLINE, _))) => Some(text.as_str()),
            _ => None,
        }
    }
}
