use super::*;

impl Parser<'_> {
    fn parse_rule_target(&mut self) -> bool {
        match self.current() {
            Some(DOLLAR) => {
                self.parse_variable_reference();
                true
            }
            // A backslash is part of the target name. Both GNU and BSD
            // make keep it, and it stops a following whitespace or `:`
            // from ending the name.
            Some(BACKSLASH) if !self.is_line_continuation() => {
                while self.current() == Some(BACKSLASH) && !self.is_line_continuation() {
                    self.bump();
                }
                if self.pending_backslash_escape && self.at_escapable_target_separator() {
                    self.bump_escaped_char();
                }
                true
            }
            Some(OPERATOR) if self.at_literal_bang() => {
                self.bump();
                true
            }
            Some(WHITESPACE | INDENT | NEWLINE | COMMENT | OPERATOR | BACKSLASH) | None => {
                self.error(
                    ParseErrorKind::MissingTarget,
                    "expected rule target".to_string(),
                );
                false
            }
            // Anything else is literal text in the target name, such as
            // `*` in `*.o: *.c` or the stray `}` in `${X}}`.
            Some(_) => {
                self.bump();
                true
            }
        }
    }

    /// Whether the current token starts with a character that ends a
    /// target name unless escaped with a backslash.
    fn at_escapable_target_separator(&self) -> bool {
        match self.current_token() {
            Some((WHITESPACE, _)) => true,
            Some((OPERATOR, op)) => op.starts_with(':') || self.at_bang_dependency_operator(),
            _ => false,
        }
    }

    /// Consume the first character of the current token as TEXT, as it
    /// is escaped by a preceding backslash, leaving the rest of the
    /// token as the current token.
    fn bump_escaped_char(&mut self) {
        let text = self.current_text().expect("at an escaped character");
        let len = text.chars().next().map_or(0, char::len_utf8);
        if len == text.len() {
            self.bump_as(TEXT);
        } else {
            self.bump_token_head_as(len, TEXT);
        }
    }

    /// Whether the current token is a `$$` escape, after which a `(` is
    /// literal rather than the start of an archive member list.
    fn at_dollar_escape(&self) -> bool {
        self.current() == Some(DOLLAR)
            && self.tokens.len() >= 2
            && self.tokens[self.tokens.len() - 2].kind == DOLLAR
    }

    /// Whether the parser is at nmake's `$$@` or `$$(@D)`, `$$(@B)`,
    /// `$$(@F)` or `$$(@R)`, which on a dependency line stand for the
    /// current target or a part of it.
    fn at_nmake_target_as_dependent(&self) -> bool {
        if self.variant != Some(MakefileVariant::NMake) || !self.at_dollar_escape() {
            return false;
        }
        let n = self.tokens.len();
        let token = |i: usize| {
            n.checked_sub(i)
                .map(|j| (self.tokens[j].kind, self.tokens[j].text))
        };
        match token(3) {
            Some((TEXT, "@")) => true,
            Some((LPAREN, _)) => {
                token(4) == Some((TEXT, "@"))
                    && matches!(token(5), Some((IDENTIFIER, "D" | "B" | "F" | "R")))
                    && matches!(token(6), Some((RPAREN, _)))
            }
            _ => false,
        }
    }

    /// Whether the `(` at the current token starts an archive member
    /// list. GNU make takes a `(` without a matching `)` as part of a
    /// plain file name, while BSD make rejects it.
    fn at_archive_member_list(&self) -> bool {
        if self.is_bsd_make() {
            return true;
        }
        // Look for the `)` as `parse_archive_member_list` would.
        let mut tokens = self.upcoming().skip(1).peekable();
        while let Some((kind, _)) = tokens.next() {
            match kind {
                RPAREN => return true,
                IDENTIFIER | TEXT | WHITESPACE => {}
                BACKSLASH if tokens.next_if(|(k, _)| *k == NEWLINE).is_some() => {
                    tokens.next_if(|(k, _)| *k == INDENT);
                }
                DOLLAR if Self::skip_variable_reference(&mut tokens) => {}
                _ => return false,
            }
        }
        false
    }

    /// Parse the parenthesized member list of an archive member
    /// reference such as `libfoo.a(bar.o baz.o)`, starting at the `(`.
    /// The archive name before it is left to the caller, as it may
    /// contain variable references.
    fn parse_archive_member_list(&mut self) {
        self.bump(); // (
        self.builder.start_node(ARCHIVE_MEMBERS.into());
        while self.current().is_some() && self.current() != Some(RPAREN) {
            // The member list may continue on the next physical line.
            if self.consume_line_continuation() {
                continue;
            }
            match self.current() {
                Some(IDENTIFIER) | Some(TEXT) => {
                    self.builder.start_node(ARCHIVE_MEMBER.into());
                    self.bump();
                    self.builder.finish_node();
                }
                Some(WHITESPACE) => self.bump(),
                Some(DOLLAR) => {
                    self.builder.start_node(ARCHIVE_MEMBER.into());
                    self.parse_variable_reference();
                    self.builder.finish_node();
                }
                _ => break,
            }
        }
        self.builder.finish_node();

        if self.current() == Some(RPAREN) {
            self.bump();
        } else {
            // Leave the token for the caller, which may be the line
            // ending or the dependency operator.
            self.record_error(
                ParseErrorKind::UnclosedArchiveMember,
                "expected ')' to close archive member".to_string(),
            );
        }
    }

    /// Parse a rule's prerequisites. If `target_locals` is set, stop at
    /// a source that starts a BSD make target-local assignment.
    fn parse_rule_dependencies(&mut self, target_locals: bool) {
        self.builder.start_node(PREREQUISITES.into());
        // Only the first `|` separates normal from order-only
        // prerequisites; GNU make takes any later one as a file name.
        // Other makes have no order-only prerequisites and take any `|`
        // as a file name.
        let mut seen_pipe = !self.gnu_directives_enabled();

        while self.current().is_some() && self.current() != Some(NEWLINE) {
            // The prerequisite list may continue on the next physical line.
            if self.consume_line_continuation() {
                continue;
            }
            match self.current() {
                Some(WHITESPACE) => {
                    self.bump(); // Consume whitespace between prerequisites
                }
                Some(COMMENT) => {
                    // Trailing comment ends the prerequisite list.
                    self.bump();
                }
                // The rest of the line after a `;` is the first recipe line.
                Some(TEXT) if self.at_text(";") => break,
                Some(TEXT) if !seen_pipe && self.at_text("|") => {
                    seen_pipe = true;
                    self.bump_as(OPERATOR);
                }
                Some(_) if target_locals && self.is_bsd_target_local_assignment() => break,
                Some(_) => {
                    // Collect contiguous non-whitespace tokens into one
                    // PREREQUISITE node, preserving structures like
                    // `$$(@:.out=.src)` or `lib(member.o)` as a single
                    // word.
                    self.parse_prerequisite_word(!seen_pipe);
                }
                None => break,
            }
        }

        self.builder.finish_node(); // End PREREQUISITES
    }

    /// Parse a single prerequisite word: consume tokens up to the next
    /// whitespace/newline/comment, descending into variable references
    /// (`$(...)`, `${...}`, `$X`, `$$`) and archive-member parentheses
    /// without treating them as word boundaries. If `stop_at_pipe` is
    /// set, a `|` that is not escaped with a backslash also ends the
    /// word.
    fn parse_prerequisite_word(&mut self, stop_at_pipe: bool) {
        self.builder.start_node(PREREQUISITE.into());

        // Whether a `(` here starts the member list of an archive member
        // reference such as `lib.a(m.o)` or `$(LIB)(m.o)`. It can't start
        // the word or follow a `$$`, and a word has only one. A word that
        // starts with `(` has none.
        let mut archive_allowed = false;
        let mut seen_archive = false;

        // Consume tokens until a separator. A line continuation ends the
        // word; the outer loop consumes it and resumes on the next
        // physical line.
        while let Some(kind) = self.current() {
            match kind {
                LPAREN if archive_allowed && !seen_archive && self.at_archive_member_list() => {
                    self.parse_archive_member_list();
                    seen_archive = true;
                    // BSD make ends the word at the `)`.
                    if self.is_bsd_make() {
                        break;
                    }
                }
                // GNU make takes a backslash-escaped space as part of
                // the name; BSD make splits sources at any whitespace.
                WHITESPACE if self.pending_backslash_escape && !self.is_bsd_make() => {
                    self.bump_escaped_char();
                }
                WHITESPACE | NEWLINE | COMMENT => break,
                BACKSLASH if self.is_line_continuation() => break,
                // GNU make takes `\|` as part of the name, but not `\;`.
                TEXT if self.at_text(";")
                    || (stop_at_pipe && self.at_text("|") && !self.pending_backslash_escape) =>
                {
                    break
                }
                // nmake's `$$@`, the target as a dependent: the first
                // `$` is followed by the reference `$@`.
                DOLLAR if self.at_nmake_target_as_dependent() => {
                    self.bump();
                    self.parse_variable_reference();
                }
                DOLLAR => {
                    let escape = self.at_dollar_escape();
                    self.parse_variable_reference();
                    archive_allowed = !escape;
                    continue;
                }
                LPAREN => {
                    seen_archive |= !archive_allowed;
                    self.bump();
                }
                _ => self.bump(),
            }
            archive_allowed = true;
        }

        self.builder.finish_node(); // End PREREQUISITE
    }

    /// The error BSD make reports for the line starting at the current
    /// token if it has no dependency operator. As BSD make tries
    /// directives first, a line starting with `.` is then an unknown
    /// directive, or an include with junk after the keyword such as
    /// `.includex "file"`.
    fn bsd_unknown_directive_error(&self) -> Option<(ParseErrorKind, String)> {
        if !self.is_bsd_make() {
            return None;
        }
        let start = usize::from(self.current_range().start());
        if start > 0 && !self.original_text[..start].ends_with('\n') {
            return None;
        }
        let mut rest = self.original_text[start..].strip_prefix('.')?;
        loop {
            let trimmed = rest.trim_start_matches([' ', '\t']);
            match trimmed.strip_prefix("\\\n") {
                Some(r) => rest = r,
                None => {
                    rest = trimmed;
                    break;
                }
            }
        }
        if rest
            .strip_prefix(['s', '-', 'd'])
            .unwrap_or(rest)
            .starts_with("include")
        {
            return Some((
                ParseErrorKind::UndelimitedIncludePath,
                ".include filename must be delimited by \"\" or <>".to_string(),
            ));
        }
        let len = rest
            .find(|c: char| !c.is_ascii_alphanumeric() && c != '-')
            .unwrap_or(rest.len());
        Some((
            ParseErrorKind::UnknownDirective,
            format!("Unknown directive \"{}\"", &rest[..len]),
        ))
    }

    /// `tab_indented` is whether the rule line starts with a tab, which
    /// GNU make reports as "recipe commences before first target"
    /// rather than "missing separator". `unknown_directive` is the error
    /// to report instead of a missing separator, if any.
    fn find_and_consume_colon(
        &mut self,
        tab_indented: bool,
        unknown_directive: Option<(ParseErrorKind, String)>,
    ) -> bool {
        // Skip whitespace before colon
        self.skip_ws();

        // Check if we're at a colon or double-colon
        if self.at_dependency_operator() {
            self.bump();
            return true;
        }

        if self.line_has_dependency_operator() {
            // Consume tokens until we find the colon (staying on same line)
            while self.current().is_some() && self.current() != Some(NEWLINE) {
                if self.at_dependency_operator() {
                    self.bump();
                    return true;
                }
                self.bump();
            }
        }

        let at_eol = self.current() == Some(NEWLINE);
        let (kind, message) = if tab_indented {
            (
                ParseErrorKind::RecipeBeforeFirstTarget,
                "expected ':'".to_string(),
            )
        } else {
            unknown_directive
                .unwrap_or((ParseErrorKind::MissingSeparator, "expected ':'".to_string()))
        };
        self.error(kind, message);
        if !at_eol {
            self.skip_logical_line();
        }
        false
    }

    pub(super) fn parse_rule(&mut self) {
        self.in_rule = RuleContext::Outside;
        self.builder.start_node(RULE.into());
        let tab_indented = self.at_tab_indented_line_start();
        let unknown_directive = self.bsd_unknown_directive_error();

        // Parse targets in a TARGETS node
        self.skip_ws();
        // BSD make takes the sources of most dependency lines that look
        // like an assignment as a target-local variable.
        let target_locals = self.is_bsd_make() && !self.at_bsd_special_sources_target();
        self.builder.start_node(TARGETS.into());
        // Both GNU and BSD make allow an empty list of targets, as in
        // `: source`.
        let has_target = self.at_dependency_operator() || self.parse_rule_targets();
        self.builder.finish_node();

        // BSD make reads `one two:=three` as the dependency operator `:`
        // followed by a target-local assignment `=three` with an empty
        // variable name, which it ignores. Likewise `:::=` is `::`
        // followed by `:=`, and `!=` is `!` followed by `=`.
        if has_target && self.bsd_directives_enabled() {
            self.skip_ws();
            if let Some((OPERATOR, op)) = self.current_token() {
                if matches!(op, ":=" | "::=" | ":::=" | "!=") {
                    self.pop_token();
                    let split = if op.starts_with("::") { 2 } else { 1 };
                    let (dependency_op, assignment_op) = op.split_at(split);
                    self.builder.token(OPERATOR.into(), dependency_op);
                    self.builder.start_node(VARIABLE.into());
                    self.builder.token(OPERATOR.into(), assignment_op);
                    self.skip_ws();
                    if self.is_bsd_make() {
                        let inline_recipe = self.parse_bsd_target_local_value();
                        self.parse_target_local_recipes(inline_recipe);
                    } else {
                        self.parse_assignment_value();
                        self.builder.finish_node(); // VARIABLE
                    }
                    self.builder.finish_node(); // RULE
                    return;
                }
            }
        }

        // Find and consume the colon
        let has_colon = if has_target {
            self.find_and_consume_colon(tab_indented, unknown_directive)
        } else {
            false
        };

        // Parse dependencies if we found both target and colon
        if has_target && has_colon {
            self.skip_ws();

            // Detect a target-specific variable assignment:
            //   target: VAR [op] value
            // by peeking IDENTIFIER (WS)? OPERATOR. If matched, treat
            // the line as a scoped assignment (no prerequisites, no
            // recipe) and produce a child VARIABLE node so callers can
            // use the existing VariableDefinition accessors.
            if self.looks_like_target_specific_assignment() {
                self.parse_target_specific_assignment();
            } else {
                if self.has_static_pattern_colon() {
                    self.parse_static_pattern();
                }
                if !(target_locals && self.is_bsd_target_local_assignment()) {
                    self.parse_rule_dependencies(target_locals);
                }
                if target_locals && self.is_bsd_target_local_assignment() {
                    let inline_recipe = self.parse_bsd_target_local_assignment();
                    self.parse_target_local_recipes(inline_recipe);
                } else {
                    if self.current() == Some(TEXT) && self.at_text(";") {
                        self.parse_inline_recipe();
                    } else {
                        self.expect_eol();
                    }
                    self.in_rule = RuleContext::Inside;
                    self.parse_rule_recipes();
                }
            }
        } else if has_target && self.is_bsd_make() {
            // BSD make starts a new, empty list of targets before parsing
            // a dependency line, so the commands after an invalid one
            // belong to no target, which is not an error.
            self.in_rule = RuleContext::Inside;
            self.parse_rule_recipes();
        }

        self.builder.finish_node();
    }

    /// Look ahead (without consuming) for a second, unescaped `:` in
    /// the prerequisites, which makes this a static pattern rule such as
    /// `$(OBJS): %.o: %.c`. Colons inside variable references, after an
    /// inline recipe's `;` or in a comment don't count.
    fn has_static_pattern_colon(&self) -> bool {
        // Only GNU make has static pattern rules; other makes take
        // `%.o:` as a file name.
        if !self.gnu_directives_enabled() {
            return false;
        }
        let mut escaped = self.pending_backslash_escape;
        let mut tokens = self.upcoming().peekable();
        while let Some((kind, text)) = tokens.next() {
            match (kind, text) {
                (OPERATOR, ":") if !escaped => return true,
                (BACKSLASH, _) if !escaped && matches!(tokens.peek(), Some((NEWLINE, _))) => {
                    tokens.next();
                    escaped = false;
                    continue;
                }
                (NEWLINE | COMMENT, _) | (TEXT, ";") => return false,
                (DOLLAR, _) if !Self::skip_variable_reference(&mut tokens) => return false,
                _ => {}
            }
            escaped = kind == BACKSLASH && !escaped;
        }
        false
    }

    /// Parse the target pattern of a static pattern rule and the colon
    /// that follows it.
    fn parse_static_pattern(&mut self) {
        while self.consume_line_continuation() {
            self.skip_ws();
        }
        self.builder.start_node(TARGET_PATTERN.into());
        loop {
            if self.consume_line_continuation() {
                continue;
            }
            match self.current() {
                Some(OPERATOR) if self.at_text(":") && !self.pending_backslash_escape => break,
                Some(WHITESPACE)
                    if self
                        .upcoming()
                        .find(|(kind, _)| *kind != WHITESPACE)
                        .is_some_and(|(kind, text)| kind == OPERATOR && text == ":") =>
                {
                    break
                }
                Some(DOLLAR) => self.parse_variable_reference(),
                Some(_) => self.bump(),
                None => break,
            }
        }
        self.builder.finish_node();
        self.skip_ws();
        self.bump();
        self.skip_ws();
    }

    /// Whether `tokens` starts with an `export`/`unexport`/`override`/
    /// `private` modifier followed by whitespace and the start of a
    /// variable name, as in `all: export CFLAGS = -O2`.
    fn at_assignment_modifier<'a, I>(mut tokens: std::iter::Peekable<I>) -> bool
    where
        I: Iterator<Item = (SyntaxKind, &'a str)> + Clone,
    {
        tokens
            .next()
            .is_some_and(|(kind, text)| kind == IDENTIFIER && is_assignment_modifier(text))
            && Self::skip_ws_and_continuation_tokens(&mut tokens)
            && matches!(tokens.peek(), Some((IDENTIFIER | DOLLAR | BACKSLASH, _)))
    }

    /// Look ahead (without consuming) for the
    /// `(MODIFIER WS)* NAME (WS)? OPERATOR` pattern that marks a
    /// target-specific variable assignment such as `all: CFLAGS = -O2`.
    /// NAME is what [`Self::parse_variable_name`] accepts, e.g.
    /// `obj-$(X)`. Line continuations may appear wherever WS may.
    /// BSD make's target-local variables follow different rules, see
    /// [`Self::parse_bsd_target_local_assignment`]; in other makes `X=1`
    /// after the colon is a prerequisite.
    fn looks_like_target_specific_assignment(&self) -> bool {
        if !matches!(self.variant, None | Some(MakefileVariant::GNUMake)) {
            return false;
        }
        // tokens is reversed (last = current), so iterate from the end.
        let mut tokens = self.upcoming().peekable();
        Self::skip_ws_and_continuation_tokens(&mut tokens);
        while Self::at_assignment_modifier(tokens.clone()) {
            tokens.next();
            Self::skip_ws_and_continuation_tokens(&mut tokens);
        }
        // GNU make starts the recipe at a `;` before the operator.
        if Self::skip_variable_name(&mut tokens, true) != Some(true) {
            return false;
        }
        Self::skip_ws_and_continuation_tokens(&mut tokens);
        tokens
            .next()
            .is_some_and(|(kind, text)| kind == OPERATOR && ASSIGNMENT_OPERATORS.contains(&text))
    }

    /// Advance `tokens` past a variable name, as accepted by
    /// [`Self::parse_variable_name`], or if `semicolon_ends` up to an
    /// unescaped `;`. Returns whether there was a name, or None if the
    /// line ends inside a variable reference.
    pub(super) fn skip_variable_name<'a, I>(
        tokens: &mut std::iter::Peekable<I>,
        semicolon_ends: bool,
    ) -> Option<bool>
    where
        I: Iterator<Item = (SyntaxKind, &'a str)> + Clone,
    {
        let mut seen_name = false;
        // Whether the previous token is an unescaped backslash.
        let mut escaped = false;
        loop {
            match tokens.peek().copied() {
                // A backslash is part of the name unless it continues
                // the line.
                Some((BACKSLASH, _))
                    if !escaped && matches!(tokens.clone().nth(1), Some((NEWLINE, _))) =>
                {
                    return Some(seen_name)
                }
                Some((DOLLAR, _)) => {
                    tokens.next();
                    if !Self::skip_variable_reference(tokens) {
                        return None;
                    }
                    seen_name = true;
                    escaped = false;
                    continue;
                }
                Some((_, text))
                    if semicolon_ends
                        && text
                            .char_indices()
                            .any(|(i, c)| c == ';' && (i > 0 || !escaped)) =>
                {
                    return Some(seen_name)
                }
                Some((kind, text)) if Self::is_gnu_name_token(kind, text) => {
                    escaped = kind == BACKSLASH && !escaped;
                }
                _ => return Some(seen_name),
            }
            tokens.next();
            seen_name = true;
        }
    }

    /// Whether a token can be part of a GNU make variable name, which may
    /// contain any characters but whitespace, `:`, `#` and `=`.
    pub(super) fn is_gnu_name_token(kind: SyntaxKind, text: &str) -> bool {
        match kind {
            WHITESPACE | NEWLINE | COMMENT | INDENT => false,
            OPERATOR => !text.contains([':', '=']),
            _ => true,
        }
    }

    /// Advance `tokens` past the rest of a variable reference whose `$`
    /// has just been consumed: `(...)`, `{...}` or the single character
    /// of `$X`. Returns false if the line ends before the reference does.
    /// Like [`Self::parse_variable_reference`], this takes a `$` inside
    /// the reference to start a nested one.
    fn skip_variable_reference<'a, I>(tokens: &mut std::iter::Peekable<I>) -> bool
    where
        I: Iterator<Item = (SyntaxKind, &'a str)>,
    {
        let close = match tokens.peek() {
            Some((LPAREN, _)) => RPAREN,
            Some((LBRACE, _)) => RBRACE,
            None | Some((NEWLINE, _)) => return false,
            // A `)` or `}` ends an enclosing reference instead.
            Some((RPAREN | RBRACE, _)) => return true,
            Some(_) => {
                tokens.next();
                return true;
            }
        };
        tokens.next();
        let open = if close == RPAREN { LPAREN } else { LBRACE };
        let mut depth = 1;
        let mut backslashes = 0;
        while let Some((kind, _)) = tokens.next() {
            if kind == BACKSLASH {
                backslashes += 1;
                continue;
            }
            let continued = backslashes % 2 == 1;
            backslashes = 0;
            match kind {
                // A line continuation inside a reference doesn't end it.
                NEWLINE if continued => {}
                NEWLINE => return false,
                DOLLAR if !Self::skip_variable_reference(tokens) => return false,
                k if k == open => depth += 1,
                k if k == close => {
                    depth -= 1;
                    if depth == 0 {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// Parse `VAR [op] value` after the rule's `:` colon, wrapped in a
    /// child `VARIABLE` node. Consumes through the end-of-line.
    fn parse_target_specific_assignment(&mut self) {
        self.builder.start_node(VARIABLE.into());
        self.skip_ws_and_continuations();
        while Self::at_assignment_modifier(self.upcoming().peekable()) {
            self.bump();
            self.skip_ws_and_continuations();
        }
        self.parse_variable_name();
        self.skip_ws_and_continuations();
        // Assignment operator.
        if self.current() == Some(OPERATOR) {
            self.bump();
        }
        // Optional whitespace before the value.
        self.skip_ws();
        self.parse_assignment_value();
        self.builder.finish_node(); // VARIABLE
    }

    /// Parse a BSD make target-local assignment in a dependency line, as
    /// in `prog: CFLAGS += -O2`, through the end of the line. Unlike in
    /// GNU make, it may follow other sources and the line may have
    /// commands. Whether make actually assigns the variable depends on
    /// `.MAKE.TARGET_LOCAL_VARIABLES` at that point, which is left to
    /// the caller. Returns whether the line has a command after `;`.
    fn parse_bsd_target_local_assignment(&mut self) -> bool {
        self.builder.start_node(VARIABLE.into());
        self.skip_ws_and_continuations();
        self.parse_bsd_variable_name();
        self.skip_ws();
        match self.sunsh_modifier() {
            Some((count, true)) => self.bump_merged(OPERATOR, count),
            sunsh => {
                if let Some((count, false)) = sunsh {
                    self.bump_n(count - 1);
                }
                self.skip_ws_and_continuations();
                if self.at_assignment_operator() {
                    self.bump();
                } else {
                    self.error(
                        ParseErrorKind::ExpectedAssignmentOperator,
                        "expected assignment operator".to_string(),
                    );
                }
            }
        }
        self.skip_ws();
        self.parse_bsd_target_local_value()
    }

    /// Parse the value of a BSD make target-local assignment, which ends
    /// at a `;` that starts a command, and finish the `VARIABLE` node.
    /// Returns whether there is such a command.
    fn parse_bsd_target_local_value(&mut self) -> bool {
        self.builder.start_node(EXPR.into());
        loop {
            match self.current() {
                None | Some(NEWLINE | COMMENT) => break,
                Some(TEXT) if self.at_text(";") => break,
                Some(DOLLAR) => self.parse_variable_reference(),
                _ if self.consume_line_continuation() => {}
                _ => self.bump(),
            }
        }
        self.builder.finish_node(); // EXPR
        if self.at_text(";") {
            self.builder.finish_node(); // VARIABLE
            self.parse_inline_recipe();
            true
        } else {
            self.expect_eol();
            self.builder.finish_node(); // VARIABLE
            false
        }
    }

    /// Parse the commands after a BSD make target-local assignment line.
    /// Unless the line has a command, the blank lines and comments after
    /// it only go in the rule if more commands follow, so that the tree
    /// is the same as for a GNU make target-specific assignment.
    fn parse_target_local_recipes(&mut self, inline_recipe: bool) {
        self.in_rule = RuleContext::Inside;
        if inline_recipe || self.recipe_continues() {
            self.parse_rule_recipes();
        }
    }

    /// Whether the line starts with a BSD make special target whose
    /// sources are never target-local assignments, as in
    /// `.SHELL: name=sh`.
    fn at_bsd_special_sources_target(&self) -> bool {
        let target: String = self
            .upcoming()
            .take_while(|(kind, _)| !matches!(kind, WHITESPACE | NEWLINE | OPERATOR))
            .map(|(_, text)| text)
            .collect();
        target.starts_with(".PATH")
            || matches!(
                target.as_str(),
                ".DELETE_ON_ERROR"
                    | ".INCLUDES"
                    | ".LIBS"
                    | ".MAKEFLAGS"
                    | ".MFLAGS"
                    | ".NOREADONLY"
                    | ".NOTPARALLEL"
                    | ".NO_PARALLEL"
                    | ".NULL"
                    | ".OBJDIR"
                    | ".READONLY"
                    | ".SHELL"
                    | ".SINGLESHELL"
                    | ".SUFFIXES"
                    | ".SYSPATH"
            )
    }

    fn parse_rule_targets(&mut self) -> bool {
        // As in parse_prerequisite_word, whether a `(` here starts the
        // member list of an archive member target.
        let mut archive_allowed = !self.at_dollar_escape();
        let mut seen_archive = self.current() == Some(LPAREN);

        if !self.parse_rule_target() {
            return false;
        }

        // Parse additional targets until we hit the colon
        loop {
            if self.current() == Some(WHITESPACE) {
                self.skip_ws();
                archive_allowed = false;
                seen_archive = false;
            }

            // Check if we're at a colon
            if self.at(OPERATOR, ":") {
                break;
            }

            // The target list may continue on the next physical line.
            if self.consume_line_continuation() {
                archive_allowed = false;
                seen_archive = false;
                continue;
            }

            match self.current() {
                Some(OPERATOR) if self.at_literal_bang() => self.bump(),
                Some(INDENT | NEWLINE | COMMENT | OPERATOR) | None => break,
                Some(LPAREN)
                    if archive_allowed && !seen_archive && self.at_archive_member_list() =>
                {
                    self.parse_archive_member_list();
                    seen_archive = true;
                }
                _ => {
                    // GNU make takes no archive name from a word that
                    // starts with `(`, and BSD make rejects one.
                    seen_archive |= self.current() == Some(LPAREN);
                    archive_allowed = !self.at_dollar_escape();
                    if !self.parse_rule_target() {
                        break;
                    }
                }
            }
        }

        true
    }
}
