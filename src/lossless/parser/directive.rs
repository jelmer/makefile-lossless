use super::*;

/// BSD make directives, without the leading dot.
const BSD_DIRECTIVES: &[&str] = &[
    "include",
    "-include",
    "sinclude",
    "dinclude",
    "if",
    "ifdef",
    "ifndef",
    "ifmake",
    "ifnmake",
    "elif",
    "elifdef",
    "elifndef",
    "elifmake",
    "elifnmake",
    "else",
    "endif",
    "for",
    "endfor",
    "break",
    "undef",
    "export",
    "export-all",
    "export-env",
    "export-literal",
    "unexport",
    "unexport-env",
    "error",
    "warning",
    "info",
];

pub(super) fn is_bsd_if(name: &str) -> bool {
    matches!(name, "if" | "ifdef" | "ifndef" | "ifmake" | "ifnmake")
}

pub(super) fn is_bsd_elif(name: &str) -> bool {
    matches!(
        name,
        "elif" | "elifdef" | "elifndef" | "elifmake" | "elifnmake"
    )
}

/// Map the keyword of an nmake preprocessing directive, `first` followed by
/// the next word `second` if any, to the name of the equivalent BSD make
/// directive, such as `elif` for `ELSEIF`. Also returns whether `second` is
/// part of the keyword, as in `!ELSE IF`.
pub(super) fn nmake_directive_name(
    first: &str,
    second: Option<&str>,
) -> Option<(&'static str, bool)> {
    let name = match first.to_ascii_lowercase().as_str() {
        "if" => "if",
        "ifdef" => "ifdef",
        "ifndef" => "ifndef",
        "elseif" => "elif",
        "elseifdef" => "elifdef",
        "elseifndef" => "elifndef",
        "else" => {
            let elif = match second.map(str::to_ascii_lowercase).as_deref() {
                Some("if") => "elif",
                Some("ifdef") => "elifdef",
                Some("ifndef") => "elifndef",
                _ => return Some(("else", false)),
            };
            return Some((elif, true));
        }
        "endif" => "endif",
        "include" => "include",
        "undef" => "undef",
        "error" => "error",
        "message" => "message",
        "cmdswitches" => "cmdswitches",
        _ => return None,
    };
    Some((name, false))
}

impl Parser<'_> {
    pub(super) fn parse_expression_statement(&mut self) {
        self.in_rule = RuleContext::Outside;
        self.builder.start_node(EXPRESSION_STATEMENT.into());
        while self.current() == Some(DOLLAR) {
            self.parse_variable_reference();
            self.skip_ws_and_continuations();
        }
        // When the references expand to nothing, make ignores the
        // rest of the line after a `;`.
        if self.current() == Some(TEXT) && self.at_text(";") {
            self.bump_as(OPERATOR);
            self.skip_ws();
            self.parse_text_to_eol(false);
        } else {
            self.expect_eol();
        }
        self.builder.finish_node();
    }

    pub(super) fn parse_include(&mut self) {
        // Unlike GNU make, BSD make doesn't end a rule's commands at an
        // include.
        if !self.is_bsd_make() {
            self.in_rule = RuleContext::Outside;
        }
        self.builder.start_node(INCLUDE.into());

        let directive = self.directive();
        // GNU make silently accepts an `include` without any file names,
        // unlike POSIX make, BSD make and nmake.
        let required = if let Some((_, count)) = directive {
            self.bump_n(count);
            true
        } else if self.current() == Some(IDENTIFIER)
            && ["include", "-include", "sinclude"].contains(&self.tokens.last().unwrap().1.as_str())
        {
            self.bump();
            !self.gnu_directives_enabled()
        } else {
            self.error(
                ParseErrorKind::Other,
                "expected include directive".to_string(),
            );
            self.builder.finish_node();
            return;
        };
        self.skip_ws_and_continuations();
        // nmake does not require delimiters.
        // TODO: Check nmake's handling of an unclosed `<` or `"`.
        if directive.is_some() && self.variant != Some(MakefileVariant::NMake) {
            self.check_include_delimiters();
        }
        self.parse_file_list("include", required);
        self.builder.finish_node();
    }

    /// Report a BSD make `.include` path that does not start with `<`
    /// or `"`, or lacks the closing delimiter on the same logical line.
    /// Like BSD make, this looks at the path before expansion, so
    /// `${X}` is not delimited, and the closing delimiter is looked for
    /// anywhere, even in a variable reference.
    fn check_include_delimiters(&mut self) {
        let close = match self.tokens.last() {
            Some((TEXT, open)) if open == "<" => '>',
            Some((QUOTE, open)) if open == "\"" => '"',
            // A missing path is reported by `parse_file_list`.
            None | Some((NEWLINE | COMMENT, _)) => return,
            Some(_) => {
                self.record_error(
                    ParseErrorKind::UndelimitedIncludePath,
                    ".include filename must be delimited by \"\" or <>".to_string(),
                );
                return;
            }
        };
        let mut prev = None;
        for (kind, text) in self.tokens.iter().rev().skip(1) {
            match kind {
                COMMENT => break,
                NEWLINE if prev != Some(BACKSLASH) => break,
                _ if text.contains(close) => return,
                _ => {}
            }
            prev = Some(*kind);
        }
        self.record_error(
            ParseErrorKind::UnclosedIncludePath,
            format!("unclosed .include filename, '{}' expected", close),
        );
    }

    /// Parse a GNU make `load` or `-load` directive into a LOAD node.
    pub(super) fn parse_load(&mut self) {
        self.in_rule = RuleContext::Outside;
        self.builder.start_node(LOAD.into());
        self.bump();
        self.skip_ws_and_continuations();
        // GNU make accepts a `load` without any objects.
        self.parse_file_list("load", false);
        self.builder.finish_node();
    }

    /// Parse the file names of an `include` or `load` directive into an
    /// EXPR node, followed by an optional comment and the newline. If
    /// `required` is set, an empty list is an error.
    fn parse_file_list(&mut self, directive: &str, required: bool) {
        self.builder.start_node(EXPR.into());
        let mut found_path = false;

        loop {
            match self.current() {
                None | Some(NEWLINE | COMMENT) => break,
                // Leave whitespace before a trailing comment out of the
                // path.
                Some(WHITESPACE)
                    if matches!(self.peek_past_ws(), None | Some(NEWLINE | COMMENT)) =>
                {
                    break
                }
                Some(WHITESPACE) => self.skip_ws(),
                Some(BACKSLASH) if self.is_line_continuation() => {
                    self.consume_line_continuation();
                }
                Some(DOLLAR) => {
                    found_path = true;
                    self.parse_variable_reference();
                }
                Some(_) => {
                    // Accept any token as part of the path
                    found_path = true;
                    self.bump();
                }
            }
        }

        if required && !found_path {
            self.record_error(
                ParseErrorKind::MissingIncludePath,
                format!("expected file path after {}", directive),
            );
        }

        self.builder.finish_node();

        // A trailing comment is not part of the path.
        self.skip_ws();
        if self.current() == Some(COMMENT) {
            self.bump();
        }

        // Expect newline
        if self.current() == Some(NEWLINE) {
            self.bump();
        } else if !self.is_at_eof() {
            self.error(
                ParseErrorKind::ExtraneousText,
                format!("expected newline after {}", directive),
            );
            self.skip_logical_line();
        }
    }

    /// Parse a `vpath` directive in one of its three forms:
    ///
    /// - `vpath PATTERN DIRS` - add a search path for files matching PATTERN
    /// - `vpath PATTERN`      - clear the search path for PATTERN
    /// - `vpath`              - clear every `vpath` setting
    ///
    /// Produces a `VPATH` node containing the keyword token, the
    /// optional pattern's tokens and an optional EXPR holding the
    /// directory list. Variable references in either are nested EXPR
    /// nodes.
    pub(super) fn parse_vpath(&mut self) {
        self.in_rule = RuleContext::Outside;
        self.builder.start_node(VPATH.into());
        // Consume the `vpath` keyword.
        self.bump();
        self.skip_ws_and_continuations();

        // Optional pattern (rest of header until whitespace).
        if !matches!(self.current(), None | Some(NEWLINE | COMMENT)) {
            // The pattern token sequence (until whitespace or newline).
            while let Some(kind) = self.current() {
                match kind {
                    WHITESPACE | NEWLINE | COMMENT => break,
                    BACKSLASH if self.is_line_continuation() => break,
                    DOLLAR => self.parse_variable_reference(),
                    _ => self.bump(),
                }
            }
            self.skip_ws_and_continuations();

            // Optional directory list (everything else on the line, up
            // to any trailing comment).
            if !matches!(self.current(), None | Some(NEWLINE | COMMENT)) {
                self.builder.start_node(EXPR.into());
                loop {
                    match self.current() {
                        None | Some(NEWLINE | COMMENT) => break,
                        Some(WHITESPACE)
                            if matches!(self.peek_past_ws(), None | Some(NEWLINE | COMMENT)) =>
                        {
                            break
                        }
                        Some(DOLLAR) => self.parse_variable_reference(),
                        _ => {
                            if !self.consume_line_continuation() {
                                self.bump();
                            }
                        }
                    }
                }
                self.builder.finish_node();
            }
        }

        self.skip_ws();
        if self.current() == Some(COMMENT) {
            self.bump();
        }

        // Consume the trailing newline.
        if self.current() == Some(NEWLINE) {
            self.bump();
        }
        self.builder.finish_node();
    }

    /// Whether the BSD directive `name`, or the BSD name of an nmake
    /// directive, can be part of a rule's body. Conditionals and loops
    /// may wrap recipe lines. BSD make also
    /// doesn't end a rule's commands at its other directives, only at
    /// dependency lines and variable assignments.
    pub(super) fn bsd_directive_in_rule(&self, name: &str) -> bool {
        is_bsd_if(name)
            || name == "for"
            || (self.is_bsd_make()
                && !is_bsd_elif(name)
                && !matches!(name, "else" | "endif" | "endfor"))
    }

    /// If the current line starts with a BSD make directive, return its
    /// name without the leading dot (e.g. `if`, `-include`) and the
    /// number of tokens making up the keyword: `.if` is a single token,
    /// while `.  if` (whitespace after the dot, used for indenting
    /// nested directives) is three. Line continuations may also appear
    /// between the dot and the name.
    ///
    /// For nmake, this finds its `!` preprocessing directives instead,
    /// returning the name of the equivalent BSD make directive; see
    /// [`Parser::nmake_directive`].
    pub(super) fn directive(&self) -> Option<(&'static str, usize)> {
        if self.variant == Some(MakefileVariant::NMake) {
            return self.nmake_directive();
        }
        self.bsd_directive_at(self.tokens.len())
    }

    /// Like `directive`, for BSD make directives only and the line
    /// starting at the token at `n - 1` in the token stack.
    pub(super) fn bsd_directive_at(&self, n: usize) -> Option<(&'static str, usize)> {
        if !self.bsd_directives_enabled() {
            return None;
        }
        let tokens = &self.tokens[..n];
        let (kind, text) = tokens.last()?;
        if *kind != IDENTIFIER {
            return None;
        }
        let (name, count) = if text == "." {
            // Skip whitespace and line continuations between the dot
            // and the name.
            let mut i = n - 1;
            loop {
                i = i.checked_sub(1)?;
                match tokens[i].0 {
                    WHITESPACE | INDENT => {}
                    BACKSLASH if i > 0 && tokens[i - 1].0 == NEWLINE => i -= 1,
                    _ => break,
                }
            }
            if i == n - 2 || tokens[i].0 != IDENTIFIER {
                return None;
            }
            (tokens[i].1.as_str(), n - i)
        } else {
            (text.strip_prefix('.')?, 1)
        };
        let name = match BSD_DIRECTIVES.iter().find(|d| **d == name) {
            Some(name) => *name,
            // BSD make only compares the start of the word for includes,
            // so `.includes: foo` is an include with a bad path.
            None if self.is_bsd_make() => ["include", "-include", "sinclude", "dinclude"]
                .into_iter()
                .find(|d| name.starts_with(d))?,
            None => return None,
        };
        // Like BSD make, require whitespace or the end of the line after
        // the name, so that `.info: foo` is a dependency line. The
        // conditional and loop directives are more lenient, as in `.if!0`.
        // `.include` doesn't need whitespace either, as in
        // `.include<bsd.prog.mk>`.
        let lenient = is_bsd_if(name)
            || is_bsd_elif(name)
            || matches!(
                name,
                "else"
                    | "endif"
                    | "for"
                    | "endfor"
                    | "include"
                    | "-include"
                    | "sinclude"
                    | "dinclude"
            );
        let next = tokens[..n - count].last();
        if !lenient && !matches!(next, None | Some((WHITESPACE | NEWLINE | COMMENT, _))) {
            return None;
        }
        Some((name, count))
    }

    /// If the current line starts with an nmake preprocessing directive
    /// such as `!IF` or `!  else ifdef`, return the name of the
    /// equivalent BSD make directive (`if`, `elifdef`) and the number of
    /// tokens making up the keyword. Like nmake, this only recognizes a
    /// `!` in the first column, and ignores the case of the keyword.
    fn nmake_directive(&self) -> Option<(&'static str, usize)> {
        if !matches!(self.tokens.last(), Some((OPERATOR, op)) if op == "!") {
            return None;
        }
        let start = usize::from(self.current_range().start());
        if start > 0 && !self.original_text[..start].ends_with('\n') {
            return None;
        }
        // The index in `self.tokens` of the word after the one at `i`,
        // skipping whitespace.
        let next_word = |i: usize| {
            let i = (0..i).rev().find(|&j| self.tokens[j].0 != WHITESPACE)?;
            (self.tokens[i].0 == IDENTIFIER).then_some(i)
        };
        let n = self.tokens.len();
        let first = next_word(n - 1)?;
        let second = next_word(first);
        let (name, uses_second) = nmake_directive_name(
            &self.tokens[first].1,
            second.map(|i| self.tokens[i].1.as_str()),
        )?;
        let last = if uses_second { second? } else { first };
        let count = n - last;
        // As for BSD make, require whitespace or the end of the line
        // after the name of directives other than conditionals and
        // includes.
        let lenient =
            is_bsd_if(name) || is_bsd_elif(name) || matches!(name, "else" | "endif" | "include");
        let next = self.tokens[..last].last();
        if !lenient && !matches!(next, None | Some((WHITESPACE | NEWLINE | COMMENT, _))) {
            return None;
        }
        Some((name, count))
    }

    /// How a directive found by [`Parser::directive`] is written in
    /// messages, such as `.elif` for BSD make or `!ELSEIF` for nmake.
    pub(super) fn directive_display(&self, name: &str) -> String {
        if self.variant != Some(MakefileVariant::NMake) {
            return format!(".{}", name);
        }
        let name = match name.strip_prefix("elif") {
            Some(rest) => format!("elseif{}", rest),
            None => name.to_string(),
        };
        format!("!{}", name.to_ascii_uppercase())
    }

    /// Dispatch a BSD make or nmake directive found by `directive`.
    pub(super) fn parse_directive(&mut self, name: &str, count: usize) {
        match name {
            _ if is_bsd_if(name) => self.parse_block_conditional(name, count),
            "for" => self.parse_bsd_for(count),
            "include" | "-include" | "sinclude" | "dinclude"
                if self.is_bsd_make()
                    && self.tokens[self.tokens.len() - count]
                        .1
                        .trim_start_matches('.')
                        != name =>
            {
                self.record_error(
                    ParseErrorKind::UndelimitedIncludePath,
                    ".include filename must be delimited by \"\" or <>".to_string(),
                );
                self.builder.start_node(ERROR.into());
                self.skip_logical_line();
                self.builder.finish_node();
            }
            "include" | "-include" | "sinclude" | "dinclude" => self.parse_include(),
            _ if is_bsd_elif(name) || matches!(name, "else" | "endif" | "endfor") => {
                let (kind, opener) = match name {
                    "endfor" => (ParseErrorKind::ExtraneousEndfor, "for"),
                    "endif" => (ParseErrorKind::ExtraneousEndif, "if"),
                    _ => (ParseErrorKind::ElseWithoutIf, "if"),
                };
                let message = format!(
                    "{} without matching {}",
                    self.directive_display(name),
                    self.directive_display(opener)
                );
                self.record_error(kind, message);
                self.builder.start_node(ERROR.into());
                self.skip_logical_line();
                self.builder.finish_node();
            }
            _ => {
                self.builder.start_node(DIRECTIVE.into());
                self.bump_n(count);
                let found = self.parse_directive_expr();
                let error = match (name, found) {
                    // TODO: Check nmake's handling of `!UNDEF` without a
                    // name.
                    _ if self.variant == Some(MakefileVariant::NMake) => None,
                    ("break", true) => Some((
                        ParseErrorKind::ExtraneousText,
                        "The .break directive does not take arguments",
                    )),
                    ("unexport-env", true) => Some((
                        ParseErrorKind::ExtraneousText,
                        "The directive .unexport-env does not take arguments",
                    )),
                    ("undef", false) => Some((
                        ParseErrorKind::ExpectedVariableName,
                        "The .undef directive requires an argument",
                    )),
                    _ => None,
                };
                if let Some((kind, message)) = error {
                    self.record_error(kind, message.to_string());
                }
                self.finish_directive_line();
                self.builder.finish_node();
            }
        }
    }

    /// Parse the rest of a directive line into an EXPR node, followed by
    /// an optional comment and the newline. If `required` names the
    /// directive, an empty argument is reported as an error.
    pub(super) fn parse_directive_argument(&mut self, required: Option<&str>) {
        self.skip_ws_and_continuations();
        let condition = (required.is_some() && self.variant != Some(MakefileVariant::NMake))
            .then(|| self.bsd_logical_line());
        let found = self.parse_directive_expr();
        if let (Some(name), false) = (required, found) {
            self.record_error(
                ParseErrorKind::InvalidConditional,
                format!("expected condition after {}", self.directive_display(name)),
            );
        }
        if let Some(condition) = condition {
            self.check_bsd_condition(&condition);
        }
        self.finish_directive_line();
    }

    /// Parse the rest of a directive line up to any comment into an EXPR
    /// node, returning whether it is non-empty.
    fn parse_directive_expr(&mut self) -> bool {
        self.skip_ws_and_continuations();
        self.builder.start_node(EXPR.into());
        let mut found = false;
        while let Some(kind) = self.current() {
            match kind {
                NEWLINE | COMMENT => break,
                BACKSLASH if self.is_line_continuation() => {
                    self.consume_line_continuation();
                }
                DOLLAR => {
                    found = true;
                    self.parse_variable_reference();
                }
                _ => {
                    found = true;
                    self.bump();
                }
            }
        }
        self.builder.finish_node();
        found
    }

    /// Consume the optional comment and the newline ending a directive.
    fn finish_directive_line(&mut self) {
        if self.current() == Some(COMMENT) {
            self.bump();
        }
        if self.current() == Some(NEWLINE) {
            self.bump();
        }
    }

    /// Consume the remainder of a directive that takes no arguments, such
    /// as `.else` or `.endif`, allowing a trailing comment. BSD make
    /// ignores anything after `.endfor`.
    pub(super) fn parse_bare_directive_end(&mut self, name: &str) {
        self.skip_ws_and_continuations();
        if self.current() == Some(COMMENT) {
            self.bump();
        }
        match self.current() {
            None => {}
            Some(NEWLINE) => self.bump(),
            Some(_) if name == "endfor" => self.skip_logical_line(),
            Some(_) => {
                self.record_error(
                    ParseErrorKind::ExtraneousText,
                    format!(
                        "The {} directive does not take arguments",
                        self.directive_display(name)
                    ),
                );
                self.skip_logical_line();
            }
        }
    }

    /// Parse a BSD `.for VAR... in LIST` ... `.endfor` loop.
    fn parse_bsd_for(&mut self, count: usize) {
        if self.nesting_depth >= crate::reference::MAX_DEPTH {
            self.parse_too_deeply_nested_block();
            return;
        }
        self.builder.start_node(FOR_LOOP.into());
        self.builder.start_node(FOR_HEADER.into());
        self.bump_n(count);
        self.skip_ws_and_continuations();
        // Like BSD make, take each word up to `in` as a variable,
        // whatever characters it consists of, as in `.for , in 1`.
        let mut found_variable = false;
        let mut valid = true;
        loop {
            // A line continuation also ends the word.
            let mut word_len = 0;
            for i in (0..self.tokens.len()).rev() {
                let kind = self.tokens[i].0;
                let continuation = kind == BACKSLASH && i > 0 && self.tokens[i - 1].0 == NEWLINE;
                if matches!(kind, WHITESPACE | INDENT | NEWLINE | COMMENT) || continuation {
                    break;
                }
                word_len += 1;
            }
            let word: String = self.tokens[self.tokens.len() - word_len..]
                .iter()
                .rev()
                .map(|(_, text)| text.as_str())
                .collect();
            if word.is_empty() || word == "in" {
                break;
            }
            if let Some(c) = word.chars().find(|c| "$:\\(){}".contains(*c)) {
                self.record_error(
                    ParseErrorKind::InvalidForLoop,
                    format!("Invalid character \"{c}\" in .for loop variable name"),
                );
                valid = false;
                break;
            }
            found_variable = true;
            self.tokens.truncate(self.tokens.len() - word_len);
            self.token_positions.truncate(self.tokens.len());
            self.pending_backslash_escape = false;
            self.builder.token(IDENTIFIER.into(), &word);
            self.skip_ws_and_continuations();
        }
        if valid && !found_variable {
            self.record_error(
                ParseErrorKind::InvalidForLoop,
                "expected variable name after .for".to_string(),
            );
        }
        if self.current() == Some(IDENTIFIER) && self.tokens.last().unwrap().1 == "in" {
            self.bump();
        } else if valid {
            self.record_error(
                ParseErrorKind::InvalidForLoop,
                "expected 'in' in .for".to_string(),
            );
        }
        self.parse_directive_argument(None);
        self.builder.finish_node();

        // As in BSD make, the rule context after the loop is the one at
        // the end of its body, which is right unless the loop runs zero
        // times.
        self.for_depth += 1;
        self.nesting_depth += 1;
        loop {
            if self.is_at_eof() {
                self.record_unterminated_error(
                    ParseErrorKind::MissingEndfor,
                    "unterminated .for (missing .endfor)".to_string(),
                );
                break;
            }
            match self.directive() {
                Some((name, count)) if name == "endfor" => {
                    self.builder.start_node(FOR_END.into());
                    self.bump_n(count);
                    self.parse_bare_directive_end(name);
                    self.builder.finish_node();
                    break;
                }
                _ => self.parse_block_item(),
            }
        }
        self.for_depth -= 1;
        self.nesting_depth -= 1;

        self.builder.finish_node();
    }

    /// Consume the rest of a `define` header after the operator, or of an
    /// `endef` or `endif` line, which may only contain a comment. Other
    /// text is reported as extraneous; it is wrapped in an ERROR node
    /// unless it is part of the value of an enclosing define.
    pub(super) fn parse_directive_line_end(&mut self, directive: &str, in_value: bool) {
        self.parse_extraneous_text(directive, in_value);
        if self.current() == Some(COMMENT) {
            self.bump();
        }
        if self.current() == Some(NEWLINE) {
            self.bump();
        }
    }

    /// Report any text before the end of the line or a comment as
    /// extraneous to `directive`, wrapping it in an ERROR node unless
    /// `in_value`.
    fn parse_extraneous_text(&mut self, directive: &str, in_value: bool) {
        self.skip_ws_and_continuations();
        if !matches!(self.current(), None | Some(NEWLINE | COMMENT)) {
            if !in_value {
                self.builder.start_node(ERROR.into());
            }
            self.record_error(
                ParseErrorKind::ExtraneousText,
                format!("extraneous text after `{directive}` directive"),
            );
            while !matches!(self.current(), None | Some(NEWLINE | COMMENT)) {
                if !self.consume_line_continuation() {
                    self.bump();
                }
            }
            if !in_value {
                self.builder.finish_node();
            }
        }
    }
}
