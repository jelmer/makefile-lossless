use super::tokens::token_stack;
use super::*;

/// Whether a token is only whitespace. The text after a recipe line's
/// indent may be lexed as TEXT, even if it is only whitespace.
fn is_blank_token((kind, text): (SyntaxKind, &str)) -> bool {
    kind == WHITESPACE || (kind == TEXT && text.trim().is_empty())
}

impl<'a> Parser<'a> {
    fn parse_recipe_line(&mut self) {
        self.with_references(
            RECIPE,
            TextContext::Recipe,
            Self::parse_recipe_line_contents,
        );
    }

    fn parse_recipe_line_contents(&mut self) {
        // Check for and consume the indent
        if self.current() != Some(INDENT) {
            self.error(
                ParseErrorKind::Other,
                "recipe line must start with a tab".to_string(),
            );
            return;
        }
        self.bump();

        // Parse the recipe content, handling line continuations (backslash at end of line)
        let mut inline_files = 0;
        // GNU and BSD make continue a line starting with `#` too, and the
        // continuation lines are part of the comment. nmake ends the
        // comment at the end of the line.
        let comment =
            self.current() == Some(COMMENT) && self.variant != Some(MakefileVariant::NMake);
        loop {
            // Like the lexer, only an odd number of backslashes continues
            // the line; `\\\\` is an escaped backslash.
            let mut is_continuation = false;

            // Consume all tokens until newline, noting whether the last
            // TEXT token ends in a continuation backslash
            while self.current().is_some() && self.current() != Some(NEWLINE) {
                if self.current() == Some(TEXT) || (comment && self.current() == Some(COMMENT)) {
                    if let Some(text) = self.current_text() {
                        if self.variant == Some(MakefileVariant::NMake) {
                            inline_files += text.matches("<<").count();
                        }
                        is_continuation = ends_with_unescaped_backslash(text);
                    }
                }
                if comment && self.current() == Some(TEXT) {
                    self.bump_as(COMMENT);
                } else {
                    self.bump();
                }
            }

            if self.current() == Some(NEWLINE) {
                if is_continuation {
                    self.bump_continued_newline();
                } else {
                    self.bump();
                }
            }

            if is_continuation {
                // This is a continuation line - consume the indent of the next line, if
                // any, and continue
                match self.current() {
                    Some(INDENT) => {
                        self.bump();
                        continue;
                    }
                    Some(TEXT) => continue,
                    _ => break,
                }
            } else {
                // No continuation - we're done
                break;
            }
        }

        // Each `<<` in an nmake command starts an inline file, whose
        // lines run up to a line starting with `<<`.
        while inline_files > 0 {
            match self.current() {
                Some(TEXT) => {
                    if self
                        .current_text()
                        .is_some_and(|text| text.starts_with("<<"))
                    {
                        inline_files -= 1;
                    }
                    self.bump();
                    if self.current() == Some(NEWLINE) {
                        self.bump();
                    }
                }
                Some(NEWLINE) => self.bump(),
                None => {
                    self.record_error(
                        ParseErrorKind::Other,
                        "unterminated inline file (missing <<)".to_string(),
                    );
                    break;
                }
                _ => break,
            }
        }
    }

    /// Parse a recipe given on the rule line after a `;`, up to the end
    /// of the line. Like make, take everything after the `;` and any
    /// whitespace following it as the recipe text, including `#`.
    pub(super) fn parse_inline_recipe(&mut self) {
        self.with_references(RECIPE, TextContext::Recipe, |p| {
            p.bump_as(OPERATOR);
            p.skip_ws();
            p.parse_text_to_eol(true);
        });
    }

    /// Consume the rest of the logical line, including any `#` and
    /// continuation lines, as TEXT tokens. If `leading_comment` is set,
    /// text starting with `#` becomes a COMMENT token instead.
    pub(super) fn parse_text_to_eol(&mut self, leading_comment: bool) {
        let mut first = true;
        let mut comment = false;
        loop {
            let mut text = String::new();
            while self.current().is_some_and(|kind| kind != NEWLINE) {
                if !self.split_continued_comment() {
                    text.push_str(self.pop_token().unwrap().text);
                }
            }
            self.pending_backslash_escape = false;
            // An odd number of trailing backslashes continues the line,
            // even after a `#`.
            let continued = self.current() == Some(NEWLINE) && ends_with_unescaped_backslash(&text);
            if !text.is_empty() {
                // Mirror how a tab-indented `# ...` line is tokenized,
                // with any continuation lines in the comment except
                // for nmake.
                let starts_comment = leading_comment && first && text.starts_with('#');
                comment |= starts_comment && self.variant != Some(MakefileVariant::NMake);
                let kind = if starts_comment || comment {
                    COMMENT
                } else {
                    TEXT
                };
                self.builder.token(kind.into(), &text);
            }
            if self.current() == Some(NEWLINE) {
                if continued {
                    self.bump_continued_newline();
                } else {
                    self.bump();
                }
            }
            if !continued {
                break;
            }
            first = false;
            if self.current() == Some(INDENT) {
                self.bump();
            }
        }
    }

    /// If the current token is a comment that the lexer continued onto
    /// the next line because it ends in a backslash, split it into its
    /// first line, the line ending, the next line's indentation and the
    /// rest. This is for places where `#` does not start a comment, such
    /// as a recipe on the rule line.
    fn split_continued_comment(&mut self) -> bool {
        let Some((COMMENT, text)) = self.current_token() else {
            return false;
        };
        let Some(lf) = text.find('\n') else {
            return false;
        };
        let eol = text[..lf].strip_suffix('\r').unwrap_or(&text[..lf]).len();
        let eol_end = lf + 1;
        let rest = &text[eol_end..];
        let indent_end = eol_end + rest.len() - rest.trim_start_matches([' ', '\t']).len();
        let pieces = [
            (COMMENT, &text[..eol]),
            (NEWLINE, &text[eol..eol_end]),
            (INDENT, &text[eol_end..indent_end]),
            (COMMENT, &text[indent_end..]),
        ]
        .into_iter()
        .filter(|(_, piece)| !piece.is_empty())
        .collect();
        self.replace_current_token(pieces);
        self.token_edits += 1;
        true
    }

    pub(super) fn parse_rule_recipes(&mut self) {
        // Track consecutive newlines to detect blank lines
        let mut newline_count = 0;

        loop {
            if let Some((name, count)) = self.directive() {
                // Blank lines don't end a rule's recipe, so this
                // belongs to the rule if it has recipe lines.
                if !self.bsd_directive_in_rule(name) || !self.recipe_continues() {
                    break;
                }
                newline_count = 0;
                self.parse_directive(name, count);
                continue;
            }
            match self.current() {
                Some(INDENT) if self.in_rule == RuleContext::Inside => {
                    newline_count = 0;
                    self.parse_recipe_line();
                }
                Some(WHITESPACE) => {
                    // A space-indented comment or blank line doesn't end the rule
                    let next = self.upcoming().nth(1).map(|(kind, _)| kind);
                    match next {
                        Some(COMMENT) if newline_count == 0 || self.recipe_continues() => {
                            self.bump();
                        }
                        // After a blank line, it ends the rule like an
                        // unindented comment.
                        Some(COMMENT) => break,
                        Some(NEWLINE) | None => self.bump(),
                        _ if self.at_space_indented_recipe() => {
                            newline_count = 0;
                            self.parse_space_indented_recipe();
                        }
                        _ => break,
                    }
                }
                Some(NEWLINE) => {
                    newline_count += 1;
                    self.bump();
                }
                Some(COMMENT) => {
                    // Comments after blank lines should not be part of the
                    // rule, unless the recipe continues after them
                    if newline_count >= 1 && !self.recipe_continues() {
                        break;
                    }
                    newline_count = 0;
                    self.parse_comment();
                }
                Some(IDENTIFIER) => {
                    // Check if this is a starting conditional directive
                    if self.current_text().is_some_and(is_gnu_conditional_start)
                        && self.at_conditional_keyword()
                    {
                        // Unless it continues the recipe, this is a top-level
                        // conditional, not part of the rule. Blank lines
                        // don't end a rule's recipe.
                        if !self.recipe_continues() {
                            break;
                        }
                        newline_count = 0;
                        self.parse_conditional();
                    } else if self.at_include_keyword() {
                        // Only BSD make keeps rule context across an
                        // include line; GNU make ends the rule there.
                        if !self.is_bsd_make() || (newline_count >= 1 && !self.recipe_continues()) {
                            break;
                        }
                        newline_count = 0;
                        self.parse_include();
                    } else {
                        // Any other identifier, including a stray `else` or
                        // `endif`, ends the rule.
                        break;
                    }
                }
                _ => break,
            }
        }
    }

    /// Whether the current WHITESPACE token starts a line in a rule that
    /// can only be a recipe indented with spaces rather than a tab: it is
    /// not a rule, assignment or directive. GNU make rejects such a line
    /// with "missing separator".
    fn at_space_indented_recipe(&mut self) -> bool {
        if self.in_rule != RuleContext::Inside
            || !matches!(self.current_token(), Some((WHITESPACE, ws)) if !ws.contains('\t'))
        {
            return false;
        }
        let ws = self.pop_token().unwrap();
        let is_recipe = self.directive().is_none()
            && !self.line_has_dependency_operator()
            && !self.has_assignment_operator_on_line()
            && !self.is_variable_assignment_line()
            && !self.at_include_keyword()
            && !matches!(
                self.current_token(),
                Some((IDENTIFIER, word)) if is_gnu_conditional_start(word)
                    || matches!(word, "else" | "endif" | "define" | "endef")
            );
        self.tokens.push(ws);
        is_recipe
    }

    /// Parse a recipe line indented with spaces as a recipe of the
    /// current rule, recording a missing separator error.
    fn parse_space_indented_recipe(&mut self) {
        self.with_references(
            RECIPE,
            TextContext::Recipe,
            Self::parse_space_indented_recipe_contents,
        );
    }

    fn parse_space_indented_recipe_contents(&mut self) {
        self.record_error(
            ParseErrorKind::MissingSeparator,
            "missing separator (recipe lines must start with a tab)".to_string(),
        );
        self.bump_as(INDENT);
        // Continuation lines belong to the recipe, as they would if it
        // were indented with a tab.
        loop {
            let mut text = String::new();
            while self.current().is_some_and(|kind| kind != NEWLINE) {
                text.push_str(self.pop_token().unwrap().text);
            }
            let continued = ends_with_unescaped_backslash(&text);
            if !text.is_empty() {
                self.builder.token(TEXT.into(), &text);
            }
            self.pending_backslash_escape = false;
            if self.current() != Some(NEWLINE) {
                break;
            }
            if !continued {
                self.bump();
                break;
            }
            self.bump_continued_newline();
        }
    }

    /// Parse an indented command line outside of rule context. GNU make
    /// parses it like any other line if it is a statement, while BSD
    /// make, POSIX and nmake read it as a command line. Either way, a
    /// command line is an error without a target. For BSD make, inside
    /// a conditional it is only an error if make takes that branch, as
    /// lines in other branches are skipped unread.
    fn parse_indented_line_outside_rule(&mut self) {
        if self.indented_lines_are_commands() {
            if self.at_bsd_comment_line() {
                self.parse_bsd_comment_line();
                return;
            }
            if self.block_conditional_depth == 0 {
                self.record_error(
                    ParseErrorKind::RecipeBeforeFirstTarget,
                    "indented line not part of a rule".to_string(),
                );
            }
            self.parse_recipe_line();
        } else if let Some(line) = self.lex_indented_statement() {
            self.replace_line(line);
        } else {
            self.record_error(
                ParseErrorKind::RecipeBeforeFirstTarget,
                "indented line not part of a rule".to_string(),
            );
            self.parse_recipe_line();
        }
    }

    /// Parse a tab-indented line, which is a recipe line in rule context.
    pub(super) fn parse_indented_line(&mut self) {
        let in_rule = self.in_rule;
        match in_rule {
            RuleContext::Inside => self.parse_recipe_line(),
            RuleContext::Outside => self.parse_indented_line_outside_rule(),
            // Whether the line belongs to a rule depends on the branches
            // make takes. BSD make, POSIX and nmake read it as a command
            // either way, while GNU make reads it as an ordinary line
            // outside of rule context, so it has to be a recipe line if
            // it isn't valid as one.
            RuleContext::Varies if self.indented_lines_are_commands() => {
                if self.at_bsd_comment_line() {
                    self.parse_bsd_comment_line()
                } else {
                    self.parse_recipe_line()
                }
            }
            RuleContext::Varies => match self.lex_indented_statement() {
                Some(line) => self.replace_line(line),
                None => self.parse_recipe_line(),
            },
        }
    }

    /// Whether an indented line is always a command line, as in BSD make,
    /// POSIX and nmake, rather than an ordinary line outside of rule
    /// context as in GNU make.
    fn indented_lines_are_commands(&self) -> bool {
        matches!(
            self.variant,
            Some(MakefileVariant::BSDMake | MakefileVariant::POSIXMake | MakefileVariant::NMake)
        )
    }

    /// Whether the tab-indented line at the current position has only a
    /// comment, or nothing at all, which BSD make skips.
    fn at_bsd_comment_line(&self) -> bool {
        self.upcoming()
            .skip(1)
            .find(|&token| !is_blank_token(token))
            .is_none_or(|(kind, text)| match kind {
                COMMENT | NEWLINE => true,
                TEXT => text.trim_start().starts_with('#'),
                _ => false,
            })
    }

    /// The tab-indented line at the current position lexed as an ordinary
    /// line, if it is valid as such outside of rule context in GNU make: a
    /// comment, blank line, directive or assignment. Expressions and rules
    /// are not.
    fn lex_indented_statement(&mut self) -> Option<RelexedLine<'a>> {
        let mut line = self.lex_as_non_recipe_line();
        let tokens = std::mem::replace(&mut self.tokens, line.tokens);
        let mut indent = vec![];
        while let Some(token) = self
            .tokens
            .pop_if(|token| matches!(token.kind, WHITESPACE | INDENT))
        {
            indent.push(token);
        }
        let is_statement = match self.current_token() {
            None | Some((NEWLINE | COMMENT, _)) => true,
            _ => {
                self.at_vpath_keyword()
                    || self.at_conditional_keyword()
                    || self.directive().is_some()
                    || self.is_define_line()
                    || self.is_assignment_line()
                    || (self.bsd_directives_enabled() && self.is_bsd_assignment_line())
                    || self.at_include_keyword()
                    || self.at_load_keyword()
            }
        };
        self.tokens.extend(indent.into_iter().rev());
        line.tokens = std::mem::replace(&mut self.tokens, tokens);
        is_statement.then_some(line)
    }

    /// Parse a tab-indented line with only a comment, or nothing at all,
    /// which BSD make skips. The comment, including any continuation
    /// lines, becomes a single COMMENT token.
    fn parse_bsd_comment_line(&mut self) {
        self.bump_as(WHITESPACE);
        while self.current_token().is_some_and(is_blank_token) {
            self.bump_as(WHITESPACE);
        }
        let mut comment = String::new();
        while let Some((kind, text)) = self.current_token() {
            if kind == NEWLINE
                && (!ends_with_unescaped_backslash(&comment) || self.tokens.len() == 1)
            {
                break;
            }
            comment.push_str(text);
            self.pop_token();
        }
        if !comment.is_empty() {
            self.pending_backslash_escape = false;
            self.builder.token(COMMENT.into(), &comment);
        }
        if self.current() == Some(NEWLINE) {
            self.bump();
        }
    }

    /// Lex the rest of the current logical line as an ordinary makefile
    /// line.
    pub(super) fn lex_as_non_recipe_line(&self) -> RelexedLine<'a> {
        let start = self.current_range().start();
        let tokens =
            lex_first_non_recipe_line(&self.original_text[usize::from(start)..], self.variant);
        let len: usize = tokens.iter().map(|(_, text)| text.len()).sum();
        let mut replaced_len = 0;
        let mut replaces = 0;
        for (_, text) in self.upcoming() {
            if replaced_len >= len {
                break;
            }
            replaced_len += text.len();
            replaces += 1;
        }
        assert_eq!(replaced_len, len, "relexed line ends inside a token");
        RelexedLine {
            tokens: token_stack(start, tokens),
            replaces,
        }
    }

    /// Replace the tokens of the rest of the current logical line with
    /// `line`.
    fn replace_line(&mut self, line: RelexedLine<'a>) {
        self.tokens.truncate(self.tokens.len() - line.replaces);
        self.tokens.extend(line.tokens);
        self.token_edits += 1;
    }
}
