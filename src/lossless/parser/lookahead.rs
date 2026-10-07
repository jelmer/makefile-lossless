use super::assignment::{is_colons_before_subst, ASSIGNMENT_OPERATORS};
use super::conditional::ConditionalRuleContext;
use super::directive::{is_bsd_elif, is_bsd_if, nmake_directive_name};
use super::*;

impl Parser<'_> {
    /// Whether `op` can separate targets from prerequisites. `&:` and
    /// `&::` mark grouped targets; BSD make also has `!`, which always
    /// rebuilds the target.
    fn is_dependency_operator(&self, op: &str) -> bool {
        Self::is_colon_dependency_operator(op) || (op == "!" && self.bsd_directives_enabled())
    }

    fn is_colon_dependency_operator(op: &str) -> bool {
        matches!(op, ":" | "::" | "&:" | "&::")
    }

    pub(super) fn at_dependency_operator(&self) -> bool {
        match self.current_token() {
            Some((OPERATOR, op)) => {
                Self::is_colon_dependency_operator(op) || self.at_bang_dependency_operator()
            }
            _ => false,
        }
    }

    /// Whether the current token is a `!` dependency operator. Without
    /// a known variant, a `!` followed by a `:` on the same logical line is
    /// instead part of a target name, as in GNU make's `a!b:`.
    pub(super) fn at_bang_dependency_operator(&self) -> bool {
        if !self.at_bang() {
            return false;
        }
        match self.variant {
            Some(MakefileVariant::BSDMake) => true,
            None => !self.line_has_operator(Self::is_colon_dependency_operator),
            _ => false,
        }
    }

    pub(super) fn at_bang(&self) -> bool {
        self.at(OPERATOR, "!")
    }

    /// Whether the current token is a `!` that is part of a name.
    pub(super) fn at_literal_bang(&self) -> bool {
        self.at_bang() && !self.at_bang_dependency_operator()
    }

    /// Look ahead (without consuming) from the current token, which
    /// starts a comment or directive, and check whether a recipe line
    /// of the current rule is reached before rule context ends,
    /// following rule context the same way the parser does. GNU make
    /// ends a rule's recipe at the first line that is not a recipe line,
    /// comment, blank line or conditional directive, so if no recipe
    /// line follows, the comment or conditional doesn't belong to the
    /// preceding rule.
    pub(super) fn recipe_continues(&self) -> bool {
        let len = self.tokens.len();
        if let Some(cached) = self.recipe_continues.get() {
            if cached.in_rule == self.in_rule
                && cached.token_edits == self.token_edits
                && cached.end < len
                && len <= cached.start
            {
                return cached.result;
            }
        }
        let mut end = None;
        let result = self.scan_recipe_continues(&mut end);
        if let Some(end) = end {
            self.recipe_continues.set(Some(RecipeContinues {
                start: len,
                end,
                in_rule: self.in_rule,
                token_edits: self.token_edits,
                result,
            }));
        }
        result
    }

    /// Do the work of [`Self::recipe_continues`]. Sets `comments_end` to
    /// the number of tokens left at the first line that is not a comment
    /// or blank line, or to 0 if there is none, unless the result is
    /// known before reaching it.
    fn scan_recipe_continues(&self, comments_end: &mut Option<usize>) -> bool {
        let bsd = self.bsd_directives_enabled();
        let nmake = self.variant == Some(MakefileVariant::NMake);
        let mut stack: Vec<ConditionalRuleContext> = Vec::new();
        let mut in_rule = self.in_rule;
        // Pair each token with whether it starts a line, which the
        // current token always does, and its end in the token stack.
        let n = self.tokens.len();
        let mut tokens = self
            .tokens
            .iter()
            .rev()
            .enumerate()
            .map(|(i, token)| (token, i == 0 || self.tokens[n - i].0 == NEWLINE, n - i))
            .filter(|((kind, _), _, _)| *kind != WHITESPACE)
            .peekable();
        while let Some(&((kind, text), at_start, end)) = tokens.peek() {
            let word = |n: usize| {
                tokens
                    .clone()
                    .nth(n)
                    .filter(|((kind, _), _, _)| *kind == IDENTIFIER)
                    .map(|((_, name), _, _)| name.as_str())
            };
            // The name of a BSD directive such as `.if` or `.  if`, or the
            // equivalent BSD name of an nmake directive such as `!IF`
            let bsd_name = match (*kind, text.as_str()) {
                (IDENTIFIER, ".") if bsd => word(1),
                (IDENTIFIER, t) if bsd => t.strip_prefix('.'),
                (OPERATOR, "!") if nmake && at_start => {
                    word(1).and_then(|first| Some(nmake_directive_name(first, word(2))?.0))
                }
                _ => None,
            };
            if comments_end.is_none() && !matches!(kind, NEWLINE | COMMENT) {
                *comments_end = Some(end);
            }
            match (*kind, text.as_str()) {
                (NEWLINE | COMMENT, _) => {}
                (INDENT, _) if in_rule == RuleContext::Inside => return true,
                _ if bsd_name.is_some_and(is_bsd_if) => {
                    stack.push(ConditionalRuleContext::new(in_rule))
                }
                // As in the parser, the rule context after a `.for` loop
                // is the one at the end of its body, so a `.for` only
                // needs to be balanced with its `.endfor`.
                _ if bsd_name == Some("for") => stack.push(ConditionalRuleContext::for_loop()),
                _ if bsd_name.is_some_and(|n| is_bsd_elif(n) || n == "else") => {
                    match stack.last_mut() {
                        Some(context) => {
                            in_rule = context.next_branch(in_rule, bsd_name == Some("else"))
                        }
                        None => return false,
                    }
                }
                _ if bsd_name.is_some_and(|n| n == "endif" || n == "endfor") => match stack.pop() {
                    Some(context) => in_rule = context.end(in_rule),
                    None => return false,
                },
                (IDENTIFIER, t)
                    if Self::is_conditional_start(t) && self.conditional_line_at(end) =>
                {
                    stack.push(ConditionalRuleContext::new(in_rule))
                }
                (IDENTIFIER, "else") if self.conditional_line_at(end) => match stack.last_mut() {
                    Some(context) => {
                        let is_final = !self.is_else_if_at(end);
                        in_rule = context.next_branch(in_rule, is_final);
                    }
                    None => return false,
                },
                (IDENTIFIER, "endif") if self.conditional_line_at(end) => match stack.pop() {
                    Some(context) => in_rule = context.end(in_rule),
                    None => return false,
                },
                _ if self
                    .bsd_directive_at(end)
                    .is_some_and(|(name, _)| self.bsd_directive_in_rule(name))
                    || (self.is_bsd_make() && self.include_keyword_at(end)) => {}
                _ => in_rule = RuleContext::Outside,
            }
            if stack.is_empty() && in_rule != RuleContext::Inside {
                return false;
            }
            // Skip to the start of the next line, following continuations
            let mut prev = None;
            for ((kind, _), _, _) in tokens.by_ref() {
                if *kind == NEWLINE && prev != Some(BACKSLASH) {
                    break;
                }
                prev = Some(*kind);
            }
        }
        comments_end.get_or_insert(0);
        false
    }

    pub(super) fn at_assignment_operator(&self) -> bool {
        matches!(self.current_token(), Some((OPERATOR, op)) if ASSIGNMENT_OPERATORS.contains(&op))
    }

    /// Whether the current token is one of `keywords`, followed by
    /// whitespace, a line continuation, a comment or the end of the line,
    /// as make requires for its directives.
    pub(super) fn at_keyword(&self, keywords: &[&str]) -> bool {
        self.keyword_at(self.tokens.len(), keywords)
    }

    /// Like `at_keyword`, for the token at `end - 1` in the token stack.
    pub(super) fn keyword_at(&self, end: usize, keywords: &[&str]) -> bool {
        let mut tokens = self.tokens[..end].iter().rev();
        if !tokens
            .next()
            .is_some_and(|(kind, text)| *kind == IDENTIFIER && keywords.contains(&text.as_str()))
        {
            return false;
        }
        match tokens.next() {
            None | Some((WHITESPACE | NEWLINE | COMMENT, _)) => true,
            Some((BACKSLASH, _)) => matches!(tokens.next(), Some((NEWLINE, _))),
            _ => false,
        }
    }

    /// Whether the token at `end - 1` in the token stack is a GNU make
    /// conditional keyword such as `ifeq` or `endif`. As for other
    /// directives, `ifeq: a` is a rule. GNU make rejects `ifeq(a,b)`,
    /// but it is still read as a conditional for error recovery.
    fn conditional_keyword_at(&self, end: usize) -> bool {
        if !self.gnu_directives_enabled() {
            return false;
        }
        if self.keyword_at(end, &["ifdef", "ifndef", "ifeq", "ifneq", "else", "endif"]) {
            return true;
        }
        let mut tokens = self.tokens[..end].iter().rev();
        matches!(tokens.next(), Some((IDENTIFIER, t)) if t == "ifeq" || t == "ifneq")
            && matches!(tokens.next(), Some((LPAREN | QUOTE, _)))
    }

    /// Whether the current token is a GNU make conditional keyword that
    /// starts a conditional line.
    pub(super) fn at_conditional_keyword(&self) -> bool {
        self.conditional_line_at(self.tokens.len())
    }

    /// Whether the token at `end - 1` in the token stack starts a GNU
    /// make conditional line. Like make, this checks for an assignment
    /// first, so `ifdef = 1` defines a variable.
    pub(super) fn conditional_line_at(&self, end: usize) -> bool {
        self.conditional_keyword_at(end) && !self.assignment_at(end)
    }

    /// Whether the current token is a GNU make `vpath` directive.
    pub(super) fn at_vpath_keyword(&self) -> bool {
        self.gnu_directives_enabled() && self.at_keyword(&["vpath"])
    }

    /// Whether the current token is a GNU make `load` or `-load`
    /// directive, which only GNU make supports. As for `include`,
    /// `load: foo` is a rule.
    pub(super) fn at_load_keyword(&self) -> bool {
        self.gnu_directives_enabled() && self.at_keyword(&["load", "-load"])
    }

    /// Whether the current token is an `include`, `-include` or
    /// `sinclude` directive. Like make, this requires whitespace after
    /// the keyword, so `include: foo` is a rule. BSD make also treats a
    /// line with a dependency operator followed by whitespace, as in
    /// `include foo: bar`, as a rule. POSIX make has no `sinclude`, and
    /// nmake only has `!INCLUDE`.
    pub(super) fn at_include_keyword(&self) -> bool {
        self.include_keyword_at(self.tokens.len())
    }

    /// Like `at_include_keyword`, for the token at `end - 1` in the
    /// token stack.
    fn include_keyword_at(&self, end: usize) -> bool {
        let keywords: &[&str] = match self.variant {
            Some(MakefileVariant::NMake) => &[],
            Some(MakefileVariant::POSIXMake) => &["include", "-include"],
            _ => &["include", "-include", "sinclude"],
        };
        if !self.keyword_at(end, keywords) {
            return false;
        }
        let mut tokens = self.tokens[..end].iter().rev().skip(1).peekable();
        if self.variant != Some(MakefileVariant::BSDMake) {
            return true;
        }
        while let Some((kind, text)) = tokens.next() {
            match (*kind, text.as_str()) {
                (NEWLINE, _) => break,
                (OPERATOR, ":" | "::")
                    if matches!(tokens.peek(), None | Some((WHITESPACE | NEWLINE, _)))
                        || text == "::" =>
                {
                    return false
                }
                _ => {}
            }
        }
        true
    }

    /// Whether the rest of the logical line has a dependency operator.
    /// A backslash escapes the first character of an operator, so `\:`
    /// is not one.
    pub(super) fn line_has_dependency_operator(&self) -> bool {
        self.line_has_operator(|op| self.is_dependency_operator(op))
    }

    /// Whether the rest of the logical line has an operator matching
    /// `matches`, after removing any escaped first character.
    fn line_has_operator(&self, matches: impl Fn(&str) -> bool) -> bool {
        let mut escaped = self.pending_backslash_escape;
        for (kind, text) in self.tokens.iter().rev() {
            match kind {
                // An unescaped backslash before the newline continues the
                // line.
                NEWLINE if !escaped => break,
                OPERATOR => {
                    let op = if escaped { &text[1..] } else { text.as_str() };
                    if matches(op) {
                        return true;
                    }
                }
                _ => {}
            }
            escaped = *kind == BACKSLASH && !escaped;
        }
        false
    }

    /// Whether the current token is at the start of a line that begins
    /// with a tab, ignoring any whitespace already consumed.
    pub(super) fn at_tab_indented_line_start(&self) -> bool {
        let start = usize::from(self.current_range().start());
        let line_start = self.original_text[..start].rfind('\n').map_or(0, |i| i + 1);
        self.original_text[line_start..].starts_with('\t')
            && self.original_text[line_start..start]
                .chars()
                .all(|c| c == ' ' || c == '\t')
    }

    /// Advance `tokens` past whitespace and line continuations. Returns
    /// whether anything was skipped.
    pub(super) fn skip_ws_and_continuation_tokens<'a, I>(
        tokens: &mut std::iter::Peekable<I>,
    ) -> bool
    where
        I: Iterator<Item = &'a (SyntaxKind, String)> + Clone,
    {
        let mut skipped = false;
        loop {
            let at_continuation = matches!(tokens.peek(), Some((BACKSLASH, _)))
                && matches!(tokens.clone().nth(1), Some((NEWLINE, _)));
            if at_continuation {
                tokens.nth(1);
                tokens.next_if(|(kind, _)| *kind == INDENT);
            } else if tokens.next_if(|(kind, _)| *kind == WHITESPACE).is_none() {
                return skipped;
            }
            skipped = true;
        }
    }

    /// Returns true if the rest of the line consists only of `$(...)`,
    /// `${...}` and `$X` references, such as `$(eval ...)` or
    /// `$(info ...)`, optionally followed (for GNU make) by a `;` and
    /// arbitrary text.
    /// Make expands such lines for their side effects; anything else on
    /// the line (e.g. a colon) makes it a rule or assignment instead.
    pub(super) fn is_expression_statement_line(&self) -> bool {
        let mut tokens = self.tokens.iter().rev().peekable();
        let mut seen_reference = false;
        loop {
            match tokens.next().map(|(kind, text)| (*kind, text.as_str())) {
                None | Some((NEWLINE | COMMENT, _)) => return seen_reference,
                // Only GNU make ignores the rest of such a line after a
                // `;`; bmake rejects it.
                Some((TEXT, ";"))
                    if matches!(self.variant, None | Some(MakefileVariant::GNUMake)) =>
                {
                    return seen_reference
                }
                Some((WHITESPACE | INDENT, _)) => {}
                Some((BACKSLASH, _)) if tokens.peek().is_some_and(|(k, _)| *k == NEWLINE) => {
                    tokens.next();
                }
                Some((DOLLAR, _)) => {
                    // Like make, only count the delimiter that opened the
                    // reference.
                    let (open, close) = match tokens.next() {
                        Some((LPAREN, _)) => (LPAREN, RPAREN),
                        Some((LBRACE, _)) => (LBRACE, RBRACE),
                        // A single-character reference such as `$X`, `$@`
                        // or `$ `; `$$` is a literal `$`.
                        Some((WHITESPACE, _)) => {
                            seen_reference = true;
                            continue;
                        }
                        // BSD make does not take `:` as a name.
                        Some((OPERATOR, text))
                            if text == ":" && self.variant == Some(MakefileVariant::BSDMake) =>
                        {
                            return false
                        }
                        Some((kind, text))
                            if text.chars().count() == 1
                                && !matches!(
                                    kind,
                                    DOLLAR | NEWLINE | BACKSLASH | COMMENT | RPAREN | RBRACE
                                ) =>
                        {
                            seen_reference = true;
                            continue;
                        }
                        _ => return false,
                    };
                    let mut tokens = tokens.by_ref().map(|(kind, _)| *kind);
                    let mut depth = 1;
                    let mut prev = open;
                    while depth > 0 {
                        let Some(kind) = tokens.next() else {
                            return false;
                        };
                        match kind {
                            k if k == open => depth += 1,
                            k if k == close => depth -= 1,
                            NEWLINE if prev != BACKSLASH => return false,
                            _ => {}
                        }
                        prev = kind;
                    }
                    seen_reference = true;
                }
                Some(_) => return false,
            }
        }
    }

    /// BSD make's rule for recognizing an assignment (`Parse_IsVar`):
    /// outside parentheses and braces, the line contains an assignment
    /// operator before any whitespace-separated second word. The name
    /// may contain almost any character, as in `EXP.[A-]=` or `a:b=c`.
    pub(super) fn is_bsd_assignment_line(&self) -> bool {
        self.is_bsd_assignment(false)
    }

    /// Whether the rest of a dependency line's sources is a target-local
    /// assignment. BSD make cuts off the command after a `;` first.
    pub(super) fn is_bsd_target_local_assignment(&self) -> bool {
        self.is_bsd_assignment(true)
    }

    fn is_bsd_assignment(&self, stop_at_semicolon: bool) -> bool {
        let mut level = 0i32;
        let mut seen_name = false;
        let mut seen_space = false;
        let mut tokens = self.tokens.iter().rev().peekable();
        while let Some((kind, text)) = tokens.next() {
            match kind {
                NEWLINE | COMMENT => return false,
                // The `:sh` assignment modifier, as in `VAR :sh= cmd`
                OPERATOR
                    if level == 0
                        && text == ":"
                        && tokens
                            .peek()
                            .is_some_and(|(k, t)| *k == IDENTIFIER && t == "sh") =>
                {
                    tokens.next();
                }
                LPAREN | LBRACE => {
                    level += 1;
                    seen_name = true;
                }
                RPAREN | RBRACE => level -= 1,
                // A line continuation counts as whitespace.
                BACKSLASH if matches!(tokens.peek(), Some((NEWLINE, _))) => {
                    tokens.next();
                    while tokens
                        .next_if(|(kind, _)| matches!(kind, INDENT | WHITESPACE))
                        .is_some()
                    {}
                    seen_space = seen_name;
                }
                _ if level != 0 => {}
                TEXT if stop_at_semicolon && text == ";" => return false,
                WHITESPACE => seen_space = seen_name,
                OPERATOR if self.is_bsd_make() && is_colons_before_subst(text) => {
                    return !seen_space
                }
                OPERATOR if ASSIGNMENT_OPERATORS.contains(&text.as_str()) => return true,
                _ if seen_space => return false,
                _ => seen_name = true,
            }
        }
        false
    }

    /// Whether the line is a GNU make style `export VAR=value`, which BSD
    /// make accepts if the line has no `:` in it.
    pub(super) fn at_gmake_export(&self) -> bool {
        let mut tokens = self.tokens.iter().rev();
        tokens
            .next()
            .is_some_and(|(kind, text)| *kind == IDENTIFIER && text == "export")
            && tokens.next().is_some_and(|(kind, _)| *kind == WHITESPACE)
            && self.has_assignment_operator_on_line()
            && !self
                .tokens
                .iter()
                .rev()
                .take_while(|(kind, _)| *kind != NEWLINE)
                .any(|(_, text)| text.contains(':'))
    }

    pub(super) fn has_assignment_operator_on_line(&self) -> bool {
        self.tokens
            .iter()
            .rev()
            .take_while(|(kind, _)| *kind != NEWLINE)
            .any(|(kind, text)| *kind == OPERATOR && ASSIGNMENT_OPERATORS.contains(&text.as_str()))
    }

    /// Whether the line starting at `end - 1` in the token stack is an
    /// `undefine` directive, optionally preceded by modifiers.
    /// `undefine = 1` and `undefine: all` instead assign to or make a
    /// target named "undefine".
    fn undefine_at(&self, end: usize) -> bool {
        if !self.gnu_directives_enabled() {
            return false;
        }
        let mut words = self.tokens[..end]
            .iter()
            .rev()
            .filter(|(kind, _)| *kind != WHITESPACE)
            .skip_while(|(kind, text)| {
                *kind == IDENTIFIER
                    && matches!(
                        text.as_str(),
                        "export" | "unexport" | "override" | "private"
                    )
            });
        matches!(words.next(), Some((IDENTIFIER, text)) if text == "undefine")
            && !matches!(words.next(), Some((OPERATOR, _)))
    }

    /// Whether the line is a variable assignment for the variant being
    /// parsed. BSD make only follows its own rule, so that `x{ = 1` is
    /// an assignment for GNU make but not for BSD make.
    pub(super) fn is_variable_assignment_line(&mut self) -> bool {
        if self.is_bsd_make() {
            return self.at_gmake_export() || self.is_bsd_assignment_line();
        }
        self.is_assignment_line()
            || (self.bsd_directives_enabled()
                && self.is_bsd_assignment_line()
                && !self.line_has_dependency_operator())
    }

    pub(super) fn is_assignment_line(&self) -> bool {
        self.assignment_at(self.tokens.len())
    }

    /// Like `is_assignment_line`, for the line starting at `end - 1` in
    /// the token stack.
    fn assignment_at(&self, end: usize) -> bool {
        if self.undefine_at(end) {
            return true;
        }
        let gnu = self.gnu_directives_enabled();
        let is_directive =
            |text: &str| gnu && matches!(text, "export" | "unexport" | "override" | "private");
        let mut tokens = self.tokens[..end].iter().rev().peekable();
        let mut seen_name = false;
        // Whitespace after the name: anything but an operator now means
        // this is not an assignment.
        let mut name_done = false;
        let mut seen_directive = false; // export or override prefix

        loop {
            if !name_done
                && !tokens
                    .peek()
                    .is_some_and(|(kind, text)| *kind == IDENTIFIER && is_directive(text))
            {
                match Self::skip_variable_name(&mut tokens, false) {
                    None => return false,
                    Some(found) => seen_name |= found,
                }
            }
            let Some((kind, text)) = tokens.next() else {
                break;
            };
            match kind {
                NEWLINE => break,
                IDENTIFIER if is_directive(text) => seen_directive = true,
                OPERATOR if ASSIGNMENT_OPERATORS.contains(&text.as_str()) => {
                    return seen_name || seen_directive
                }
                // It's a rule if we see a colon first
                OPERATOR if matches!(text.as_str(), ":" | "::" | "&:" | "&::") => return false,
                WHITESPACE => name_done = seen_name,
                // A line continuation counts as whitespace.
                BACKSLASH if matches!(tokens.peek(), Some((NEWLINE, _))) => {
                    tokens.next();
                    while tokens
                        .next_if(|(kind, _)| matches!(kind, INDENT | WHITESPACE))
                        .is_some()
                    {}
                    name_done = seen_name;
                }
                _ if seen_directive => return true, // Everything after export/override is part of the assignment
                _ => return false,
            }
        }
        // Bare "export VARNAME" (without assignment operator) is a valid GNU Make directive
        seen_directive
    }
}
