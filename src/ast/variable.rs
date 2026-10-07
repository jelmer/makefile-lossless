use super::makefile::MakefileItem;
use super::{is_continuation, line_ending, logical_text, terminate_line_before, LineSyntax};
use crate::lossless::{
    detached_elements, is_sunsh_operator, node_text, parse, remove_with_preceding_comments,
    scan_recipe_variable_refs, Error, ErrorInfo, ParseError, RecipeVariableReference,
    VariableDefinition, VariableReference, ASSIGNMENT_OPERATORS,
};
use crate::MakefileVariant;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::{GreenNodeBuilder, SyntaxNode};

/// Recursively rebuild a syntax node into a GreenNodeBuilder.
fn rebuild_node(builder: &mut GreenNodeBuilder, node: &crate::lossless::SyntaxNode) {
    builder.start_node(node.kind().into());
    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                builder.token(token.kind().into(), token.text());
            }
            rowan::NodeOrToken::Node(child_node) => {
                rebuild_node(builder, &child_node);
            }
        }
    }
    builder.finish_node();
}

fn value_error(context: &str, message: String) -> Error {
    Error::Parse(ParseError {
        errors: vec![ErrorInfo {
            kind: crate::ParseErrorKind::Other,
            message,
            line: 1,
            context: context.to_string(),
        }],
    })
}

/// Whether `text` has a line break that is not part of a line continuation,
/// or ends in a backslash that would continue the line.
fn breaks_line(text: &str) -> bool {
    let mut backslashes = 0;
    for c in text.chars() {
        match c {
            '\\' => backslashes += 1,
            '\n' | '\r' if backslashes % 2 == 0 => return true,
            // The `\n` of a `\r\n` continuation follows the `\r`.
            '\r' => {}
            _ => backslashes = 0,
        }
    }
    backslashes % 2 == 1
}

/// The EXPR node of the single variable definition in `text`, followed by
/// another line, if it parses without errors and its raw value is `value`.
fn parse_value_expr(text: &str, value: &str) -> Option<SyntaxNode<crate::lossless::Lang>> {
    let parsed = parse(&format!("{text}Z = 1\n"), None);
    if !parsed.errors.is_empty() {
        return None;
    }
    let vars: Vec<_> = parsed.root().variable_definitions().collect();
    let [var, _] = vars.as_slice() else {
        return None;
    };
    let expr = var
        .value_expr()
        .filter(|_| var.raw_value().as_deref() == Some(value))?;
    Some(SyntaxNode::new_root_mut(expr.green().into_owned()))
}

/// The number of `define` blocks opened in the body of a `define` block
/// and not closed again, counted the way the parser does: by the first word
/// of each logical line.
fn open_nested_defines(body: &crate::lossless::SyntaxNode) -> usize {
    let tokens: Vec<_> = body
        .descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .collect();
    let lines = tokens.split(|t| t.kind() == NEWLINE && !is_continuation(&t.clone().into()));
    let mut depth = 0usize;
    for line in lines {
        let mut words = line
            .iter()
            .skip_while(|t| matches!(t.kind(), WHITESPACE | INDENT));
        let Some(first) = words.next().filter(|t| t.kind() == IDENTIFIER) else {
            continue;
        };
        let ends_word = match words.next().map(|t| t.kind()) {
            None | Some(WHITESPACE) => true,
            // A line continuation right after the word.
            Some(BACKSLASH) => words.next().is_some_and(|t| t.kind() == NEWLINE),
            _ => false,
        };
        match first.text() {
            "define" if ends_word => depth += 1,
            "endef" if ends_word => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    depth
}

/// Whether `text` is an assignment operator token.
fn is_assignment_operator(text: &str) -> bool {
    ASSIGNMENT_OPERATORS.contains(&text) || is_sunsh_operator(text)
}

impl VariableDefinition {
    /// Internal: the leading directive keywords (`export`/`unexport`/
    /// `override`/`private`/`define`/`undefine`). A keyword only counts as
    /// one when another word follows it, so `undefine = 1` assigns to a
    /// variable named `undefine`. The exception is a trailing keyword without
    /// an assignment operator, such as a bare `export` or the `undefine` in
    /// `override undefine` with its name missing.
    fn directive_keywords(&self) -> Vec<crate::lossless::SyntaxToken> {
        let mut words: Vec<Vec<crate::lossless::SyntaxElement>> = Vec::new();
        let mut in_word = false;
        let mut has_operator = false;
        for it in self.syntax().children_with_tokens() {
            if it.kind() == WHITESPACE || is_continuation(&it) {
                in_word = false;
                continue;
            }
            match it.kind() {
                OPERATOR => {
                    has_operator = true;
                    break;
                }
                NEWLINE | COMMENT => break,
                _ => {}
            }
            if !in_word {
                words.push(Vec::new());
                in_word = true;
            }
            words.last_mut().unwrap().push(it);
        }
        let keyword = |word: &[crate::lossless::SyntaxElement]| match word {
            [rowan::NodeOrToken::Token(t)]
                if t.kind() == IDENTIFIER
                    && matches!(
                        t.text(),
                        "export" | "unexport" | "override" | "private" | "define" | "undefine"
                    ) =>
            {
                Some(t.clone())
            }
            _ => None,
        };
        let count = match words.as_slice() {
            [.., last] if !has_operator && keyword(last).is_some() => words.len(),
            _ => words.len().saturating_sub(1),
        };
        let mut keywords = Vec::new();
        for token in words.iter().take(count).map_while(|word| keyword(word)) {
            let is_last = matches!(token.text(), "define" | "undefine");
            keywords.push(token);
            // Everything after `define` or `undefine` is part of the name.
            if is_last {
                break;
            }
        }
        keywords
    }

    /// The directive keywords on this line with their source ranges, in
    /// source order: any of `export`, `unexport`, `override`, `private`,
    /// `define` and `undefine` before the name, and the `endef` closing a
    /// `define` block.
    ///
    /// A word only counts as a keyword in the same cases as for
    /// [`Self::is_export`] and the like, so `export = 1` has none.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "override define X\nx\nendef\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert_eq!(
    ///     var.keyword_ranges(),
    ///     vec![
    ///         ("override".to_string(), TextRange::new(0.into(), 8.into())),
    ///         ("define".to_string(), TextRange::new(9.into(), 15.into())),
    ///         ("endef".to_string(), TextRange::new(20.into(), 25.into())),
    ///     ]
    /// );
    /// ```
    pub fn keyword_ranges(&self) -> Vec<(String, rowan::TextRange)> {
        let mut keywords: Vec<_> = self
            .directive_keywords()
            .into_iter()
            .map(|t| (t.text().to_string(), t.text_range()))
            .collect();
        if self.is_define() {
            let body = self
                .syntax()
                .children()
                .filter(|it| it.kind() == EXPR)
                .last();
            let endef = body
                .into_iter()
                .flat_map(|body| {
                    std::iter::successors(body.next_sibling_or_token(), |it| {
                        it.next_sibling_or_token()
                    })
                })
                .filter_map(|it| it.into_token())
                .find(|t| t.kind() == IDENTIFIER && t.text() == "endef");
            keywords.extend(endef.map(|t| (t.text().to_string(), t.text_range())));
        }
        keywords
    }

    /// Internal: the elements making up the variable's name, i.e. the
    /// IDENTIFIER tokens and variable references that follow any directive
    /// keywords. A name usually is a single IDENTIFIER, but may contain
    /// references as in `CFLAGS.${PROG}` or backslashes as in `a\b`.
    /// Single source of truth for [`Self::name`], [`Self::name_range`] and
    /// [`Self::set_name`].
    fn name_elements(&self) -> Vec<crate::lossless::SyntaxElement> {
        let directive = self.directive_keywords().pop();
        if let Some(directive) = directive.filter(|t| matches!(t.text(), "define" | "undefine")) {
            // GNU make takes the rest of the line as the name, including any
            // whitespace and line continuations inside it. The parser only
            // emits an OPERATOR token after a `define` name if it is the
            // assignment operator. At the end of the file the line is
            // followed by the empty body of the block, its last EXPR node.
            let is_define = directive.text() == "define";
            let body = self.define_body().map(rowan::NodeOrToken::Node);
            let mut elements: Vec<_> = self
                .after_directive_keywords()
                .take_while(|it| {
                    is_continuation(it)
                        || !(matches!(it.kind(), NEWLINE | COMMENT)
                            || is_define && it.kind() == OPERATOR
                            || Some(it) == body.as_ref())
                })
                .collect();
            while elements
                .last()
                .is_some_and(|it| it.kind() == WHITESPACE || is_continuation(it))
            {
                elements.pop();
            }
            return elements;
        }
        // The parser ends the name at the operator before the value. Look
        // for it from the value, since a BSD make name may itself contain
        // operators, as in `a:b`, and a GNU make name unbalanced brackets,
        // as in `x{`.
        let operator = self
            .syntax()
            .children()
            .filter(|it| it.kind() == EXPR)
            .last()
            .and_then(|value| {
                std::iter::successors(value.prev_sibling_or_token(), |it| {
                    it.prev_sibling_or_token()
                })
                .find(|it| it.kind() != WHITESPACE)
            })
            .filter(|it| {
                it.as_token()
                    .is_some_and(|t| t.kind() == OPERATOR && is_assignment_operator(t.text()))
            });
        // BSD make names may contain almost any character, as in `EXP.[A-]`
        // or `a:b`, including whitespace inside parentheses and braces.
        let mut elements: Vec<_> = self
            .after_directive_keywords()
            .take_while(|it| Some(it) != operator.as_ref())
            .scan(0isize, |level, it| {
                if is_continuation(&it) {
                    return None;
                }
                let in_name = match &it {
                    rowan::NodeOrToken::Token(t) => match t.kind() {
                        LPAREN | LBRACE => {
                            *level += 1;
                            true
                        }
                        RPAREN | RBRACE => {
                            *level -= 1;
                            true
                        }
                        NEWLINE | COMMENT => false,
                        _ if *level != 0 => true,
                        WHITESPACE => false,
                        OPERATOR => !is_assignment_operator(t.text()),
                        _ => true,
                    },
                    rowan::NodeOrToken::Node(n) => n.kind() == EXPR,
                };
                in_name.then_some(it)
            })
            .collect();
        while elements.last().is_some_and(|it| it.kind() == WHITESPACE) {
            elements.pop();
        }
        elements
    }

    /// Internal: the children following the directive keywords and any
    /// whitespace around them.
    fn after_directive_keywords(&self) -> impl Iterator<Item = crate::lossless::SyntaxElement> {
        let keywords = self.directive_keywords();
        self.syntax().children_with_tokens().skip_while(move |it| {
            it.kind() == WHITESPACE
                || is_continuation(it)
                || it.as_token().is_some_and(|t| keywords.contains(t))
        })
    }

    /// Internal: the EXPR node holding the value, which follows the name
    /// (or, for BSD make's empty variable name, the assignment operator).
    pub(crate) fn value_expr(&self) -> Option<crate::lossless::SyntaxNode> {
        let name_end = match self.name_elements().last() {
            Some(element) => element.index(),
            None => self
                .syntax()
                .children_with_tokens()
                .find(|it| it.kind() == OPERATOR)?
                .index(),
        };
        self.syntax()
            .children()
            .find(|it| it.kind() == EXPR && it.index() > name_end)
    }

    /// Get the name of the variable definition
    ///
    /// For an `undefine` directive this is the rest of the line, which may
    /// contain whitespace: `undefine A B` undefines the variable "A B".
    /// Likewise for a `define` header up to the assignment operator. A
    /// line continuation inside it reads as a single space.
    pub fn name(&self) -> Option<String> {
        let elements = self.name_elements();
        if elements.is_empty() {
            return None;
        }
        let mut name = String::new();
        let mut in_continuation = false;
        for it in &elements {
            if is_continuation(it) {
                if !in_continuation {
                    name.truncate(name.trim_end().len());
                    name.push(' ');
                    in_continuation = true;
                }
            } else if !(in_continuation && it.kind() == WHITESPACE) {
                name.push_str(&it.to_string());
                in_continuation = false;
            }
        }
        Some(name)
    }

    /// All variable names on this line, including variable references
    /// such as `$(VARS)` verbatim.
    ///
    /// Usually this is just [`Self::name`], but a bare `export` or
    /// `unexport` directive can list several variables. An `undefine`
    /// or `define` directive always has a single name, as in `undefine A B`,
    /// which yields just "A B".
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "export quiet Q KBUILD_VERBOSE\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert_eq!(
    ///     var.names().collect::<Vec<_>>(),
    ///     vec!["quiet", "Q", "KBUILD_VERBOSE"]
    /// );
    /// ```
    pub fn names(&self) -> impl Iterator<Item = String> {
        if self.is_undefine() || self.is_define() {
            return self.name().into_iter().collect::<Vec<_>>().into_iter();
        }
        let mut names = Vec::new();
        let mut current = String::new();
        for it in self.after_directive_keywords().take_while(|it| {
            matches!(it.kind(), IDENTIFIER | BACKSLASH | EXPR | WHITESPACE) || is_continuation(it)
        }) {
            if it.kind() == WHITESPACE || is_continuation(&it) {
                if !current.is_empty() {
                    names.push(std::mem::take(&mut current));
                }
            } else {
                current.push_str(&it.to_string());
            }
        }
        if !current.is_empty() {
            names.push(current);
        }
        names.into_iter()
    }

    /// The source range covering just the variable's name.
    ///
    /// Excludes any `export`/`override`/`private`/`define` prefix, the
    /// assignment operator and the value. Lets callers compute a minimal
    /// rename edit instead of re-rendering the whole definition (and with it
    /// the surrounding whitespace).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "export FOO := bar\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// let range = var.name_range().unwrap();
    /// assert_eq!(usize::from(range.start()), 7);
    /// assert_eq!(usize::from(range.end()), 10);
    /// ```
    pub fn name_range(&self) -> Option<rowan::TextRange> {
        let elements = self.name_elements();
        let first = elements.first()?.text_range();
        let last = elements.last()?.text_range();
        Some(first.cover(last))
    }

    /// Returns true if this assignment is a `define` ... `endef` block.
    pub fn is_define(&self) -> bool {
        self.directive_keywords()
            .iter()
            .any(|t| t.text() == "define")
    }

    /// Internal: the EXPR node holding the body of a `define` block.
    fn define_body(&self) -> Option<crate::lossless::SyntaxNode> {
        if !self.is_define() {
            return None;
        }
        self.syntax()
            .children()
            .filter(|it| it.kind() == EXPR)
            .last()
    }

    /// Returns true if this is a `define` block that is closed by an
    /// `endef` line.
    ///
    /// Returns false for a `define` block that runs to the end of the file,
    /// which the parser reports as
    /// [`ParseErrorKind::MissingEndef`](crate::ParseErrorKind::MissingEndef),
    /// and for any other kind of assignment.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "define A\nx\nendef\n".parse().unwrap();
    /// assert!(makefile.variable_definitions().next().unwrap().has_endef());
    /// let (makefile, _) = Makefile::from_str_relaxed("define A\nx\n");
    /// assert!(!makefile.variable_definitions().next().unwrap().has_endef());
    /// ```
    pub fn has_endef(&self) -> bool {
        let Some(body) = self.define_body() else {
            return false;
        };
        std::iter::successors(body.next_sibling_or_token(), |it| {
            it.next_sibling_or_token()
        })
        .any(|it| {
            it.as_token()
                .is_some_and(|t| t.kind() == IDENTIFIER && t.text() == "endef")
        })
    }

    /// Close a `define` block that has no `endef`, as one running to the end
    /// of the file does.
    ///
    /// Nested `define` lines in the body that are not closed get an `endef`
    /// too, since the parser counts them when looking for the end of the
    /// block. If the body does not end with a newline, one is added before
    /// the first `endef`.
    ///
    /// Returns `Ok(true)` if `endef` lines were added and `Ok(false)` if
    /// the block already had one. Returns an error if this is not a
    /// `define` block.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let (makefile, _) = Makefile::from_str_relaxed("define A\ndefine B\nx");
    /// let mut var = makefile.variable_definitions().next().unwrap();
    /// assert!(var.add_endef().unwrap());
    /// assert_eq!(makefile.code(), "define A\ndefine B\nx\nendef\nendef\n");
    /// assert!(var.has_endef());
    /// ```
    pub fn add_endef(&mut self) -> Result<bool, Error> {
        let Some(body) = self.define_body() else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: "Cannot add endef to a variable that is not a define block"
                        .to_string(),
                    line: self.line() + 1,
                    context: "variable_add_endef".to_string(),
                }],
            }));
        };
        if self.has_endef() {
            return Ok(false);
        }
        let eol = super::line_ending(self.syntax());

        // The parser marks the missing endef with an empty ERROR node.
        let errors: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| n.index() > body.index() && n.kind() == ERROR && n.text().is_empty())
            .collect();
        for error in errors {
            error.detach();
        }

        let mut inner = Vec::new();
        let last = body
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .last();
        match last {
            // A continued last line would continue onto `endef`, so end it
            // with a blank line.
            Some(t) if t.kind() == NEWLINE => {
                if is_continuation(&t.into()) {
                    inner.push((NEWLINE, eol.as_str()));
                }
            }
            Some(_) => {
                let len = body.children_with_tokens().count();
                super::terminate_line_before(&body, len, &eol);
            }
            // An empty body: end the `define` line instead.
            None => {
                super::terminate_line_before(self.syntax(), body.index(), &eol);
            }
        }
        for _ in 0..open_nested_defines(&body) {
            inner.push((IDENTIFIER, "endef"));
            inner.push((NEWLINE, eol.as_str()));
        }
        let len = body.children_with_tokens().count();
        body.splice_children(len..len, detached_elements(&inner, None));

        let body_index = body.index();
        self.syntax().splice_children(
            body_index + 1..body_index + 1,
            detached_elements(&[(IDENTIFIER, "endef"), (NEWLINE, &eol)], None),
        );
        Ok(true)
    }

    /// Iterate `$(VAR)` and `${VAR}` variable references in the body of a
    /// `define` block.
    ///
    /// The references are found by scanning each line of the body the same
    /// way as by [`Recipe::variable_references`](crate::Recipe::variable_references),
    /// with ranges in the original source. Returns an empty list if this is
    /// not a `define` block.
    ///
    /// The references in a `define` body are also in the syntax tree, where
    /// [`Makefile::variable_references`](crate::Makefile::variable_references)
    /// finds them along with function calls, automatic variables and
    /// references spanning lines.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "define E\n$(FOO) $$(BAR) ${BAZ:a=b}\nendef\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// let names: Vec<_> = var
    ///     .define_variable_references()
    ///     .iter()
    ///     .map(|r| r.name().to_string())
    ///     .collect();
    /// assert_eq!(names, vec!["FOO", "BAZ"]);
    /// ```
    #[deprecated(
        note = "use the references in the syntax tree, from Makefile::variable_references, which also finds function calls, automatic variables and references spanning lines"
    )]
    pub fn define_variable_references(&self) -> Vec<RecipeVariableReference> {
        let mut out = Vec::new();
        if !self.is_define() {
            return out;
        }
        if let Some(body) = self.value_expr() {
            scan_recipe_variable_refs(
                &body.text().to_string(),
                body.text_range().start().into(),
                &mut out,
            );
        }
        out
    }

    /// Check if this is an `undefine` directive, e.g. `undefine FOO`
    ///
    /// Such a node has a name but no assignment operator or value.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "override undefine CC\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert!(var.is_undefine());
    /// assert!(var.is_override());
    /// assert_eq!(var.name(), Some("CC".to_string()));
    /// assert_eq!(var.assignment_operator(), None);
    /// ```
    pub fn is_undefine(&self) -> bool {
        self.directive_keywords()
            .iter()
            .any(|t| t.text() == "undefine")
    }

    /// Check if this variable definition is exported
    pub fn is_export(&self) -> bool {
        self.directive_keywords()
            .iter()
            .any(|t| t.text() == "export")
    }

    /// Check if this variable definition uses the `unexport` directive
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "unexport CC\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert!(var.is_unexport());
    /// assert!(!var.is_export());
    /// ```
    pub fn is_unexport(&self) -> bool {
        self.directive_keywords()
            .iter()
            .any(|t| t.text() == "unexport")
    }

    /// Check if this variable definition uses the `override` directive
    ///
    /// `override FOO = bar` makes the assignment take precedence over any
    /// value passed on the make command line.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "override CC = clang\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert!(var.is_override());
    /// assert_eq!(var.name(), Some("CC".to_string()));
    /// ```
    pub fn is_override(&self) -> bool {
        self.directive_keywords()
            .iter()
            .any(|t| t.text() == "override")
    }

    /// Check if this variable definition uses the `private` modifier
    ///
    /// A private target-specific variable is not inherited by the target's
    /// prerequisites.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "all: private CFLAGS = -O2\n".parse().unwrap();
    /// let var = rule.scoped_assignment().unwrap();
    /// assert!(var.is_private());
    /// assert_eq!(var.name(), Some("CFLAGS".to_string()));
    /// ```
    pub fn is_private(&self) -> bool {
        self.directive_keywords()
            .iter()
            .any(|t| t.text() == "private")
    }

    /// Returns true if this is a target-specific assignment on a rule line,
    /// as in `all: CFLAGS = -O2`, i.e. one returned by
    /// [`Rule::scoped_assignment`](crate::Rule::scoped_assignment).
    ///
    /// An assignment on its own line in a rule's body, such as inside a
    /// conditional between recipe lines, is not target-specific: GNU make
    /// treats it as an ordinary assignment, even though
    /// [`Makefile::rules`](crate::Makefile::rules) sees the conditional as
    /// part of the rule.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "all: X = 1\nall:\nifdef D\n\techo\nY = 1\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let vars: Vec<_> = makefile
    ///     .variable_definitions()
    ///     .map(|v| (v.name().unwrap(), v.is_target_specific()))
    ///     .collect();
    /// assert_eq!(vars, vec![("X".to_string(), true), ("Y".to_string(), false)]);
    /// ```
    pub fn is_target_specific(&self) -> bool {
        self.syntax().parent().is_some_and(|p| p.kind() == RULE)
    }

    /// Get the assignment operator/flavor used in this variable definition
    ///
    /// Returns the operator as a string: "=", ":=", "::=", ":::=", "+=", "?=", or "!=",
    /// or ":sh=" for BSD make's alternative shell assignment operator, which
    /// may also be written with whitespace as in `VAR :sh = cmd`.
    ///
    /// Returns `None` for an `undefine` directive, even one such as
    /// `undefine A = b` whose name contains an operator.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "VAR := value\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert_eq!(var.assignment_operator(), Some(":=".to_string()));
    /// ```
    pub fn assignment_operator(&self) -> Option<String> {
        if self.is_undefine() {
            return None;
        }
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == OPERATOR && is_assignment_operator(t.text()))
            .map(|t| {
                if is_sunsh_operator(t.text()) {
                    ":sh=".to_string()
                } else {
                    t.text().to_string()
                }
            })
    }

    /// Get the raw value of the variable definition, as written
    ///
    /// Line continuations, escapes such as `\#` and whitespace before a
    /// trailing comment are kept; CRLF line endings are converted to LF.
    /// See [`Self::value`] for the value as GNU make stores it.
    pub fn raw_value(&self) -> Option<String> {
        self.value_expr().map(|it| node_text(&it))
    }

    /// The source range of the value, covering the same text as
    /// [`Self::raw_value`].
    ///
    /// For a `define` block this is the body, including the line break
    /// before `endef`. Returns `None` if there is no value, as for an
    /// `undefine` directive; an empty value gives an empty range.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "X := a $(B) # c\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert_eq!(var.value_range(), Some(TextRange::new(5.into(), 12.into())));
    /// ```
    pub fn value_range(&self) -> Option<rowan::TextRange> {
        self.value_expr().map(|it| it.text_range())
    }

    /// The variable references in the value, in source order, including
    /// those nested in other references, as in the function call
    /// `$(patsubst %.c,%.o,$(SRCS))` and its argument `$(SRCS)`.
    ///
    /// References in the variable's name are not included. For a `define`
    /// block, those in the body are.
    ///
    /// The whitespace before a comment after the value is kept, although
    /// make includes it in the value.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "X.$(A) = $(B) $(addprefix -I,$(C))\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// let names: Vec<_> = var.value_references().filter_map(|r| r.name()).collect();
    /// assert_eq!(names, vec!["B", "addprefix", "C"]);
    /// ```
    pub fn value_references(&self) -> impl Iterator<Item = VariableReference> {
        self.value_expr()
            .into_iter()
            .flat_map(|expr| expr.descendants())
            .filter_map(VariableReference::cast)
    }

    /// Get the value of the variable as `variant` stores it, before
    /// expansion; for GNU make this is what `$(value VAR)` returns.
    ///
    /// Unlike [`Self::raw_value`], line continuations are collapsed into a
    /// single space, escapes and comments are handled the way `variant`
    /// handles them and CRLF line endings are converted to LF. The parse
    /// tree does not record which variant a makefile was parsed as, so it
    /// has to be passed in.
    ///
    /// - GNU make drops the whitespace before a line continuation. `\#` is
    ///   unescaped to `#` except inside variable references, and the
    ///   backslashes before it, before a line continuation or before a
    ///   trailing comment are halved. Whitespace before a trailing comment
    ///   is part of the value. In `define` blocks only the line
    ///   continuations are collapsed.
    /// - POSIX make is handled like GNU make with `.POSIX:`, which keeps the
    ///   whitespace before a line continuation.
    /// - BSD make keeps the whitespace before a line continuation, does not
    ///   halve backslashes, unescapes `\#` and ends the value at `#` even
    ///   inside variable references, and removes trailing whitespace.
    /// - For nmake, `\#` is not an escape, but a caret before one of
    ///   ``: ; # ( ) $ ^ \ { } ! @ -`` is, as in `^#`, and a caret at the end
    ///   of a line continues the value with a newline. Other carets and
    ///   those in quoted strings are literal. The makefile has to be parsed
    ///   as nmake for this, since other variants lex `^#` as a caret and a
    ///   comment.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = "X := a\\#b \\\n    c # comment\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert_eq!(var.raw_value(), Some("a\\#b \\\n    c ".to_string()));
    /// assert_eq!(var.value(MakefileVariant::GNUMake), Some("a#b c ".to_string()));
    /// assert_eq!(var.value(MakefileVariant::BSDMake), Some("a#b  c".to_string()));
    /// ```
    pub fn value(&self, variant: MakefileVariant) -> Option<String> {
        let expr = self.value_expr()?;
        let tokens = expr
            .descendants_with_tokens()
            .filter_map(|it| it.into_token());
        let syntax = LineSyntax::from(variant);
        if self.is_define() {
            let mut value = logical_text(&expr, tokens, syntax, false);
            // The newline before `endef` is not part of the value.
            if value.ends_with('\n') {
                value.pop();
            }
            Some(value)
        } else {
            let value = logical_text(&expr, tokens, syntax, true);
            Some(value.trim_start_matches([' ', '\t']).to_string())
        }
    }

    /// Get the parent item of this variable definition, if any
    ///
    /// Returns `Some(MakefileItem)` if this variable has a parent that is a MakefileItem
    /// (e.g., a Conditional), or `None` if the parent is the root Makefile node.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = r#"ifdef DEBUG
    /// VAR = value
    /// endif
    /// "#.parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let var = cond.if_items().next().unwrap();
    /// // Variable's parent is the conditional
    /// assert!(matches!(var, makefile_lossless::MakefileItem::Variable(_)));
    /// ```
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }

    /// Remove this variable definition from its parent makefile
    ///
    /// This also removes the comment lines directly above it, with no blank line in between, as
    /// they document it. If that leaves a blank line above where it was
    /// followed by another blank line or the end of the file, the blank line
    /// above is removed too.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "VAR = value\n".parse().unwrap();
    /// let mut var = makefile.variable_definitions().next().unwrap();
    /// var.remove();
    /// assert_eq!(makefile.variable_definitions().count(), 0);
    /// ```
    pub fn remove(&mut self) {
        if let Some(parent) = self.syntax().parent() {
            remove_with_preceding_comments(self.syntax(), &parent);
        }
    }

    /// Change the assignment operator of this variable definition while preserving everything else
    /// (export prefix, variable name, value, whitespace, etc.)
    ///
    /// # Arguments
    /// * `op` - The new operator: "=", ":=", "::=", ":::=", "+=", "?=", or "!="
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "VAR := value\n".parse().unwrap();
    /// let mut var = makefile.variable_definitions().next().unwrap();
    /// var.set_assignment_operator("?=");
    /// assert_eq!(var.assignment_operator(), Some("?=".to_string()));
    /// assert!(makefile.code().contains("VAR ?= value"));
    /// ```
    pub fn set_assignment_operator(&mut self, op: &str) {
        // The name may contain operator tokens too, as in BSD make's `a:b=c`.
        let op_index = self
            .syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == OPERATOR && is_assignment_operator(t.text()))
            .map(|t| t.index());

        // Build a new VARIABLE node, copying all children but replacing the OPERATOR token
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(VARIABLE.into());

        for child in self.syntax().children_with_tokens() {
            match child {
                rowan::NodeOrToken::Token(token) if Some(token.index()) == op_index => {
                    builder.token(OPERATOR.into(), op);
                }
                rowan::NodeOrToken::Token(token) => {
                    builder.token(token.kind().into(), token.text());
                }
                rowan::NodeOrToken::Node(node) => {
                    rebuild_node(&mut builder, &node);
                }
            }
        }

        builder.finish_node();
        let new_variable = SyntaxNode::new_root_mut(builder.finish());

        // Replace the old VARIABLE node with the new one
        let index = self.syntax().index();
        if let Some(parent) = self.syntax().parent() {
            parent.splice_children(index..index + 1, vec![new_variable.clone().into()]);

            // Update self to point to the new node
            *self = VariableDefinition::cast(
                parent
                    .children_with_tokens()
                    .nth(index)
                    .and_then(|it| it.into_node())
                    .unwrap(),
            )
            .unwrap();
        }
    }

    /// Rename the variable, preserving the operator, value and any
    /// `export`/`override`/`define` prefix.
    ///
    /// Replaces the whole name as returned by [`Self::name`], including any
    /// variable references in it. A no-op if the definition has no name.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "export FOO := bar\n".parse().unwrap();
    /// let mut var = makefile.variable_definitions().next().unwrap();
    /// var.set_name("BAZ");
    /// assert_eq!(var.name(), Some("BAZ".to_string()));
    /// assert_eq!(makefile.code(), "export BAZ := bar\n");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `new_name` contains a newline. Use
    /// [`Self::try_set_name`] to get an error instead.
    pub fn set_name(&mut self, new_name: &str) {
        self.try_set_name(new_name)
            .unwrap_or_else(|e| panic!("invalid variable name: {e}"))
    }

    /// Rename the variable, like [`Self::set_name`]
    ///
    /// Returns an error, leaving the definition unchanged, if `new_name`
    /// contains a newline.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "FOO := bar\n".parse().unwrap();
    /// let mut var = makefile.variable_definitions().next().unwrap();
    /// assert!(var.try_set_name("A\nB").is_err());
    /// var.try_set_name("BAZ").unwrap();
    /// assert_eq!(makefile.code(), "BAZ := bar\n");
    /// ```
    pub fn try_set_name(&mut self, new_name: &str) -> Result<(), Error> {
        if new_name.contains(['\n', '\r']) {
            return Err(value_error(
                "set_name",
                format!("Variable name {new_name:?} contains a newline"),
            ));
        }
        self.replace_name(new_name);
        Ok(())
    }

    fn replace_name(&mut self, new_name: &str) {
        let elements = self.name_elements();
        let (Some(first), Some(last)) = (elements.first(), elements.last()) else {
            return;
        };
        let name_indices = first.index()..=last.index();

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(VARIABLE.into());

        for child in self.syntax().children_with_tokens() {
            if name_indices.contains(&child.index()) {
                if child.index() == *name_indices.start() {
                    builder.token(IDENTIFIER.into(), new_name);
                }
                continue;
            }
            match child {
                rowan::NodeOrToken::Token(token) => {
                    builder.token(token.kind().into(), token.text());
                }
                rowan::NodeOrToken::Node(node) => {
                    rebuild_node(&mut builder, &node);
                }
            }
        }

        builder.finish_node();
        let new_variable = SyntaxNode::new_root_mut(builder.finish());

        let index = self.syntax().index();
        if let Some(parent) = self.syntax().parent() {
            parent.splice_children(index..index + 1, vec![new_variable.clone().into()]);

            *self = VariableDefinition::cast(
                parent
                    .children_with_tokens()
                    .nth(index)
                    .and_then(|it| it.into_node())
                    .unwrap(),
            )
            .unwrap();
        }
    }

    /// Remove a trailing whitespace token at the tail of the value, if any.
    ///
    /// In GNU Make, whitespace after the last non-comment content but before
    /// the end of the line (or a `#` comment) is included in the variable's
    /// value. This is almost always unintentional. This method strips that
    /// trailing whitespace while preserving everything else (comments,
    /// nested variable references, line continuations).
    ///
    /// Returns `true` if a trailing whitespace token was removed.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "VAR = value  \n".parse().unwrap();
    /// let mut var = makefile.variable_definitions().next().unwrap();
    /// assert!(var.trim_trailing_value_whitespace());
    /// assert_eq!(makefile.code(), "VAR = value\n");
    /// ```
    pub fn trim_trailing_value_whitespace(&mut self) -> bool {
        let Some(token) = self.trailing_value_whitespace() else {
            return false;
        };
        token.detach();
        true
    }

    /// Internal: the whitespace token at the end of the value, before any
    /// comment, that [`Self::trim_trailing_value_whitespace`] removes.
    fn trailing_value_whitespace(&self) -> Option<crate::lossless::SyntaxToken> {
        // Comments are part of the EXPR but the whitespace we care about
        // precedes them (Make includes that whitespace in the value).
        self.value_expr()?
            .children_with_tokens()
            .filter(|c| c.kind() != COMMENT)
            .last()?
            .into_token()
            .filter(|t| t.kind() == WHITESPACE)
    }

    /// The source range of whitespace at the end of the value, before any
    /// comment, which GNU make includes in the value.
    ///
    /// This is the whitespace that [`Self::trim_trailing_value_whitespace`]
    /// removes. Whitespace inside a nested variable reference does not
    /// count.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "X = a  # c\nY = b\n".parse().unwrap();
    /// let ranges: Vec<_> = makefile
    ///     .variable_definitions()
    ///     .map(|v| v.trailing_value_whitespace_range())
    ///     .collect();
    /// assert_eq!(ranges, vec![Some(TextRange::new(5.into(), 7.into())), None]);
    /// ```
    pub fn trailing_value_whitespace_range(&self) -> Option<rowan::TextRange> {
        self.trailing_value_whitespace().map(|t| t.text_range())
    }

    /// Update the value of this variable definition while preserving the rest
    /// (export prefix, operator, whitespace, etc.)
    ///
    /// For a `define` block, `new_value` is the body, as returned by
    /// [`Self::raw_value`]. A line ending is added if it does not end in one.
    ///
    /// A space is added between the operator and a value that was empty, as
    /// in `X =`. An `export` or `unexport` directive of a single variable
    /// without a value, as in `export X`, becomes an assignment with `=`.
    ///
    /// The whitespace before a comment after the value is kept, although
    /// make includes it in the value.
    ///
    /// # Panics
    ///
    /// Panics if `new_value` can not be written as the value, or the
    /// definition can not have one, as described for
    /// [`Self::try_set_value`], which returns an error instead.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "export VAR := old_value\n".parse().unwrap();
    /// let mut var = makefile.variable_definitions().next().unwrap();
    /// var.set_value("new_value");
    /// assert_eq!(var.raw_value(), Some("new_value".to_string()));
    /// assert!(makefile.code().contains("export VAR := new_value"));
    /// ```
    pub fn set_value(&mut self, new_value: &str) {
        self.try_set_value(new_value)
            .unwrap_or_else(|e| panic!("invalid variable value: {e}"))
    }

    /// Update the value of this variable definition, like
    /// [`Self::set_value`]
    ///
    /// Returns an error, leaving the definition unchanged, if `new_value`
    /// contains a newline that is not part of a line continuation or ends
    /// in a backslash that would continue the line. In a `define` block
    /// newlines are allowed, but the body must not end the block early,
    /// e.g. with an `endef` line. Also returns an error if the definition
    /// can not have a value, such as an `undefine` directive or an `export`
    /// directive of several variables.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "VAR = old\n".parse().unwrap();
    /// let mut var = makefile.variable_definitions().next().unwrap();
    /// assert!(var.try_set_value("a\nb").is_err());
    /// var.try_set_value("a \\\n  b").unwrap();
    /// assert_eq!(makefile.code(), "VAR = a \\\n  b\n");
    /// ```
    pub fn try_set_value(&mut self, new_value: &str) -> Result<(), Error> {
        let new_expr = if self.is_define() {
            let eol = line_ending(self.syntax());
            let body = if new_value.is_empty() || new_value.ends_with('\n') {
                new_value.to_string()
            } else {
                format!("{new_value}{eol}")
            };
            parse_value_expr(&format!("define X{eol}{body}endef{eol}"), &body).ok_or_else(|| {
                value_error(
                    "set_value",
                    format!("Cannot write {new_value:?} as the body of a define block"),
                )
            })?
        } else {
            if breaks_line(new_value) {
                return Err(value_error(
                    "set_value",
                    format!("Cannot write {new_value:?} as a value on a single line"),
                ));
            }
            parse_value_expr(&format!("X = {new_value}\n"), new_value).unwrap_or_else(|| {
                // TODO: escape values that the parser would read differently,
                // such as ones containing `#`
                let mut builder = GreenNodeBuilder::new();
                builder.start_node(EXPR.into());
                builder.token(IDENTIFIER.into(), new_value);
                builder.finish_node();
                SyntaxNode::new_root_mut(builder.finish())
            })
        };

        let Some(mut expr) = self.value_expr() else {
            return self.insert_value(&new_expr);
        };
        if self.is_define() {
            // A `define` line at the end of the file has no line break
            // before the body, or one that continues it.
            let eol = line_ending(self.syntax());
            let continued = expr
                .prev_sibling_or_token()
                .is_some_and(|it| it.kind() == NEWLINE && is_continuation(&it));
            let index = if continued {
                let index = expr.index();
                self.syntax()
                    .splice_children(index..index, detached_elements(&[(NEWLINE, &eol)], None));
                index + 1
            } else {
                terminate_line_before(self.syntax(), expr.index(), &eol)
            };
            expr = self
                .syntax()
                .children_with_tokens()
                .nth(index)
                .and_then(|it| it.into_node())
                .expect("the body follows the define line");
        }
        let after_operator = expr
            .prev_sibling_or_token()
            .is_some_and(|it| it.kind() == OPERATOR);
        let tokens: &[_] = if new_value.is_empty() || self.is_define() || !after_operator {
            &[]
        } else {
            &[(WHITESPACE, " ")]
        };
        // The parser puts the whitespace before a comment at the end of the
        // value, or before it if the value is empty.
        let before_comment = expr
            .next_sibling_or_token()
            .filter(|it| it.kind() == COMMENT && !new_value.is_empty())
            .and_then(|_| {
                expr.last_child_or_token()
                    .or_else(|| expr.prev_sibling_or_token())
            })
            .and_then(|it| it.into_token())
            .filter(|t| t.kind() == WHITESPACE);
        let mut elements = value_elements(tokens, &new_expr, before_comment.as_slice());
        // A line continuation at the end of the file leaves the line break,
        // and any indentation after it, in the value. Keep the line break as
        // the end of the line.
        let ends_line = !self.is_define() && expr.next_sibling_or_token().is_none();
        let newline = expr
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() != INDENT)
            .last()
            .filter(|t| ends_line && t.kind() == NEWLINE);
        if let Some(newline) = newline {
            elements.extend(detached_elements(&[(NEWLINE, newline.text())], None));
        }
        let expr_idx = expr.index();
        self.syntax()
            .splice_children(expr_idx..expr_idx + 1, elements);
        Ok(())
    }

    /// Internal: add an `=` operator and `expr`, an EXPR node, to a
    /// definition without a value, as in `export X`.
    fn insert_value(&mut self, expr: &SyntaxNode<crate::lossless::Lang>) -> Result<(), Error> {
        let name = self.name_elements();
        let is_undefine = self
            .directive_keywords()
            .iter()
            .any(|t| t.text() == "undefine");
        let rest_is_blank = name.last().is_some_and(|last| {
            std::iter::successors(last.next_sibling_or_token(), |it| {
                it.next_sibling_or_token()
            })
            .all(|it| matches!(it.kind(), WHITESPACE | COMMENT | NEWLINE) || is_continuation(&it))
        });
        if is_undefine || self.is_define() || !rest_is_blank {
            return Err(value_error(
                "set_value",
                format!("{:?} has no value to set", self.syntax().to_string()),
            ));
        }
        let index = name.last().unwrap().index() + 1;
        // The parser includes the rest of the logical line up to a comment
        // in the value: whitespace and line continuations.
        let rest: Vec<_> = self
            .syntax()
            .children_with_tokens()
            .skip(index)
            .take_while(|it| match it.kind() {
                COMMENT => false,
                NEWLINE => is_continuation(it),
                _ => true,
            })
            .filter_map(|it| it.into_token())
            .collect();
        let mut tokens = vec![(WHITESPACE, " "), (OPERATOR, "=")];
        let mut trailing = &rest[..];
        if !expr.text().is_empty() {
            tokens.push((WHITESPACE, " "));
        } else if let Some((first, tail)) =
            rest.split_first().filter(|(t, _)| t.kind() == WHITESPACE)
        {
            // The whitespace after the operator is not part of an empty value.
            tokens.push((WHITESPACE, first.text()));
            trailing = tail;
        }
        let elements = value_elements(&tokens, expr, trailing);
        // TODO: splice them out once rowan's splice_children removes more
        // than the first child of the range, as it does from 0.17 on.
        for token in &rest {
            token.detach();
        }
        self.syntax().splice_children(index..index, elements);
        Ok(())
    }
}

/// The elements to insert for a value: `tokens` followed by `expr`, an EXPR
/// node, with copies of `trailing` added to it.
fn value_elements(
    tokens: &[(crate::SyntaxKind, &str)],
    expr: &SyntaxNode<crate::lossless::Lang>,
    trailing: &[crate::lossless::SyntaxToken],
) -> Vec<crate::lossless::SyntaxElement> {
    let mut children: Vec<_> = expr.green().children().map(|it| it.to_owned()).collect();
    children.extend(
        trailing
            .iter()
            .map(|t| rowan::GreenToken::new(t.kind().into(), t.text()).into()),
    );
    detached_elements(tokens, Some(rowan::GreenNode::new(EXPR.into(), children)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lossless::Makefile;

    #[test]
    fn test_variable_parent() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();

        let var = makefile.variable_definitions().next().unwrap();
        let parent = var.parent();
        // Parent is ROOT node which doesn't cast to MakefileItem
        assert!(parent.is_none());
    }

    #[test]
    fn test_assignment_operator_simple() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.assignment_operator(), Some("=".to_string()));
    }

    #[test]
    fn test_assignment_operator_recursive() {
        let makefile: Makefile = "VAR := value\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.assignment_operator(), Some(":=".to_string()));
    }

    #[test]
    fn test_assignment_operator_conditional() {
        let makefile: Makefile = "VAR ?= value\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.assignment_operator(), Some("?=".to_string()));
    }

    #[test]
    fn test_assignment_operator_append() {
        let makefile: Makefile = "VAR += value\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.assignment_operator(), Some("+=".to_string()));
    }

    #[test]
    fn test_assignment_operator_export() {
        let makefile: Makefile = "export VAR := value\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.assignment_operator(), Some(":=".to_string()));
    }

    #[test]
    fn test_is_define_true() {
        let makefile: Makefile = "define greeting\necho hello\nendef\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_define());
    }

    #[test]
    fn test_is_define_false_for_plain_assignment() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(!var.is_define());
    }

    #[test]
    fn test_is_define_false_for_value_containing_define_word() {
        // The identifier check must look for a `define` keyword token, not a
        // value that merely contains the word.
        let makefile: Makefile = "VAR = define\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(!var.is_define());
    }

    #[test]
    fn test_set_assignment_operator_simple_to_conditional() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("?=");
        assert_eq!(var.assignment_operator(), Some("?=".to_string()));
        assert_eq!(makefile.code(), "VAR ?= value\n");
    }

    #[test]
    fn test_set_assignment_operator_recursive_to_conditional() {
        let makefile: Makefile = "VAR := value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("?=");
        assert_eq!(var.assignment_operator(), Some("?=".to_string()));
        assert_eq!(makefile.code(), "VAR ?= value\n");
    }

    #[test]
    fn test_set_assignment_operator_preserves_export() {
        let makefile: Makefile = "export VAR := value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("?=");
        assert_eq!(var.assignment_operator(), Some("?=".to_string()));
        assert!(var.is_export());
        assert_eq!(makefile.code(), "export VAR ?= value\n");
    }

    #[test]
    fn test_set_assignment_operator_preserves_whitespace() {
        let makefile: Makefile = "VAR  :=  value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("?=");
        assert_eq!(var.assignment_operator(), Some("?=".to_string()));
        assert_eq!(makefile.code(), "VAR  ?=  value\n");
    }

    #[test]
    fn test_set_assignment_operator_preserves_value() {
        let makefile: Makefile = "VAR := old_value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("=");
        assert_eq!(var.assignment_operator(), Some("=".to_string()));
        assert_eq!(var.raw_value(), Some("old_value".to_string()));
        assert_eq!(makefile.code(), "VAR = old_value\n");
    }

    #[test]
    fn test_set_assignment_operator_to_triple_colon() {
        let makefile: Makefile = "VAR := value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("::=");
        assert_eq!(var.assignment_operator(), Some("::=".to_string()));
        assert_eq!(makefile.code(), "VAR ::= value\n");
    }

    #[test]
    fn test_combined_operations() {
        let makefile: Makefile = "export VAR := old_value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();

        // Change operator
        var.set_assignment_operator("?=");
        assert_eq!(var.assignment_operator(), Some("?=".to_string()));

        // Change value
        var.set_value("new_value");
        assert_eq!(var.raw_value(), Some("new_value".to_string()));

        // Verify everything
        assert!(var.is_export());
        assert_eq!(var.name(), Some("VAR".to_string()));
        assert_eq!(makefile.code(), "export VAR ?= new_value\n");
    }

    #[test]
    fn test_set_name_simple() {
        let makefile: Makefile = "VAR := value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_name("RENAMED");
        assert_eq!(var.name(), Some("RENAMED".to_string()));
        assert_eq!(var.assignment_operator(), Some(":=".to_string()));
        assert_eq!(var.raw_value(), Some("value".to_string()));
        assert_eq!(makefile.code(), "RENAMED := value\n");
    }

    #[test]
    fn test_set_name_preserves_export() {
        let makefile: Makefile = "export FOO = nocheck\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_name("BAR");
        assert!(var.is_export());
        assert_eq!(var.name(), Some("BAR".to_string()));
        assert_eq!(makefile.code(), "export BAR = nocheck\n");
    }

    #[test]
    fn test_set_name_preserves_override_and_whitespace() {
        let makefile: Makefile = "override  FOO  :=  bar\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_name("BAZ");
        assert!(var.is_override());
        assert_eq!(makefile.code(), "override  BAZ  :=  bar\n");
    }

    #[test]
    fn test_set_name_undefine_with_spaces() {
        let makefile: Makefile = "undefine A B # c\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert_eq!(usize::from(var.name_range().unwrap().start()), 9);
        assert_eq!(usize::from(var.name_range().unwrap().end()), 12);
        var.set_name("C");
        assert!(var.is_undefine());
        assert_eq!(var.name(), Some("C".to_string()));
        assert_eq!(makefile.code(), "undefine C # c\n");
    }

    #[test]
    fn test_set_name_does_not_touch_value_reference() {
        let makefile: Makefile = "FOO := $(FOO) extra\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_name("BAR");
        assert_eq!(makefile.code(), "BAR := $(FOO) extra\n");
    }

    #[test]
    fn test_name_range_simple() {
        let text = "FOO := bar\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        let range = var.name_range().unwrap();
        assert_eq!(usize::from(range.start()), 0);
        assert_eq!(usize::from(range.end()), 3);
        assert_eq!(&text[range.start().into()..range.end().into()], "FOO");
    }

    #[test]
    fn test_name_range_skips_export_prefix() {
        let text = "export FOO := bar\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        let range = var.name_range().unwrap();
        assert_eq!(&text[range.start().into()..range.end().into()], "FOO");
    }

    #[test]
    fn test_name_range_skips_override_prefix() {
        let text = "override  FOO  :=  bar\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        let range = var.name_range().unwrap();
        assert_eq!(&text[range.start().into()..range.end().into()], "FOO");
    }

    #[test]
    fn test_name_range_excludes_value_reference() {
        let text = "FOO := $(FOO) extra\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        let range = var.name_range().unwrap();
        assert_eq!(usize::from(range.start()), 0);
        assert_eq!(usize::from(range.end()), 3);
    }

    #[test]
    fn test_name_range_matches_name() {
        let text = "export  BAR:=1\nFOO = 2\n";
        let makefile: Makefile = text.parse().unwrap();
        for var in makefile.variable_definitions() {
            let range = var.name_range().unwrap();
            assert_eq!(
                &text[range.start().into()..range.end().into()],
                var.name().unwrap().as_str()
            );
        }
    }

    #[test]
    fn test_override_simple() {
        let makefile: Makefile = "override CC = clang\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_override());
        assert!(!var.is_export());
        assert_eq!(var.name(), Some("CC".to_string()));
        assert_eq!(var.assignment_operator(), Some("=".to_string()));
        assert_eq!(var.raw_value(), Some("clang".to_string()));
    }

    #[test]
    fn test_override_with_immediate_op() {
        let makefile: Makefile = "override FOO := bar\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_override());
        assert_eq!(var.name(), Some("FOO".to_string()));
        assert_eq!(var.assignment_operator(), Some(":=".to_string()));
    }

    #[test]
    fn test_override_export() {
        let makefile: Makefile = "override export FOO = bar\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_override());
        assert!(var.is_export());
        assert_eq!(var.name(), Some("FOO".to_string()));
    }

    #[test]
    fn test_export_override() {
        // GNU Make accepts either order.
        let makefile: Makefile = "export override FOO = bar\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_override());
        assert!(var.is_export());
        assert_eq!(var.name(), Some("FOO".to_string()));
    }

    #[test]
    fn test_keyword_as_variable_name() {
        let makefile: Makefile = "private = 1\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("private".to_string()));
        assert!(!var.is_private());
    }

    #[test]
    fn test_private() {
        let makefile: Makefile = "private X = 1\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("X".to_string()));
        assert_eq!(var.assignment_operator(), Some("=".to_string()));
        assert_eq!(var.raw_value(), Some("1".to_string()));
        assert!(var.is_private());
        assert!(!var.is_export());
        assert!(!var.is_override());
    }

    #[test]
    fn test_private_export() {
        let makefile: Makefile = "private export X := 2\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("X".to_string()));
        assert_eq!(var.assignment_operator(), Some(":=".to_string()));
        assert_eq!(var.raw_value(), Some("2".to_string()));
        assert!(var.is_private());
        assert!(var.is_export());
        assert!(!var.is_override());
        assert_eq!(makefile.to_string(), "private export X := 2\n");
    }

    #[test]
    fn test_override_as_variable_name() {
        let makefile: Makefile = "override := 2\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("override".to_string()));
        assert_eq!(var.assignment_operator(), Some(":=".to_string()));
        assert_eq!(var.raw_value(), Some("2".to_string()));
        assert!(!var.is_override());
    }

    #[test]
    fn test_export_as_variable_name() {
        let makefile: Makefile = "export = 1\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("export".to_string()));
        assert_eq!(var.raw_value(), Some("1".to_string()));
        assert!(!var.is_export());
    }

    /// Build a VARIABLE node directly, bypassing the parser.
    fn variable_from_tokens(tokens: &[(crate::SyntaxKind, &str)]) -> VariableDefinition {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(VARIABLE.into());
        for (kind, text) in tokens {
            builder.token((*kind).into(), text);
        }
        builder.finish_node();
        VariableDefinition::cast(SyntaxNode::new_root_mut(builder.finish())).unwrap()
    }

    #[test]
    fn test_bare_keyword_directive() {
        // Check the keyword logic independently of the parser, including
        // forms such as a bare `override` that it doesn't produce.
        let var = variable_from_tokens(&[(IDENTIFIER, "export"), (NEWLINE, "\n")]);
        assert!(var.is_export());
        assert!(!var.is_override());
        assert_eq!(var.name(), None);

        let var = variable_from_tokens(&[
            (IDENTIFIER, "export"),
            (WHITESPACE, " "),
            (COMMENT, "# all"),
            (NEWLINE, "\n"),
        ]);
        assert!(var.is_export());
        assert_eq!(var.name(), None);

        let var = variable_from_tokens(&[(IDENTIFIER, "override"), (WHITESPACE, " ")]);
        assert!(var.is_override());
        assert!(!var.is_export());
        assert_eq!(var.name(), None);
    }

    #[test]
    fn test_override_keyword_named_variable() {
        // GNU make treats this as an override of a variable named `export`.
        let makefile: Makefile = "override export = 5\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("export".to_string()));
        assert_eq!(var.raw_value(), Some("5".to_string()));
        assert!(var.is_override());
        assert!(!var.is_export());
    }

    #[test]
    fn test_without_override() {
        let makefile: Makefile = "FOO = bar\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(!var.is_override());
    }

    #[test]
    fn test_override_in_makefile_with_other_lines() {
        let makefile: Makefile = "FOO = a\noverride BAR := b\n".parse().unwrap();
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars.len(), 2);
        assert_eq!(vars[0].name(), Some("FOO".to_string()));
        assert!(!vars[0].is_override());
        assert_eq!(vars[1].name(), Some("BAR".to_string()));
        assert!(vars[1].is_override());
    }

    #[test]
    fn test_set_assignment_operator_preserves_shell_call() {
        let makefile: Makefile = "DEB_HOST_ARCH := $(shell dpkg-architecture -qDEB_HOST_ARCH)\n"
            .parse()
            .unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("?=");
        assert_eq!(var.assignment_operator(), Some("?=".to_string()));
        assert_eq!(
            makefile.code(),
            "DEB_HOST_ARCH ?= $(shell dpkg-architecture -qDEB_HOST_ARCH)\n"
        );
    }

    #[test]
    fn test_trim_trailing_value_whitespace_single_space() {
        let makefile: Makefile = "VAR = value \n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = value\n");
    }

    #[test]
    fn test_trim_trailing_value_whitespace_multiple_spaces() {
        let makefile: Makefile = "VAR = value    \n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = value\n");
    }

    #[test]
    fn test_trim_trailing_value_whitespace_tab() {
        let makefile: Makefile = "VAR = value\t\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = value\n");
    }

    #[test]
    fn test_trim_trailing_value_whitespace_none() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(!var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = value\n");
    }

    #[test]
    fn test_trim_trailing_value_whitespace_preserves_comment() {
        // `VAR = value # comment` sets VAR to "value " — the trailing space
        // before the `#` is part of the value. Trimming should strip just that.
        let makefile: Makefile = "VAR = value # comment\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = value# comment\n");
    }

    #[test]
    fn test_trim_trailing_value_whitespace_preserves_internal_whitespace() {
        let makefile: Makefile = "VAR = foo bar   \n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = foo bar\n");
    }

    #[test]
    fn test_trim_trailing_value_whitespace_with_var_ref() {
        let makefile: Makefile = "VAR = $(BAR)  \n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = $(BAR)\n");
    }

    #[test]
    fn test_trim_trailing_value_whitespace_empty_value() {
        // `VAR = ` has an empty EXPR; the whitespace is between OPERATOR and
        // NEWLINE, not part of the value.
        let makefile: Makefile = "VAR = \n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(!var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = \n");
    }

    #[test]
    fn test_trim_trailing_value_whitespace_line_continuation() {
        // The last token in EXPR is BACKSLASH, not WHITESPACE — don't trim.
        let makefile: Makefile = "VAR = foo \\\n\tbar\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(!var.trim_trailing_value_whitespace());
        assert_eq!(makefile.code(), "VAR = foo \\\n\tbar\n");
    }

    #[test]
    fn test_name_with_variable_reference() {
        let makefile: Makefile = "CPPFLAGS.${PROG}+= -DX\nDIRS-$(CONFIG_FOO) += foo\n"
            .parse()
            .unwrap();
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars[0].name(), Some("CPPFLAGS.${PROG}".to_string()));
        assert_eq!(vars[0].assignment_operator(), Some("+=".to_string()));
        assert_eq!(vars[0].raw_value(), Some("-DX".to_string()));
        let range = vars[0].name_range().unwrap();
        assert_eq!(
            &makefile.code()[std::ops::Range::from(range)],
            "CPPFLAGS.${PROG}"
        );
        assert_eq!(vars[1].name(), Some("DIRS-$(CONFIG_FOO)".to_string()));
        assert_eq!(vars[1].raw_value(), Some("foo".to_string()));
    }

    #[test]
    fn test_set_name_with_variable_reference() {
        let makefile: Makefile = "COPTS.${f}+=\t-O0\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_name("COPTS.foo.c");
        assert_eq!(var.name(), Some("COPTS.foo.c".to_string()));
        assert_eq!(makefile.code(), "COPTS.foo.c+=\t-O0\n");
    }

    #[test]
    fn test_set_name_with_backslash() {
        let makefile: Makefile = "export a\\b = 1\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        let range = var.name_range().unwrap();
        assert_eq!(&makefile.code()[std::ops::Range::from(range)], "a\\b");
        var.set_name("c");
        assert_eq!(var.name(), Some("c".to_string()));
        assert_eq!(makefile.code(), "export c = 1\n");
    }

    #[test]
    fn test_set_value_with_variable_reference_in_name() {
        let makefile: Makefile = "A.${B} = old\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_value("new");
        assert_eq!(makefile.code(), "A.${B} = new\n");
    }

    #[test]
    fn test_set_value_before_comment() {
        // The whitespace before a comment is kept.
        for (text, value, expected) in [
            ("X = a # c\n", "new", "X = new # c\n"),
            ("X = a  # c\n", "new", "X = new  # c\n"),
            ("X = # c\n", "new", "X = new # c\n"),
            ("X =  # c\n", "new", "X =  new  # c\n"),
            ("X =\t# c\n", "new", "X =\tnew\t# c\n"),
            ("X =# c\n", "new", "X = new# c\n"),
            ("a: X = # c\n", "new", "a: X = new # c\n"),
            ("export X := a # c\r\n", "new", "export X := new # c\r\n"),
        ] {
            let makefile: Makefile = text.parse().unwrap();
            let mut var = makefile.variable_definitions().next().unwrap();
            var.set_value(value);
            assert_eq!(makefile.code(), expected, "{text:?}");
            crate::test_util::assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_escaped_hash_in_value() {
        let makefile: Makefile = "FOO = a\\#b # comment\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.raw_value(), Some("a\\#b ".to_string()));
    }

    #[test]
    fn test_set_assignment_operator_with_operator_in_name() {
        let parsed =
            crate::Makefile::parse_with_variant("a:b=c\n", crate::MakefileVariant::BSDMake);
        let makefile = parsed.tree();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("+=");
        assert_eq!(var.name(), Some("a:b".to_string()));
        assert_eq!(makefile.code(), "a:b+=c\n");
    }

    #[test]
    fn test_export_names_line_continuation() {
        for keyword in ["export", "unexport"] {
            let code = format!("{} X \\\n  Y\\\n\t$(Z)\n", keyword);
            let makefile: Makefile = code.parse().unwrap();
            assert_eq!(makefile.to_string(), code);
            assert_eq!(makefile.rules().count(), 0);
            let vars: Vec<_> = makefile.variable_definitions().collect();
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].name(), Some("X".to_string()));
            assert_eq!(vars[0].names().collect::<Vec<_>>(), vec!["X", "Y", "$(Z)"]);
        }
    }

    #[test]
    fn test_export_line_continuation_before_name() {
        let code = "export \\\n  X Y\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_export());
        assert_eq!(var.name(), Some("X".to_string()));
        assert_eq!(var.names().collect::<Vec<_>>(), vec!["X", "Y"]);
    }

    #[test]
    fn test_undefine_line_continuation_before_name() {
        let code = "undefine \\\n  X\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_undefine());
        assert_eq!(var.name(), Some("X".to_string()));
    }

    #[test]
    fn test_undefine_line_continuation_after_name() {
        let code = "undefine X \\\n\nall:\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("X".to_string()));
        assert_eq!(makefile.rules().count(), 1);

        // Like `undefine X Y`, this names a single variable "X Y".
        let code = "undefine X \\\n  Y\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("X Y".to_string()));
        assert_eq!(makefile.rules().count(), 0);
    }

    #[test]
    fn test_continuation_before_operator() {
        // As in Linux's drivers/scsi/Makefile.
        for variant in [
            None,
            Some(crate::MakefileVariant::GNUMake),
            Some(crate::MakefileVariant::BSDMake),
        ] {
            let text = "flags-$(CONFIG_X) \\\n\t\t:= -DA \\\n\t\t-DB\nY = 1\n";
            let parsed = match variant {
                None => crate::Makefile::parse(text),
                Some(v) => crate::Makefile::parse_with_variant(text, v),
            };
            assert!(parsed.ok(), "{variant:?}");
            let vars: Vec<_> = parsed.tree().variable_definitions().collect();
            assert_eq!(vars.len(), 2, "{variant:?}");
            assert_eq!(vars[0].name(), Some("flags-$(CONFIG_X)".to_string()));
            assert_eq!(vars[0].assignment_operator(), Some(":=".to_string()));
        }
    }

    #[test]
    fn test_dollar_before_line_continuation() {
        // Make joins the lines before expanding `$`, so this is `X = ab`.
        let makefile: Makefile = "X = a$\\\n\tb\nY = 1\n".parse().unwrap();
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars.len(), 2);
        assert_eq!(vars[0].raw_value(), Some("a$\\\n\tb".to_string()));
    }

    fn value_in(variant: MakefileVariant, code: &str) -> Option<String> {
        let makefile = Makefile::parse_with_variant(code, variant).tree();
        assert_eq!(makefile.to_string(), code);
        let var = makefile.variable_definitions().next().unwrap();
        var.value(variant)
    }

    fn value_of(code: &str) -> Option<String> {
        value_in(MakefileVariant::GNUMake, code)
    }

    #[test]
    fn test_value_plain() {
        assert_eq!(value_of("X = a b\n"), Some("a b".to_string()));
    }

    #[test]
    fn test_value_escaped_hash() {
        assert_eq!(value_of("X := a\\#b\n"), Some("a#b".to_string()));
        assert_eq!(value_of("X := a\\#b # c\n"), Some("a#b ".to_string()));
    }

    #[test]
    fn test_value_backslashes_before_hash() {
        // GNU make halves a run of backslashes before `#`; an odd run
        // escapes the `#`, an even run leaves it starting a comment.
        assert_eq!(value_of("X := a\\\\#b\n"), Some("a\\".to_string()));
        assert_eq!(value_of("X := a\\\\\\#b\n"), Some("a\\#b".to_string()));
        assert_eq!(value_of("X := a\\\\\\\\#b\n"), Some("a\\\\".to_string()));
    }

    #[test]
    fn test_value_other_backslashes_kept() {
        assert_eq!(value_of("X = a\\b\\\\c\n"), Some("a\\b\\\\c".to_string()));
    }

    #[test]
    fn test_value_keeps_whitespace_before_comment() {
        assert_eq!(value_of("X = a  # c\n"), Some("a  ".to_string()));
        assert_eq!(value_of("X = a  \n"), Some("a  ".to_string()));
    }

    #[test]
    fn test_value_continuation() {
        assert_eq!(value_of("X = a \\\n   b\n"), Some("a b".to_string()));
        assert_eq!(value_of("X = a\\\n b\n"), Some("a b".to_string()));
        assert_eq!(value_of("X = a\t\\\n\t b\n"), Some("a b".to_string()));
        assert_eq!(value_of("X = a \\\n  \\\n  b\n"), Some("a b".to_string()));
        assert_eq!(value_of("X = a \\\n  \n"), Some("a ".to_string()));
        assert_eq!(value_of("X = \\\n  a\n"), Some("a".to_string()));
    }

    #[test]
    fn test_value_continuation_after_backslashes() {
        // The backslashes before a continuation are halved; an even run
        // does not continue the line and is kept as is.
        assert_eq!(value_of("X = a \\\\\\\n b\n"), Some("a \\ b".to_string()));
        assert_eq!(
            value_of("X = a \\\\\\\\\\\n b\n"),
            Some("a \\\\ b".to_string())
        );
        assert_eq!(value_of("X = a \\\\\n"), Some("a \\\\".to_string()));
    }

    #[test]
    fn test_value_continued_comment() {
        assert_eq!(value_of("X = a\\#b # c \\\n b\n"), Some("a#b ".to_string()));
    }

    #[test]
    fn test_value_crlf() {
        assert_eq!(
            value_of("X = a \\\r\n b\r\nY = c\r\n"),
            Some("a b".to_string())
        );
    }

    #[test]
    fn test_value_escaped_hash_in_reference() {
        // GNU make does not treat `#` inside a variable reference as a
        // comment, and leaves a `\#` there alone.
        assert_eq!(
            value_of("X = $(info a\\#b) c\\#d #e\n"),
            Some("$(info a\\#b) c#d ".to_string())
        );
        assert_eq!(
            value_of("X = ${a\\#b} $a\\#b\n"),
            Some("${a\\#b} $a#b".to_string())
        );
    }

    #[test]
    fn test_value_hash_in_reference() {
        let code = "X = ${A:M#*} $(a #b) c # d\n";
        assert_eq!(value_of(code), Some("${A:M#*} $(a #b) c ".to_string()));
        assert_eq!(posix_value(code), Some("${A:M#*} $(a #b) c ".to_string()));
        assert_eq!(bsd_value(code), Some("${A:M".to_string()));
    }

    #[test]
    fn test_value_bsd_hash_in_reference_parsed_as_default() {
        let makefile: Makefile = "X = ${A:M#*} b\nY = ${L:[#]}\n".parse().unwrap();
        assert_eq!(
            makefile
                .variable_definitions()
                .map(|v| v.value(MakefileVariant::BSDMake))
                .collect::<Vec<_>>(),
            vec![Some("${A:M".to_string()), Some("${L:[#]}".to_string())]
        );
    }

    #[test]
    fn test_value_continuation_in_reference() {
        assert_eq!(
            value_of("X = $(info a \\\n   b)\n"),
            Some("$(info a b)".to_string())
        );
    }

    #[test]
    fn test_value_define() {
        // Continuations are collapsed in define bodies, but comments and
        // `\#` are kept.
        assert_eq!(
            value_of("define X\na \\\n  b\\#c # d\nendef\n"),
            Some("a b\\#c # d".to_string())
        );
        assert_eq!(
            value_of("define X\n\na\n\nendef\n"),
            Some("\na\n".to_string())
        );
        assert_eq!(
            value_of("define X\na \\\\\n  b\nendef\n"),
            Some("a \\\\\n  b".to_string())
        );
        assert_eq!(
            value_of("define X\na \\\\\\\n  b\nendef\n"),
            Some("a \\ b".to_string())
        );
        assert_eq!(value_of("define X\nendef\n"), Some("".to_string()));
    }

    #[test]
    fn test_value_define_crlf() {
        assert_eq!(
            value_of("define X\r\na \\\r\n  b\r\nc\r\nendef\r\n"),
            Some("a b\nc".to_string())
        );
    }

    #[test]
    fn test_value_dollar_before_continuation() {
        assert_eq!(value_of("X = a$\\\n\tb\n"), Some("a$ b".to_string()));
    }

    #[test]
    fn test_value_undefine() {
        assert_eq!(value_of("undefine X\n"), None);
    }

    #[test]
    fn test_value_target_specific() {
        let rule: crate::Rule = "foo: X = a\\#b \\\n  c # d\n".parse().unwrap();
        assert_eq!(
            rule.scoped_assignment()
                .unwrap()
                .value(MakefileVariant::GNUMake),
            Some("a#b c ".to_string())
        );
    }

    fn bsd_value(code: &str) -> Option<String> {
        value_in(MakefileVariant::BSDMake, code)
    }

    #[test]
    fn test_value_bsd_strips_trailing_whitespace() {
        assert_eq!(bsd_value("X = a  # c\n"), Some("a".to_string()));
        assert_eq!(bsd_value("X = a  \n"), Some("a".to_string()));
        assert_eq!(bsd_value("X = a \\\n\nY = b\n"), Some("a".to_string()));
    }

    #[test]
    fn test_value_bsd_escaped_space() {
        assert_eq!(bsd_value("X = a\\ \n"), Some("a\\ ".to_string()));
        assert_eq!(bsd_value("X = a\\  \n"), Some("a\\ ".to_string()));
    }

    #[test]
    fn test_value_bsd_escaped_hash() {
        assert_eq!(bsd_value("X = a\\#b # c\n"), Some("a#b".to_string()));
        assert_eq!(
            bsd_value("X = ${a\\#b} $(c\\#d)\n"),
            Some("${a#b} $(c#d)".to_string())
        );
    }

    #[test]
    fn test_value_bsd_backslashes_not_halved() {
        assert_eq!(bsd_value("X = a\\\\#b\n"), Some("a\\\\".to_string()));
        assert_eq!(bsd_value("X = a\\\\\\#b\n"), Some("a\\\\#b".to_string()));
        assert_eq!(bsd_value("X = a\\b\\\\c\n"), Some("a\\b\\\\c".to_string()));
        assert_eq!(bsd_value("X = a \\\\\n"), Some("a \\\\".to_string()));
    }

    #[test]
    fn test_value_bsd_comment_in_reference() {
        let makefile = Makefile::parse_with_variant("X = ${A:M#*} b\n", MakefileVariant::BSDMake);
        let var = makefile.tree().variable_definitions().next().unwrap();
        assert_eq!(
            var.value(MakefileVariant::BSDMake),
            Some("${A:M".to_string())
        );
        assert_eq!(bsd_value("X = ${L:[#]}\n"), Some("${L:[#]}".to_string()));
    }

    #[test]
    fn test_value_quotes_ignored() {
        // Neither GNU make nor BSD make treats quotes specially when
        // reading a line.
        let cases = [
            ("A?= @echo '\\#  '\n", "@echo '#  '", "@echo '#  '"),
            ("X = '\\#x' \"\\#y\"\n", "'#x' \"#y\"", "'#x' \"#y\""),
            ("X = 'a\\\\\\#b'\n", "'a\\#b'", "'a\\\\#b'"),
            ("X = 'a\\\\#b'\n", "'a\\", "'a\\\\"),
            ("X = \"a#b\"\n", "\"a", "\"a"),
            ("X = 'a \\\n    b'\n", "'a b'", "'a  b'"),
            (
                "X = $(subst '\\#',z,'\\#')\n",
                "$(subst '\\#',z,'\\#')",
                "$(subst '#',z,'#')",
            ),
        ];
        for (code, gnu, bsd) in cases {
            assert_eq!(value_of(code), Some(gnu.to_string()), "{code:?}");
            assert_eq!(bsd_value(code), Some(bsd.to_string()), "{code:?}");
            let makefile: Makefile = code.parse().unwrap();
            assert_eq!(makefile.to_string(), code);
            let var = makefile.variable_definitions().next().unwrap();
            assert_eq!(var.value(MakefileVariant::GNUMake), Some(gnu.to_string()));
            assert_eq!(var.value(MakefileVariant::BSDMake), Some(bsd.to_string()));
        }
        assert_eq!(
            posix_value("X = 'a \\\n    b' '\\#'\n"),
            Some("'a  b' '#'".to_string())
        );
        assert_eq!(
            value_in(MakefileVariant::NMake, "X = 'a\\#b'\n"),
            Some("'a\\".to_string())
        );
    }

    #[test]
    fn test_raw_value_comment_in_quotes() {
        let makefile: Makefile = "A = \"a#b\" # c\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.raw_value(), Some("\"a".to_string()));
    }

    #[test]
    fn test_reference_in_quotes() {
        let makefile: Makefile = "A = \"$(B)\" '${C}'\n".parse().unwrap();
        let names: Vec<_> = makefile
            .variable_references()
            .filter_map(|r| r.name())
            .collect();
        assert_eq!(names, vec!["B".to_string(), "C".to_string()]);
    }

    #[test]
    fn test_value_bsd_continuation() {
        assert_eq!(bsd_value("X = a \\\n   b\n"), Some("a  b".to_string()));
        assert_eq!(bsd_value("X = a\t\\\n\t b\n"), Some("a\t b".to_string()));
        assert_eq!(bsd_value("X = a\\\n b\n"), Some("a b".to_string()));
        assert_eq!(
            bsd_value("X = a \\\n  \\\n  b\n"),
            Some("a   b".to_string())
        );
        assert_eq!(
            bsd_value("X = a \\\\\\\n b\n"),
            Some("a \\\\ b".to_string())
        );
        assert_eq!(bsd_value("X = \\\n  a\n"), Some("a".to_string()));
    }

    fn posix_value(code: &str) -> Option<String> {
        value_in(MakefileVariant::POSIXMake, code)
    }

    #[test]
    fn test_value_posix_continuation() {
        assert_eq!(posix_value("x = a \\\n   b\n"), Some("a  b".to_string()));
        assert_eq!(posix_value("x = a\t\\\n\t b\n"), Some("a\t b".to_string()));
        assert_eq!(posix_value("x = a\\\n b\n"), Some("a b".to_string()));
        assert_eq!(
            posix_value("x = a \\\n  \\\n  b\n"),
            Some("a   b".to_string())
        );
        assert_eq!(
            posix_value("x = a \\\\\\\n b\n"),
            Some("a \\ b".to_string())
        );
        assert_eq!(posix_value("x = \\\n  a\n"), Some("a".to_string()));
    }

    #[test]
    fn test_value_posix_comments() {
        assert_eq!(posix_value("x = a\\#b # c\n"), Some("a#b ".to_string()));
        assert_eq!(posix_value("x = a\\\\#b\n"), Some("a\\".to_string()));
        assert_eq!(posix_value("x = a\\\\\\#b\n"), Some("a\\#b".to_string()));
        assert_eq!(posix_value("x = ${a\\#b}\n"), Some("${a\\#b}".to_string()));
        assert_eq!(posix_value("x = a  \n"), Some("a  ".to_string()));
    }

    #[test]
    fn test_value_nmake() {
        // `\#` is not an escape in nmake, so the `#` starts a comment.
        assert_eq!(
            value_in(MakefileVariant::NMake, "X = a\\#b\n"),
            Some("a\\".to_string())
        );
    }

    #[test]
    fn test_value_nmake_caret_escapes() {
        let nmake_value = |code| value_in(MakefileVariant::NMake, code);
        assert_eq!(nmake_value("X = a^#b # c\n"), Some("a#b ".to_string()));
        assert_eq!(nmake_value("X = a^\\\n"), Some("a\\".to_string()));
        assert_eq!(nmake_value("X = a^^#b\n"), Some("a^".to_string()));
        assert_eq!(nmake_value("X = ^$(Y)\n"), Some("$(Y)".to_string()));
        assert_eq!(
            nmake_value("X = ^:^;^(^)^{^}^!^@^-\n"),
            Some(":;(){}!@-".to_string())
        );
        // A caret before any other character, or in a quoted string, is
        // literal.
        assert_eq!(nmake_value("X = a^b\n"), Some("a^b".to_string()));
        assert_eq!(nmake_value("X = \"a^:b\"\n"), Some("\"a^:b\"".to_string()));
        assert_eq!(
            nmake_value("X = \"a^:b\" ^:\n"),
            Some("\"a^:b\" :".to_string())
        );
        // A caret at the end of a line continues a quoted string too.
        assert_eq!(nmake_value("X = \"a^\nb\"\n"), Some("\"a\nb\"".to_string()));
    }

    #[test]
    fn test_value_nmake_caret_newline() {
        let code = "CMDS = cls^\ndir\nY = 1\n";
        let makefile = Makefile::parse_with_variant(code, MakefileVariant::NMake).tree();
        assert_eq!(makefile.to_string(), code);
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(
            vars.iter()
                .map(|v| (v.name(), v.value(MakefileVariant::NMake)))
                .collect::<Vec<_>>(),
            vec![
                (Some("CMDS".to_string()), Some("cls\ndir".to_string())),
                (Some("Y".to_string()), Some("1".to_string())),
            ]
        );
    }

    #[test]
    fn test_value_caret_not_escape_in_other_variants() {
        for variant in [
            MakefileVariant::GNUMake,
            MakefileVariant::BSDMake,
            MakefileVariant::POSIXMake,
        ] {
            assert_eq!(
                value_in(variant, "X = a^\\#b\n"),
                Some("a^#b".to_string()),
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_name_with_unbalanced_brackets() {
        // GNU make does not pair up brackets in a name: `x{ = 1` assigns to
        // `x{`. BSD make doesn't accept these as assignments at all.
        let cases = [
            ("x{ = 1\n", "x{"),
            ("x( = 1\n", "x("),
            ("a{b = 1\n", "a{b"),
            ("a(b := 1\n", "a(b"),
            ("a}b = 1\n", "a}b"),
            ("a)b += 1\n", "a)b"),
            ("{x = 1\n", "{x"),
            ("(x = 1\n", "(x"),
            ("}x = 1\n", "}x"),
            (")x := 1\n", ")x"),
            ("{ = 1\n", "{"),
            ("override x{ = 1\n", "x{"),
        ];
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::POSIXMake),
            Some(MakefileVariant::NMake),
        ] {
            for (code, name) in cases {
                let gnu = matches!(variant, None | Some(MakefileVariant::GNUMake));
                if !gnu && code.starts_with("override") {
                    continue;
                }
                let parsed = match variant {
                    None => Makefile::parse(code),
                    Some(v) => Makefile::parse_with_variant(code, v),
                };
                assert!(parsed.ok(), "{variant:?} {code:?}: {:?}", parsed.errors());
                let makefile = parsed.tree();
                assert_eq!(makefile.code(), code);
                let vars: Vec<_> = makefile.variable_definitions().collect();
                assert_eq!(vars.len(), 1, "{variant:?} {code:?}");
                assert_eq!(
                    vars[0].name(),
                    Some(name.to_string()),
                    "{variant:?} {code:?}"
                );
                assert_eq!(vars[0].raw_value(), Some("1".to_string()), "{variant:?}");
            }
        }
    }

    #[test]
    fn test_name_with_brackets_bsd() {
        // BSD make pairs up brackets in a name, and lets the nesting level
        // go negative.
        for (code, name) in [("a{b c} = 1\n", "a{b c}"), ("a}b{ = 1\n", "a}b{")] {
            let parsed = Makefile::parse_with_variant(code, MakefileVariant::BSDMake);
            assert!(parsed.ok(), "{code:?}: {:?}", parsed.errors());
            let makefile = parsed.tree();
            assert_eq!(makefile.code(), code);
            let var = makefile.variable_definitions().next().unwrap();
            assert_eq!(var.name(), Some(name.to_string()));
            assert_eq!(var.raw_value(), Some("1".to_string()));
        }
    }

    #[test]
    fn test_set_name_with_unbalanced_bracket() {
        let makefile: Makefile = "x{ = 1\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_name("y");
        assert_eq!(makefile.code(), "y = 1\n");
    }

    #[allow(deprecated)]
    fn define_references(text: &str) -> Vec<(String, std::ops::Range<usize>)> {
        let makefile: Makefile = text.parse().unwrap();
        makefile
            .variable_definitions()
            .flat_map(|v| v.define_variable_references())
            .map(|r| (r.name().to_string(), r.text_range().into()))
            .collect()
    }

    #[test]
    fn test_define_variable_references() {
        assert_eq!(
            define_references(
                "define E\n$(FOO) $(FOO:a=b) $$(X) $$$(Y)\n\t$(shell echo ${A.${B}})\nendef\n"
            ),
            vec![
                ("FOO".to_string(), 11..14),
                ("FOO".to_string(), 18..21),
                ("Y".to_string(), 37..38),
                ("A.${B}".to_string(), 56..62),
                ("B".to_string(), 60..61),
            ]
        );
    }

    #[test]
    fn test_define_variable_references_in_conditional() {
        assert_eq!(
            define_references("ifdef X\ndefine E :=\n$(FOO)\nendef\nendif\n"),
            vec![("FOO".to_string(), 22..25)]
        );
    }

    #[test]
    fn test_define_variable_references_not_define() {
        assert_eq!(define_references("E = $(FOO)\n"), vec![]);
    }

    fn name_references(text: &str) -> Vec<(String, Option<String>, std::ops::Range<usize>)> {
        let makefile: Makefile = text.parse().unwrap();
        assert_eq!(makefile.code(), text);
        makefile
            .variable_references()
            .map(|r| {
                (
                    r.syntax().text().to_string(),
                    r.name(),
                    r.syntax().text_range().into(),
                )
            })
            .collect()
    }

    fn define_name(text: &str) -> (Option<String>, Option<std::ops::Range<usize>>) {
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_define());
        (var.name(), var.name_range().map(Into::into))
    }

    #[test]
    fn test_define_name_references() {
        let r = |text: &str, name: &str, range: std::ops::Range<usize>| {
            (text.to_string(), Some(name.to_string()), range)
        };
        assert_eq!(
            name_references("define $(A) =\nbody\nendef\n"),
            vec![r("$(A)", "A", 7..11)]
        );
        assert_eq!(
            name_references("define $(PREFIX)_FLAGS\nbody\nendef\n"),
            vec![r("$(PREFIX)", "PREFIX", 7..16)]
        );
        assert_eq!(
            name_references("define ${A}.${B}\nbody\nendef\n"),
            vec![r("${A}", "A", 7..11), r("${B}", "B", 12..16)]
        );
        assert_eq!(
            name_references("override define $(A)\nbody\nendef\n"),
            vec![r("$(A)", "A", 16..20)]
        );
        assert_eq!(
            name_references("export define $(A) :=\nbody\nendef\n"),
            vec![r("$(A)", "A", 14..18)]
        );
        assert_eq!(
            name_references("define $(A) \\\n $(B)\nbody\nendef\n"),
            vec![r("$(A)", "A", 7..11), r("$(B)", "B", 15..19)]
        );
        assert_eq!(
            name_references("define $(A)\n$(B)\nendef\n"),
            vec![r("$(A)", "A", 7..11), r("$(B)", "B", 12..16)]
        );
        // Consistent with an ordinary assignment.
        assert_eq!(name_references("$(A)_X = 1\n"), vec![r("$(A)", "A", 0..4)]);
        assert_eq!(
            name_references("override $(A) = 1\n"),
            vec![r("$(A)", "A", 9..13)]
        );
    }

    #[test]
    fn test_define_name_with_references() {
        for (text, name, range) in [
            ("define $(A) =\nbody\nendef\n", "$(A)", 7..11),
            (
                "define $(PREFIX)_FLAGS\nbody\nendef\n",
                "$(PREFIX)_FLAGS",
                7..22,
            ),
            ("define ${A}.${B}\nbody\nendef\n", "${A}.${B}", 7..16),
            ("override define $(A)\nbody\nendef\n", "$(A)", 16..20),
            ("export define $(A) :=\nbody\nendef\n", "$(A)", 14..18),
            ("define $(A) B\nbody\nendef\n", "$(A) B", 7..13),
            ("define $(A) \\\n $(B)\nbody\nendef\n", "$(A) $(B)", 7..19),
            ("define $(A) B =\nbody\nendef\n", "$(A) B =", 7..15),
        ] {
            assert_eq!(
                define_name(text),
                (Some(name.to_string()), Some(range)),
                "{text:?}"
            );
        }
    }

    #[test]
    fn test_define_name_references_keep_body() {
        let text = "export define $(A) :=\n$(B)\nendef\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.is_export());
        assert_eq!(var.assignment_operator(), Some(":=".to_string()));
        assert_eq!(var.raw_value(), Some("$(B)\n".to_string()));
        assert_eq!(define_references(text), vec![("B".to_string(), 24..25)]);
    }

    #[test]
    fn test_define_rename_name_with_reference() {
        let makefile: Makefile = "define $(A)_X =\nbody\nendef\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_name("C");
        assert_eq!(var.name(), Some("C".to_string()));
        assert_eq!(makefile.code(), "define C =\nbody\nendef\n");
    }

    #[test]
    fn test_define_rename_name_with_continuation() {
        let code = "define A \\\nB\nbody\nendef\n";
        let makefile: Makefile = code.parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        let range = var.name_range().unwrap();
        assert_eq!(&code[range], "A \\\nB");
        var.set_name("C");
        assert_eq!(var.name(), Some("C".to_string()));
        assert_eq!(makefile.code(), "define C\nbody\nendef\n");
    }

    #[test]
    fn test_variable_definition_set_value() {
        let makefile: Makefile = "VAR = old_value\n".parse().unwrap();

        let mut var = makefile
            .variable_definitions()
            .next()
            .expect("Should have variable");
        assert_eq!(var.raw_value(), Some("old_value".to_string()));

        // Change the value
        var.set_value("new_value");

        // Verify the value changed
        assert_eq!(var.raw_value(), Some("new_value".to_string()));
        assert!(makefile.code().contains("VAR = new_value"));
    }

    #[test]
    fn test_variable_definition_set_value_preserves_format() {
        let makefile: Makefile = "export VAR := old_value\n".parse().unwrap();

        let mut var = makefile
            .variable_definitions()
            .next()
            .expect("Should have variable");
        assert_eq!(var.raw_value(), Some("old_value".to_string()));

        // Change the value
        var.set_value("new_value");

        // Verify the value changed but format preserved
        assert_eq!(var.raw_value(), Some("new_value".to_string()));
        let code = makefile.code();
        assert!(code.contains("export"), "Should preserve export prefix");
        assert!(code.contains(":="), "Should preserve := operator");
        assert!(code.contains("new_value"), "Should have new value");
    }

    /// Set the value of the only variable definition in `text`.
    fn set_value(text: &str, value: &str) -> String {
        let makefile: Makefile = text.parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_value(value);
        assert_eq!(var.raw_value().as_deref().map(str::trim_end), Some(value));
        crate::test_util::assert_matches_reparse(&makefile);
        makefile.code()
    }

    #[test]
    fn test_set_value_empty() {
        assert_eq!(set_value("X =\n", "new"), "X = new\n");
        assert_eq!(set_value("X :=\n", "new"), "X := new\n");
        assert_eq!(set_value("X ?=\n", "new"), "X ?= new\n");
        assert_eq!(set_value("X=\n", "new"), "X= new\n");
        assert_eq!(set_value("X = \n", "new"), "X = new\n");
        assert_eq!(set_value("export X =\n", "new"), "export X = new\n");
        assert_eq!(set_value("a: X =\n", "new"), "a: X = new\n");
        assert_eq!(set_value("X =\r\n", "new"), "X = new\r\n");
        assert_eq!(set_value("X =", "new"), "X = new");
        assert_eq!(set_value("X =\n", ""), "X =\n");
    }

    #[test]
    fn test_set_value_without_operator() {
        assert_eq!(set_value("export X\n", "new"), "export X = new\n");
        assert_eq!(set_value("export X", "new"), "export X = new");
        assert_eq!(set_value("unexport X\n", "new"), "unexport X = new\n");
        assert_eq!(set_value("export X\r\n", "new"), "export X = new\r\n");
        assert_eq!(set_value("export X # c\n", "new"), "export X = new # c\n");
        assert_eq!(set_value("export X\n", ""), "export X =\n");
    }

    #[test]
    fn test_set_value_define_at_end_of_file() {
        // The `define` line is ended before the body.
        for (text, expected) in [
            ("define X", "define X\nnew\nendef\n"),
            ("define X ", "define X \nnew\nendef\n"),
            ("define X =", "define X =\nnew\nendef\n"),
            ("define X # c", "define X # c\nnew\nendef\n"),
            ("define $(A)B", "define $(A)B\nnew\nendef\n"),
            ("define X\\\n", "define X\\\n\nnew\nendef\n"),
            ("define X\n", "define X\nnew\nendef\n"),
        ] {
            let (makefile, _) = Makefile::from_str_relaxed(text);
            let mut var = makefile.variable_definitions().next().unwrap();
            var.set_value("new");
            assert!(var.add_endef().unwrap());
            crate::test_util::assert_matches_reparse(&makefile);
            assert_eq!(makefile.code(), expected);
            assert_eq!(var.raw_value().as_deref(), Some("new\n"));
        }
    }

    #[test]
    fn test_define_name_at_end_of_file() {
        for text in ["define X", "define X ", "define X\\\n"] {
            let (makefile, _) = Makefile::from_str_relaxed(text);
            let var = makefile.variable_definitions().next().unwrap();
            assert_eq!(var.name().as_deref(), Some("X"));
            assert_eq!(var.raw_value().as_deref(), Some(""));
        }
    }

    #[test]
    fn test_try_set_value_without_value() {
        for text in ["undefine X\n", "export X Y\n"] {
            let (makefile, _) = Makefile::from_str_relaxed(text);
            let mut var = makefile.variable_definitions().next().unwrap();
            let error = var.try_set_value("new").unwrap_err();
            assert_eq!(
                error.to_string(),
                format!(
                    "Parse error: Error at line 1: {text:?} has no value to set\n1| set_value\n"
                )
            );
            assert_eq!(makefile.code(), text);
        }
    }

    #[test]
    fn test_set_value_without_operator_continuation() {
        // The rest of the logical line, up to a comment, becomes part of the
        // value, as the parser has it.
        fn set_value_continued(text: &str, value: &str) -> String {
            let makefile: Makefile = text.parse().unwrap();
            let mut var = makefile.variable_definitions().next().unwrap();
            var.set_value(value);
            crate::test_util::assert_matches_reparse(&makefile);
            makefile.code()
        }
        assert_eq!(
            set_value_continued("export X \\\n", "new"),
            "export X = new \\\n"
        );
        assert_eq!(
            set_value_continued("export X\\\n", "new"),
            "export X = new\\\n"
        );
        assert_eq!(
            set_value_continued("export X \\\r\n", "new"),
            "export X = new \\\r\n"
        );
        assert_eq!(
            set_value_continued("export X \\\n\n", "new"),
            "export X = new \\\n\n"
        );
        assert_eq!(
            set_value_continued("export X \\\n  # c\n", "new"),
            "export X = new \\\n  # c\n"
        );
        assert_eq!(
            set_value_continued("unexport X \\\n# c\n", "new"),
            "unexport X = new \\\n# c\n"
        );
        assert_eq!(
            set_value_continued("export X \n", "new"),
            "export X = new \n"
        );
        assert_eq!(set_value_continued("export X \\\n", ""), "export X = \\\n");
        assert_eq!(
            set_value_continued("export X # c\n", ""),
            "export X = # c\n"
        );
    }

    #[test]
    #[should_panic(expected = "has no value to set")]
    fn test_set_value_export_several_continuation() {
        set_value("export X \\\n  Y\n", "new");
    }

    #[test]
    #[should_panic(expected = "has no value to set")]
    fn test_set_value_undefine() {
        set_value("undefine X\n", "new");
    }

    #[test]
    #[should_panic(expected = "has no value to set")]
    fn test_set_value_export_several() {
        set_value("export X Y\n", "new");
    }

    fn keywords(text: &str) -> Vec<Vec<(String, &str)>> {
        let (makefile, _) = Makefile::from_str_relaxed(text);
        makefile
            .variable_definitions()
            .map(|v| {
                v.keyword_ranges()
                    .into_iter()
                    .map(|(keyword, range)| (keyword, &text[range]))
                    .collect()
            })
            .collect()
    }

    fn expected(v: &[&[&'static str]]) -> Vec<Vec<(String, &'static str)>> {
        v.iter()
            .map(|words| words.iter().map(|w| (w.to_string(), *w)).collect())
            .collect()
    }

    #[test]
    fn test_keyword_ranges() {
        assert_eq!(
            keywords(
                "X = 1\nexport Y := 2\noverride  private Z += 3\nunexport A B\nexport\nexport = 4\noverride undefine C\nall: private D = 5\n"
            ),
            expected(&[
                &[],
                &["export"],
                &["override", "private"],
                &["unexport"],
                &["export"],
                &[],
                &["override", "undefine"],
                &["private"],
            ])
        );
    }

    #[test]
    fn test_keyword_ranges_define() {
        assert_eq!(
            keywords(
                "export define A\ndefine B\nendef\n  endef # c\ndefine C =\r\nx\r\nendef\r\ndefine D\n"
            ),
            expected(&[&["export", "define", "endef"], &["define", "endef"], &["define"]])
        );
    }

    #[test]
    fn test_keyword_ranges_continuation() {
        let text = "export \\\n  X = 1\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(
            var.keyword_ranges(),
            vec![(
                "export".to_string(),
                rowan::TextRange::new(0.into(), 6.into())
            )]
        );
    }

    fn range_text(text: &str, range: Option<rowan::TextRange>) -> Option<&str> {
        range.map(|r| &text[r])
    }

    #[test]
    fn test_is_target_specific() {
        let text = "a b: export X += 1\nc:: Y = 2\nZ = 3\n";
        let makefile: Makefile = text.parse().unwrap();
        let vars: Vec<_> = makefile
            .variable_definitions()
            .map(|v| (v.name().unwrap(), v.is_target_specific()))
            .collect();
        assert_eq!(
            vars,
            vec![
                ("X".to_string(), true),
                ("Y".to_string(), true),
                ("Z".to_string(), false)
            ]
        );
    }

    #[test]
    fn test_is_target_specific_conditional_in_rule_body() {
        // GNU make assigns Y globally here, although the conditional is part
        // of the rule.
        let makefile: Makefile = "all:\nifdef X\n\techo\nY = 1\nendif\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.body_items().count(), 1);
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("Y".to_string()));
        assert!(!var.is_target_specific());
    }

    #[test]
    fn test_is_target_specific_bsd_after_sources() {
        let parsed =
            Makefile::parse_with_variant("prog: .USE VAR=value\n", MakefileVariant::BSDMake);
        let var = parsed.tree().variable_definitions().next().unwrap();
        assert!(var.is_target_specific());
    }

    #[test]
    fn test_value_range() {
        let text = "export X := a $(B) # c\nY =\nZ = \\\n  z\nundefine W\n";
        let makefile: Makefile = text.parse().unwrap();
        let ranges: Vec<_> = makefile
            .variable_definitions()
            .map(|v| range_text(text, v.value_range()))
            .collect();
        assert_eq!(
            ranges,
            vec![Some("a $(B) "), Some(""), Some("\\\n  z"), None]
        );
        for var in makefile.variable_definitions() {
            assert_eq!(
                range_text(text, var.value_range()).map(str::to_string),
                var.raw_value()
            );
        }
    }

    #[test]
    fn test_value_range_target_specific() {
        let text = "all: CFLAGS = -O2 # c\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(range_text(text, var.value_range()), Some("-O2 "));
    }

    #[test]
    fn test_value_range_define() {
        let text = "define A =\nx\ny\nendef\ndefine B\nendef\n";
        let makefile: Makefile = text.parse().unwrap();
        let ranges: Vec<_> = makefile
            .variable_definitions()
            .map(|v| v.value_range())
            .collect();
        assert_eq!(
            ranges,
            vec![
                Some(rowan::TextRange::new(11.into(), 15.into())),
                Some(rowan::TextRange::new(30.into(), 30.into()))
            ]
        );
    }

    #[test]
    fn test_value_range_crlf() {
        let text = "X = a \\\r\n b\r\nY = c\r\n";
        let makefile: Makefile = text.parse().unwrap();
        let ranges: Vec<_> = makefile
            .variable_definitions()
            .map(|v| range_text(text, v.value_range()))
            .collect();
        assert_eq!(ranges, vec![Some("a \\\r\n b"), Some("c")]);
    }

    #[test]
    fn test_value_references() {
        let text = "X.$(A) := $(B) $(patsubst %.c,%.o,$(SRCS:.c=.o)) ${C} $$(D) $E\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        let refs: Vec<_> = var
            .value_references()
            .map(|r| &text[r.text_range()])
            .collect();
        assert_eq!(
            refs,
            vec![
                "$(B)",
                "$(patsubst %.c,%.o,$(SRCS:.c=.o))",
                "$(SRCS:.c=.o)",
                "${C}",
                "$E"
            ]
        );
    }

    #[test]
    fn test_value_references_target_specific() {
        let text = "$(T): X = $(Y)\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        let refs: Vec<_> = var
            .value_references()
            .map(|r| &text[r.text_range()])
            .collect();
        assert_eq!(refs, vec!["$(Y)"]);
    }

    #[test]
    fn test_value_references_define_and_undefine() {
        let makefile: Makefile = "define $(A)\n$(B)\nendef\nundefine $(C)\n".parse().unwrap();
        let names: Vec<Vec<_>> = makefile
            .variable_definitions()
            .map(|v| v.value_references().filter_map(|r| r.name()).collect())
            .collect();
        assert_eq!(names, vec![vec!["B".to_string()], vec![]]);
    }

    #[test]
    fn test_trailing_value_whitespace_range() {
        let text = "A = a \t\nB = b\nC = c  # x\nD = $(d )\nE = \\\n\te \nF = \nall: G = g \n";
        let makefile: Makefile = text.parse().unwrap();
        let ranges: Vec<_> = makefile
            .variable_definitions()
            .map(|v| range_text(text, v.trailing_value_whitespace_range()))
            .collect();
        assert_eq!(
            ranges,
            vec![
                Some(" \t"),
                None,
                Some("  "),
                None,
                Some(" "),
                None,
                Some(" ")
            ]
        );
        let offsets: Vec<_> = makefile
            .variable_definitions()
            .filter_map(|v| v.trailing_value_whitespace_range())
            .map(|r| usize::from(r.start()))
            .collect();
        assert_eq!(offsets, vec![5, 19, 43, 60]);
    }

    #[test]
    fn test_trailing_value_whitespace_range_crlf() {
        let text = "A = a \r\nB = b\r\n";
        let makefile: Makefile = text.parse().unwrap();
        let ranges: Vec<_> = makefile
            .variable_definitions()
            .map(|v| range_text(text, v.trailing_value_whitespace_range()))
            .collect();
        assert_eq!(ranges, vec![Some(" "), None]);
    }

    #[test]
    fn test_has_endef() {
        let makefile: Makefile = "define A\nx\nendef\noverride define B\n  endef # c\nC = endef\n"
            .parse()
            .unwrap();
        let has: Vec<_> = makefile
            .variable_definitions()
            .map(|v| v.has_endef())
            .collect();
        assert_eq!(has, vec![true, true, false]);
    }

    #[test]
    fn test_has_endef_nested() {
        let (makefile, _) = Makefile::from_str_relaxed("define A\ndefine B\nx\nendef\n");
        let var = makefile.variable_definitions().next().unwrap();
        assert!(!var.has_endef());
        let makefile: Makefile = "define A\ndefine B\nx\nendef\nendef\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert!(var.has_endef());
    }

    fn add_endef(text: &str) -> (Result<bool, String>, String) {
        let (makefile, _) = Makefile::from_str_relaxed(text);
        let mut var = makefile.variable_definitions().next().unwrap();
        let result = var.add_endef().map_err(|e| e.to_string());
        if result == Ok(true) {
            assert!(var.has_endef());
            crate::test_util::assert_matches_reparse(&makefile);
        }
        (result, makefile.code())
    }

    #[test]
    fn test_add_endef() {
        assert_eq!(
            add_endef("define A\nx\n"),
            (Ok(true), "define A\nx\nendef\n".to_string())
        );
    }

    #[test]
    fn test_add_endef_no_trailing_newline() {
        assert_eq!(
            add_endef("define A\nx"),
            (Ok(true), "define A\nx\nendef\n".to_string())
        );
    }

    #[test]
    fn test_add_endef_empty_body() {
        assert_eq!(
            add_endef("define A\n"),
            (Ok(true), "define A\nendef\n".to_string())
        );
        assert_eq!(
            add_endef("define A # c"),
            (Ok(true), "define A # c\nendef\n".to_string())
        );
    }

    #[test]
    fn test_add_endef_nested() {
        assert_eq!(
            add_endef("define A\n define B\ndefine C\nendef\nx\n"),
            (
                Ok(true),
                "define A\n define B\ndefine C\nendef\nx\nendef\nendef\n".to_string()
            )
        );
        // A line starting with a tab, or a word merely starting with
        // "define", does not open a nested define.
        assert_eq!(
            add_endef("define A\n\tdefine B\ndefined\ndefine=1\n"),
            (
                Ok(true),
                "define A\n\tdefine B\ndefined\ndefine=1\nendef\n".to_string()
            )
        );
    }

    #[test]
    fn test_add_endef_crlf() {
        assert_eq!(
            add_endef("define A\r\ndefine B\r\nx"),
            (
                Ok(true),
                "define A\r\ndefine B\r\nx\r\nendef\r\nendef\r\n".to_string()
            )
        );
    }

    #[test]
    fn test_add_endef_already_closed() {
        assert_eq!(
            add_endef("define A\nx\nendef\n"),
            (Ok(false), "define A\nx\nendef\n".to_string())
        );
    }

    #[test]
    fn test_add_endef_not_define() {
        let (result, code) = add_endef("A = 1\n");
        assert_eq!(code, "A = 1\n");
        assert_eq!(
            result,
            Err(
                "Parse error: Error at line 1: Cannot add endef to a variable that is not a \
                 define block\n1| variable_add_endef\n"
                    .to_string()
            )
        );
    }

    #[test]
    fn test_add_endef_in_conditional() {
        let (makefile, _) = Makefile::from_str_relaxed("ifdef X\ndefine A\nx\nendif\n");
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.add_endef().unwrap());
        assert_eq!(makefile.code(), "ifdef X\ndefine A\nx\nendif\nendef\n");
    }

    #[test]
    fn test_add_endef_after_continuation() {
        // A newline after the backslash would continue the last line onto
        // `endef`, so a blank line ends it first.
        for (text, expected) in [
            ("define A\nx \\\n", "define A\nx \\\n\nendef\n"),
            ("define A\nx \\", "define A\nx \\\n\nendef\n"),
            ("define A\nx \\\\\\", "define A\nx \\\\\\\n\nendef\n"),
            ("define A\nx \\\\", "define A\nx \\\\\nendef\n"),
            ("define A\nx \\\n  ", "define A\nx \\\n  \nendef\n"),
            ("define A\n# c \\", "define A\n# c \\\n\nendef\n"),
            ("define A\r\nx \\\r\n", "define A\r\nx \\\r\n\r\nendef\r\n"),
        ] {
            assert_eq!(
                add_endef(text),
                (Ok(true), expected.to_string()),
                "{text:?}"
            );
        }
    }

    #[test]
    fn test_add_endef_nested_continuation() {
        // Like make, nested defines are found at the start of logical lines.
        for (text, expected) in [
            (
                "define A\nx \\\ndefine B\n",
                "define A\nx \\\ndefine B\nendef\n",
            ),
            (
                "define A\ndefine B \\\nendef\n",
                "define A\ndefine B \\\nendef\nendef\nendef\n",
            ),
            (
                "define A\ndefine\\\n  B\n",
                "define A\ndefine\\\n  B\nendef\nendef\n",
            ),
        ] {
            assert_eq!(
                add_endef(text),
                (Ok(true), expected.to_string()),
                "{text:?}"
            );
        }
    }
}
