use super::makefile::MakefileItem;
use super::{is_continuation, logical_text, LineSyntax};
use crate::lossless::{
    is_sunsh_operator, node_text, remove_with_preceding_comments, scan_recipe_variable_refs,
    RecipeVariableReference, VariableDefinition, ASSIGNMENT_OPERATORS,
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
            // assignment operator.
            let is_define = directive.text() == "define";
            let mut elements: Vec<_> = self
                .after_directive_keywords()
                .take_while(|it| {
                    is_continuation(it)
                        || !(matches!(it.kind(), NEWLINE | COMMENT)
                            || is_define && it.kind() == OPERATOR)
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
    fn value_expr(&self) -> Option<crate::lossless::SyntaxNode> {
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

    /// Iterate `$(VAR)` and `${VAR}` variable references in the body of a
    /// `define` block.
    ///
    /// Like recipes, `define` bodies are stored as raw text, so
    /// [`Makefile::variable_references`](crate::Makefile::variable_references)
    /// does not find references in them. The references are found the same
    /// way as by [`Recipe::variable_references`](crate::Recipe::variable_references),
    /// with ranges in the original source. Returns an empty list if this is
    /// not a `define` block.
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
    /// This will also remove any preceding comments and up to 1 empty line before the variable.
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
    pub fn set_name(&mut self, new_name: &str) {
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
        let Some(expr) = self.value_expr() else {
            return false;
        };

        // Find the last non-comment child. Comments are part of the EXPR but
        // the whitespace we care about precedes them (Make includes that
        // whitespace in the value).
        let last_non_comment = expr
            .children_with_tokens()
            .filter(|c| c.kind() != COMMENT)
            .last();
        let Some(elem) = last_non_comment else {
            return false;
        };
        let Some(token) = elem.into_token() else {
            return false;
        };
        if token.kind() != WHITESPACE {
            return false;
        }

        let idx = token.index();
        expr.splice_children(idx..idx + 1, vec![]);
        true
    }

    /// Update the value of this variable definition while preserving the rest
    /// (export prefix, operator, whitespace, etc.)
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
        // Find the EXPR node containing the value
        let expr_index = self.value_expr().map(|it| it.index());

        if let Some(expr_idx) = expr_index {
            // Build a new EXPR node with the new value
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(EXPR.into());
            builder.token(IDENTIFIER.into(), new_value);
            builder.finish_node();

            let new_expr = SyntaxNode::new_root_mut(builder.finish());

            // Replace the old EXPR with the new one
            self.syntax()
                .splice_children(expr_idx..expr_idx + 1, vec![new_expr.into()]);
        }
    }
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
}
