use super::makefile::MakefileItem;
use crate::lossless::{remove_with_preceding_comments, VariableDefinition};
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

impl VariableDefinition {
    /// Internal: the elements making up the variable's name, i.e. the
    /// adjacent IDENTIFIER tokens and variable reference EXPR nodes following
    /// any directive keywords (`export`/`override`/`define`). Usually a single
    /// IDENTIFIER, but computed names like `obj-$(X)` have several parts.
    /// Single source of truth for [`Self::name`], [`Self::name_range`] and
    /// [`Self::set_name`].
    fn name_elements(&self) -> Vec<crate::lossless::SyntaxElement> {
        self.syntax()
            .children_with_tokens()
            .skip_while(|it| {
                it.kind() == WHITESPACE
                    || it.as_token().is_some_and(|t| {
                        t.kind() == IDENTIFIER
                            && matches!(t.text(), "export" | "override" | "define")
                    })
            })
            .take_while(|it| matches!(it.kind(), IDENTIFIER | EXPR))
            .collect()
    }

    /// Internal: the EXPR node holding the value, i.e. the first EXPR after
    /// the operator, or after the header line of a `define` without one.
    fn value_expr(&self) -> Option<crate::lossless::SyntaxNode> {
        self.syntax()
            .children_with_tokens()
            .skip_while(|it| !matches!(it.kind(), OPERATOR | NEWLINE))
            .filter_map(|it| it.into_node())
            .find(|it| it.kind() == EXPR)
    }

    /// Get the name of the variable definition
    pub fn name(&self) -> Option<String> {
        let elements = self.name_elements();
        if elements.is_empty() {
            return None;
        }
        Some(elements.iter().map(|it| it.to_string()).collect())
    }

    /// The source range covering just the variable's name.
    ///
    /// Excludes any `export`/`override`/`define` prefix, the assignment
    /// operator and the value. Lets callers compute a minimal rename edit
    /// instead of re-rendering the whole definition (and with it the
    /// surrounding whitespace).
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
        let start = elements.first()?.text_range().start();
        let end = elements.last()?.text_range().end();
        Some(rowan::TextRange::new(start, end))
    }

    /// Returns true if this assignment is a `define` ... `endef` block.
    pub fn is_define(&self) -> bool {
        self.syntax().children_with_tokens().any(|it| {
            it.as_token()
                .is_some_and(|t| t.kind() == IDENTIFIER && t.text() == "define")
        })
    }

    /// Check if this variable definition is exported
    pub fn is_export(&self) -> bool {
        self.syntax()
            .children_with_tokens()
            .any(|it| it.as_token().is_some_and(|token| token.text() == "export"))
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
        self.syntax().children_with_tokens().any(|it| {
            it.as_token()
                .is_some_and(|token| token.text() == "override")
        })
    }

    /// Get the assignment operator/flavor used in this variable definition
    ///
    /// Returns the operator as a string: "=", ":=", "::=", ":::=", "+=", "?=", or "!="
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "VAR := value\n".parse().unwrap();
    /// let var = makefile.variable_definitions().next().unwrap();
    /// assert_eq!(var.assignment_operator(), Some(":=".to_string()));
    /// ```
    pub fn assignment_operator(&self) -> Option<String> {
        self.syntax().children_with_tokens().find_map(|it| {
            it.as_token().and_then(|token| {
                if token.kind() == OPERATOR {
                    Some(token.text().to_string())
                } else {
                    None
                }
            })
        })
    }

    /// Get the raw value of the variable definition
    pub fn raw_value(&self) -> Option<String> {
        self.value_expr().map(|it| it.text().into())
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
        // Build a new VARIABLE node, copying all children but replacing the OPERATOR token
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(VARIABLE.into());

        for child in self.syntax().children_with_tokens() {
            match child {
                rowan::NodeOrToken::Token(token) if token.kind() == OPERATOR => {
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
    /// The name is the first IDENTIFIER token that is not a directive
    /// keyword (the same token [`Self::name`] returns). A no-op if the
    /// definition has no such token.
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
    fn test_name_range_computed_name() {
        let text = "export obj-$(X)_y := $(Z)\n";
        let makefile: Makefile = text.parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        let range = var.name_range().unwrap();
        assert_eq!(
            &text[range.start().into()..range.end().into()],
            "obj-$(X)_y"
        );
    }

    #[test]
    fn test_set_name_computed_name() {
        let makefile: Makefile = "export obj-$(X)_y := $(Z)\n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_name("FOO");
        assert_eq!(var.name(), Some("FOO".to_string()));
        assert_eq!(var.raw_value(), Some("$(Z)".to_string()));
        assert_eq!(makefile.code(), "export FOO := $(Z)\n");
    }

    #[test]
    fn test_set_value_computed_name() {
        let makefile: Makefile = "$(X) = a \n".parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.trim_trailing_value_whitespace());
        assert_eq!(var.raw_value(), Some("a".to_string()));
        var.set_value("b");
        assert_eq!(makefile.code(), "$(X) = b\n");
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
}
