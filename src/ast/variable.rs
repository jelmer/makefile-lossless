use super::makefile::MakefileItem;
use crate::lossless::{remove_with_preceding_comments, VariableDefinition};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::{GreenNodeBuilder, SyntaxNode};

impl VariableDefinition {
    /// Get the name of the variable definition
    pub fn name(&self) -> Option<String> {
        self.syntax().children_with_tokens().find_map(|it| {
            it.as_token().and_then(|it| {
                if it.kind() == IDENTIFIER && it.text() != "export" {
                    Some(it.text().to_string())
                } else {
                    None
                }
            })
        })
    }

    /// Check if this variable definition is exported
    pub fn is_export(&self) -> bool {
        self.syntax()
            .children_with_tokens()
            .any(|it| it.as_token().is_some_and(|token| token.text() == "export"))
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
        self.syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .map(|it| it.text().into())
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
                    // For nodes (like EXPR), rebuild them by iterating their structure
                    builder.start_node(node.kind().into());
                    for node_child in node.children_with_tokens() {
                        if let rowan::NodeOrToken::Token(token) = node_child {
                            builder.token(token.kind().into(), token.text());
                        }
                    }
                    builder.finish_node();
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
        let expr_index = self
            .syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .map(|it| it.index());

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
}
