use super::makefile::MakefileItem;
use crate::lossless::{remove_with_preceding_comments, Error, ErrorInfo, Include, ParseError};
use crate::SyntaxKind::{EXPR, IDENTIFIER};
use rowan::ast::AstNode;
use rowan::{GreenNodeBuilder, SyntaxNode};

impl Include {
    /// Get the raw path of the include directive
    pub fn path(&self) -> Option<String> {
        self.syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .map(|it| it.text().to_string().trim().to_string())
    }

    /// Check if this is an optional include (-include or sinclude)
    pub fn is_optional(&self) -> bool {
        let text = self.syntax().text();
        text.to_string().starts_with("-include") || text.to_string().starts_with("sinclude")
    }

    /// Get the parent item of this include directive, if any
    ///
    /// Returns `Some(MakefileItem)` if this include has a parent that is a MakefileItem
    /// (e.g., a Conditional), or `None` if the parent is the root Makefile node.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = r#"ifdef DEBUG
    /// include debug.mk
    /// endif
    /// "#.parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let inc = cond.if_items().next().unwrap();
    /// // Include's parent is the conditional
    /// assert!(matches!(inc, makefile_lossless::MakefileItem::Include(_)));
    /// ```
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }

    /// Remove this include directive from the makefile
    ///
    /// This will also remove any preceding comments.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "include config.mk\nVAR = value\n".parse().unwrap();
    /// let mut inc = makefile.includes().next().unwrap();
    /// inc.remove().unwrap();
    /// assert_eq!(makefile.includes().count(), 0);
    /// ```
    pub fn remove(&mut self) -> Result<(), Error> {
        let Some(parent) = self.syntax().parent() else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot remove include: no parent node".to_string(),
                    line: 1,
                    context: "include_remove".to_string(),
                }],
            }));
        };

        remove_with_preceding_comments(self.syntax(), &parent);
        Ok(())
    }

    /// Set the path of this include directive
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "include old.mk\n".parse().unwrap();
    /// let mut inc = makefile.includes().next().unwrap();
    /// inc.set_path("new.mk");
    /// assert_eq!(inc.path(), Some("new.mk".to_string()));
    /// assert_eq!(makefile.to_string(), "include new.mk\n");
    /// ```
    pub fn set_path(&mut self, new_path: &str) {
        // Find the EXPR node containing the path
        let expr_index = self
            .syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .map(|it| it.index());

        if let Some(expr_idx) = expr_index {
            // Build a new EXPR node with the new path
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(EXPR.into());
            builder.token(IDENTIFIER.into(), new_path);
            builder.finish_node();

            let new_expr = SyntaxNode::new_root_mut(builder.finish());

            // Replace the old EXPR with the new one
            self.syntax()
                .splice_children(expr_idx..expr_idx + 1, vec![new_expr.into()]);
        }
    }

    /// Make this include optional (change "include" to "-include")
    ///
    /// If the include is already optional, this has no effect.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "include config.mk\n".parse().unwrap();
    /// let mut inc = makefile.includes().next().unwrap();
    /// inc.set_optional(true);
    /// assert!(inc.is_optional());
    /// assert_eq!(makefile.to_string(), "-include config.mk\n");
    /// ```
    pub fn set_optional(&mut self, optional: bool) {
        use crate::SyntaxKind::INCLUDE;

        // Find the first IDENTIFIER token (which is the include keyword)
        let keyword_token = self.syntax().children_with_tokens().find(|it| {
            it.as_token()
                .map(|t| t.kind() == IDENTIFIER)
                .unwrap_or(false)
        });

        if let Some(token_element) = keyword_token {
            let token = token_element.as_token().unwrap();
            let current_text = token.text();

            let new_keyword = if optional {
                // Make it optional
                if current_text == "include" {
                    "-include"
                } else if current_text == "sinclude" || current_text == "-include" {
                    // Already optional, no change needed
                    return;
                } else {
                    // Shouldn't happen, but handle gracefully
                    return;
                }
            } else {
                // Make it non-optional
                if current_text == "-include" || current_text == "sinclude" {
                    "include"
                } else if current_text == "include" {
                    // Already non-optional, no change needed
                    return;
                } else {
                    // Shouldn't happen, but handle gracefully
                    return;
                }
            };

            // Rebuild the entire INCLUDE node, replacing just the keyword token
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(INCLUDE.into());

            for child in self.syntax().children_with_tokens() {
                match child {
                    rowan::NodeOrToken::Token(tok)
                        if tok.kind() == IDENTIFIER && tok.text() == current_text =>
                    {
                        // Replace the include keyword
                        builder.token(IDENTIFIER.into(), new_keyword);
                    }
                    rowan::NodeOrToken::Token(tok) => {
                        // Copy other tokens as-is
                        builder.token(tok.kind().into(), tok.text());
                    }
                    rowan::NodeOrToken::Node(node) => {
                        // For nodes (like EXPR), rebuild them
                        builder.start_node(node.kind().into());
                        for node_child in node.children_with_tokens() {
                            if let rowan::NodeOrToken::Token(tok) = node_child {
                                builder.token(tok.kind().into(), tok.text());
                            }
                        }
                        builder.finish_node();
                    }
                }
            }

            builder.finish_node();
            let new_include = SyntaxNode::new_root_mut(builder.finish());

            // Replace the old INCLUDE node with the new one
            let index = self.syntax().index();
            if let Some(parent) = self.syntax().parent() {
                parent.splice_children(index..index + 1, vec![new_include.clone().into()]);

                // Update self to point to the new node
                *self = Include::cast(
                    parent
                        .children_with_tokens()
                        .nth(index)
                        .and_then(|it| it.into_node())
                        .unwrap(),
                )
                .unwrap();
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::lossless::Makefile;

    #[test]
    fn test_include_parent() {
        let makefile: Makefile = "include common.mk\n".parse().unwrap();

        let inc = makefile.includes().next().unwrap();
        let parent = inc.parent();
        // Parent is ROOT node which doesn't cast to MakefileItem
        assert!(parent.is_none());
    }

    #[test]
    fn test_add_include() {
        let mut makefile = Makefile::new();
        makefile.add_include("config.mk");

        let includes: Vec<_> = makefile.includes().collect();
        assert_eq!(includes.len(), 1);
        assert_eq!(includes[0].path(), Some("config.mk".to_string()));

        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["config.mk"]);

        // Check the generated text
        assert_eq!(makefile.to_string(), "include config.mk\n");
    }

    #[test]
    fn test_add_include_to_existing() {
        let mut makefile: Makefile = "VAR = value\nrule:\n\tcommand\n".parse().unwrap();
        makefile.add_include("config.mk");

        // Include should be added at the beginning
        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["config.mk"]);

        // Check that the include comes first
        let text = makefile.to_string();
        assert!(text.starts_with("include config.mk\n"));
        assert!(text.contains("VAR = value"));
    }

    #[test]
    fn test_insert_include() {
        let mut makefile: Makefile = "VAR = value\nrule:\n\tcommand\n".parse().unwrap();
        makefile.insert_include(1, "config.mk").unwrap();

        let items: Vec<_> = makefile.items().collect();
        assert_eq!(items.len(), 3);

        // Check the middle item is the include
        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["config.mk"]);
    }

    #[test]
    fn test_insert_include_at_beginning() {
        let mut makefile: Makefile = "VAR = value\n".parse().unwrap();
        makefile.insert_include(0, "config.mk").unwrap();

        let text = makefile.to_string();
        assert!(text.starts_with("include config.mk\n"));
    }

    #[test]
    fn test_insert_include_at_end() {
        let mut makefile: Makefile = "VAR = value\n".parse().unwrap();
        let item_count = makefile.items().count();
        makefile.insert_include(item_count, "config.mk").unwrap();

        let text = makefile.to_string();
        assert!(text.ends_with("include config.mk\n"));
    }

    #[test]
    fn test_insert_include_out_of_bounds() {
        let mut makefile: Makefile = "VAR = value\n".parse().unwrap();
        let result = makefile.insert_include(100, "config.mk");
        assert!(result.is_err());
    }

    #[test]
    fn test_insert_include_after() {
        let mut makefile: Makefile = "VAR1 = value1\nVAR2 = value2\n".parse().unwrap();
        let first_var = makefile.items().next().unwrap();
        makefile
            .insert_include_after(&first_var, "config.mk")
            .unwrap();

        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["config.mk"]);

        // Check that the include is after VAR1
        let text = makefile.to_string();
        let var1_pos = text.find("VAR1").unwrap();
        let include_pos = text.find("include config.mk").unwrap();
        assert!(include_pos > var1_pos);
    }

    #[test]
    fn test_insert_include_after_with_rule() {
        let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
        let first_rule_item = makefile.items().next().unwrap();
        makefile
            .insert_include_after(&first_rule_item, "config.mk")
            .unwrap();

        let text = makefile.to_string();
        let rule1_pos = text.find("rule1:").unwrap();
        let include_pos = text.find("include config.mk").unwrap();
        let rule2_pos = text.find("rule2:").unwrap();

        // Include should be between rule1 and rule2
        assert!(include_pos > rule1_pos);
        assert!(include_pos < rule2_pos);
    }

    #[test]
    fn test_include_remove() {
        let makefile: Makefile = "include config.mk\nVAR = value\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.remove().unwrap();

        assert_eq!(makefile.includes().count(), 0);
        assert_eq!(makefile.to_string(), "VAR = value\n");
    }

    #[test]
    fn test_include_remove_multiple() {
        let makefile: Makefile = "include first.mk\ninclude second.mk\nVAR = value\n"
            .parse()
            .unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.remove().unwrap();

        assert_eq!(makefile.includes().count(), 1);
        let remaining = makefile.includes().next().unwrap();
        assert_eq!(remaining.path(), Some("second.mk".to_string()));
    }

    #[test]
    fn test_include_set_path() {
        let makefile: Makefile = "include old.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_path("new.mk");

        assert_eq!(inc.path(), Some("new.mk".to_string()));
        assert_eq!(makefile.to_string(), "include new.mk\n");
    }

    #[test]
    fn test_include_set_path_preserves_optional() {
        let makefile: Makefile = "-include old.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_path("new.mk");

        assert_eq!(inc.path(), Some("new.mk".to_string()));
        assert!(inc.is_optional());
        assert_eq!(makefile.to_string(), "-include new.mk\n");
    }

    #[test]
    fn test_include_set_optional_true() {
        let makefile: Makefile = "include config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(true);

        assert!(inc.is_optional());
        assert_eq!(makefile.to_string(), "-include config.mk\n");
    }

    #[test]
    fn test_include_set_optional_false() {
        let makefile: Makefile = "-include config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(false);

        assert!(!inc.is_optional());
        assert_eq!(makefile.to_string(), "include config.mk\n");
    }

    #[test]
    fn test_include_set_optional_from_sinclude() {
        let makefile: Makefile = "sinclude config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(false);

        assert!(!inc.is_optional());
        assert_eq!(makefile.to_string(), "include config.mk\n");
    }

    #[test]
    fn test_include_set_optional_already_optional() {
        let makefile: Makefile = "-include config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(true);

        // Should remain unchanged
        assert!(inc.is_optional());
        assert_eq!(makefile.to_string(), "-include config.mk\n");
    }

    #[test]
    fn test_include_set_optional_already_non_optional() {
        let makefile: Makefile = "include config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(false);

        // Should remain unchanged
        assert!(!inc.is_optional());
        assert_eq!(makefile.to_string(), "include config.mk\n");
    }

    #[test]
    fn test_include_combined_operations() {
        let makefile: Makefile = "include old.mk\nVAR = value\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();

        // Change path and make optional
        inc.set_path("new.mk");
        inc.set_optional(true);

        assert_eq!(inc.path(), Some("new.mk".to_string()));
        assert!(inc.is_optional());
        assert_eq!(makefile.to_string(), "-include new.mk\nVAR = value\n");
    }

    #[test]
    fn test_include_with_comment() {
        let makefile: Makefile = "# Comment\ninclude config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.remove().unwrap();

        // Comment should also be removed
        assert_eq!(makefile.includes().count(), 0);
        assert!(!makefile.to_string().contains("# Comment"));
    }
}
