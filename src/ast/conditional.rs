use crate::lossless::{
    remove_with_preceding_comments, Conditional, Error, ErrorInfo, MakefileItem, ParseError,
};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::{GreenNodeBuilder, SyntaxNode};

impl Conditional {
    /// Get the parent item of this conditional, if any
    ///
    /// Returns `Some(MakefileItem)` if this conditional has a parent that is a MakefileItem
    /// (e.g., another Conditional for nested conditionals), or `None` if the parent is the root Makefile node.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = r#"ifdef OUTER
    /// ifdef INNER
    /// VAR = value
    /// endif
    /// endif
    /// "#.parse().unwrap();
    ///
    /// let outer = makefile.conditionals().next().unwrap();
    /// let inner = outer.if_items().find_map(|item| {
    ///     if let makefile_lossless::MakefileItem::Conditional(c) = item {
    ///         Some(c)
    ///     } else {
    ///         None
    ///     }
    /// }).unwrap();
    /// // Inner conditional's parent is the outer conditional
    /// assert!(inner.parent().is_some());
    /// ```
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }

    /// Get the type of conditional (ifdef, ifndef, ifeq, ifneq)
    pub fn conditional_type(&self) -> Option<String> {
        self.syntax()
            .children()
            .find(|it| it.kind() == CONDITIONAL_IF)?
            .children_with_tokens()
            .find(|it| it.kind() == IDENTIFIER)
            .map(|it| it.as_token().unwrap().text().to_string())
    }

    /// Get the condition expression
    pub fn condition(&self) -> Option<String> {
        let if_node = self
            .syntax()
            .children()
            .find(|it| it.kind() == CONDITIONAL_IF)?;

        // Find the EXPR node which contains the condition
        let expr_node = if_node.children().find(|it| it.kind() == EXPR)?;

        Some(expr_node.text().to_string().trim().to_string())
    }

    /// Check if this conditional has an else clause
    pub fn has_else(&self) -> bool {
        self.syntax()
            .children()
            .any(|it| it.kind() == CONDITIONAL_ELSE)
    }

    /// Get the body content of the if branch
    pub fn if_body(&self) -> Option<String> {
        let mut body = String::new();
        let mut in_if_body = false;

        for child in self.syntax().children_with_tokens() {
            if child.kind() == CONDITIONAL_IF {
                in_if_body = true;
                continue;
            }
            if child.kind() == CONDITIONAL_ELSE || child.kind() == CONDITIONAL_ENDIF {
                break;
            }
            if in_if_body {
                body.push_str(child.to_string().as_str());
            }
        }

        if body.is_empty() {
            None
        } else {
            Some(body)
        }
    }

    /// Get the body content of the else branch (if it exists)
    pub fn else_body(&self) -> Option<String> {
        if !self.has_else() {
            return None;
        }

        let mut body = String::new();
        let mut in_else_body = false;

        for child in self.syntax().children_with_tokens() {
            if child.kind() == CONDITIONAL_ELSE {
                in_else_body = true;
                continue;
            }
            if child.kind() == CONDITIONAL_ENDIF {
                break;
            }
            if in_else_body {
                body.push_str(child.to_string().as_str());
            }
        }

        if body.is_empty() {
            None
        } else {
            Some(body)
        }
    }

    /// Remove this conditional from the makefile
    pub fn remove(&mut self) -> Result<(), Error> {
        let Some(parent) = self.syntax().parent() else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot remove conditional: no parent node".to_string(),
                    line: 1,
                    context: "conditional_remove".to_string(),
                }],
            }));
        };

        remove_with_preceding_comments(self.syntax(), &parent);

        Ok(())
    }

    /// Remove the conditional directives (ifdef/endif) but keep the body content
    ///
    /// This "unwraps" the conditional, keeping only the if branch content.
    /// Returns an error if the conditional has an else clause.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = r#"ifdef DEBUG
    /// VAR = debug
    /// endif
    /// "#.parse().unwrap();
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// cond.unwrap().unwrap();
    /// // Now makefile contains just "VAR = debug\n"
    /// assert!(makefile.to_string().contains("VAR = debug"));
    /// assert!(!makefile.to_string().contains("ifdef"));
    /// ```
    pub fn unwrap(&mut self) -> Result<(), Error> {
        // Check if there's an else clause
        if self.has_else() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot unwrap conditional with else clause".to_string(),
                    line: 1,
                    context: "conditional_unwrap".to_string(),
                }],
            }));
        }

        let Some(parent) = self.syntax().parent() else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot unwrap conditional: no parent node".to_string(),
                    line: 1,
                    context: "conditional_unwrap".to_string(),
                }],
            }));
        };

        // Collect the body items (everything between CONDITIONAL_IF and CONDITIONAL_ENDIF)
        let body_nodes: Vec<_> = self
            .syntax()
            .children_with_tokens()
            .skip_while(|n| n.kind() != CONDITIONAL_IF)
            .skip(1) // Skip CONDITIONAL_IF itself
            .take_while(|n| n.kind() != CONDITIONAL_ENDIF)
            .collect();

        // Find the position of this conditional in parent
        let conditional_index = self.syntax().index();

        // Replace the entire conditional with just its body items
        parent.splice_children(conditional_index..conditional_index + 1, body_nodes);

        Ok(())
    }

    /// Get all items (rules, variables, includes, nested conditionals) in the if branch
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = r#"ifdef DEBUG
    /// VAR = debug
    /// rule:
    /// 	command
    /// endif
    /// "#.parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let items: Vec<_> = cond.if_items().collect();
    /// assert_eq!(items.len(), 2); // One variable, one rule
    /// ```
    pub fn if_items(&self) -> impl Iterator<Item = MakefileItem> + '_ {
        self.syntax()
            .children()
            .skip_while(|n| n.kind() != CONDITIONAL_IF)
            .skip(1) // Skip the CONDITIONAL_IF itself
            .take_while(|n| n.kind() != CONDITIONAL_ELSE && n.kind() != CONDITIONAL_ENDIF)
            .filter_map(MakefileItem::cast)
    }

    /// Get all items (rules, variables, includes, nested conditionals) in the else branch
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = r#"ifdef DEBUG
    /// VAR = debug
    /// else
    /// VAR = release
    /// endif
    /// "#.parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let items: Vec<_> = cond.else_items().collect();
    /// assert_eq!(items.len(), 1); // One variable in else branch
    /// ```
    pub fn else_items(&self) -> impl Iterator<Item = MakefileItem> + '_ {
        self.syntax()
            .children()
            .skip_while(|n| n.kind() != CONDITIONAL_ELSE)
            .skip(1) // Skip the CONDITIONAL_ELSE itself
            .take_while(|n| n.kind() != CONDITIONAL_ENDIF)
            .filter_map(MakefileItem::cast)
    }

    /// Add an item to the if branch of the conditional
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let mut makefile: Makefile = "ifdef DEBUG\nendif\n".parse().unwrap();
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// let temp: Makefile = "CFLAGS = -g\n".parse().unwrap();
    /// let var = temp.variable_definitions().next().unwrap();
    /// cond.add_if_item(MakefileItem::Variable(var));
    /// assert!(makefile.to_string().contains("CFLAGS = -g"));
    /// ```
    pub fn add_if_item(&mut self, item: MakefileItem) {
        let item_node = item.syntax().clone();

        // Find position after CONDITIONAL_IF
        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|n| n.kind() == CONDITIONAL_IF)
            .map(|p| p + 1)
            .unwrap_or(0);

        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![item_node.into()]);
    }

    /// Add an item to the else branch of the conditional
    ///
    /// If the conditional doesn't have an else branch, this will create one.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let mut makefile: Makefile = "ifdef DEBUG\nVAR=1\nendif\n".parse().unwrap();
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// let temp: Makefile = "CFLAGS = -O2\n".parse().unwrap();
    /// let var = temp.variable_definitions().next().unwrap();
    /// cond.add_else_item(MakefileItem::Variable(var));
    /// assert!(makefile.to_string().contains("else"));
    /// assert!(makefile.to_string().contains("CFLAGS = -O2"));
    /// ```
    pub fn add_else_item(&mut self, item: MakefileItem) {
        // Ensure there's an else clause
        if !self.has_else() {
            self.add_else_clause();
        }

        let item_node = item.syntax().clone();

        // Find position after CONDITIONAL_ELSE
        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|n| n.kind() == CONDITIONAL_ELSE)
            .map(|p| p + 1)
            .unwrap_or(0);

        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![item_node.into()]);
    }

    /// Add an else clause to the conditional if it doesn't already have one
    fn add_else_clause(&mut self) {
        if self.has_else() {
            return;
        }

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(CONDITIONAL_ELSE.into());
        builder.token(IDENTIFIER.into(), "else");
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        // Find position before CONDITIONAL_ENDIF
        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|n| n.kind() == CONDITIONAL_ENDIF)
            .unwrap_or(self.syntax().children_with_tokens().count());

        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![syntax.into()]);
    }
}
