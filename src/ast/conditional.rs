use super::makefile::MakefileItem;
use crate::lossless::{remove_with_preceding_comments, Conditional, Error, ErrorInfo, ParseError};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::{GreenNodeBuilder, SyntaxNode};

/// Split `s` at the first top-level comma. A comma is "top-level" when it
/// is not inside a `$(...)` / `${...}` group. Returns `None` if no such
/// comma exists.
fn split_top_level_comma(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    let mut paren = 0usize;
    let mut brace = 0usize;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'$' if i + 1 < bytes.len() => {
                let next = bytes[i + 1];
                if next == b'(' {
                    paren += 1;
                    i += 2;
                    continue;
                }
                if next == b'{' {
                    brace += 1;
                    i += 2;
                    continue;
                }
                // $$ or $X — skip both.
                i += 2;
                continue;
            }
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b',' if paren == 0 && brace == 0 => {
                return Some((&s[..i], &s[i + 1..]));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Extract two quoted strings from `s`, in the form `"a" "b"` or `'a' 'b'`.
/// Returns `None` if fewer than two quoted strings are present. Surrounding
/// quote characters are stripped from each result.
fn quoted_pair(s: &str) -> Option<Vec<String>> {
    let mut out = Vec::new();
    let mut iter = s.chars().peekable();
    while iter.peek().is_some() {
        // Skip leading whitespace between args.
        while let Some(&c) = iter.peek() {
            if c.is_ascii_whitespace() {
                iter.next();
            } else {
                break;
            }
        }
        let opener = match iter.next() {
            Some(c @ ('"' | '\'')) => c,
            _ => break,
        };
        let mut buf = String::new();
        for c in iter.by_ref() {
            if c == opener {
                out.push(buf);
                buf = String::new();
                break;
            }
            buf.push(c);
        }
    }
    if out.len() >= 2 {
        Some(out)
    } else {
        None
    }
}

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

    /// For an `ifeq` / `ifneq` conditional, return the two argument
    /// strings (unexpanded). Supports both the `(a,b)` and `"a" "b"`
    /// (or `'a' 'b'`) syntaxes.
    ///
    /// Returns `None` for `ifdef` / `ifndef` (or if the args can't be
    /// recovered).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mf: Makefile = "ifeq ($(A),$(B))\nX = 1\nendif\n".parse().unwrap();
    /// let c = mf.conditionals().next().unwrap();
    /// assert_eq!(c.ifeq_args(), Some(("$(A)".to_string(), "$(B)".to_string())));
    /// ```
    pub fn ifeq_args(&self) -> Option<(String, String)> {
        let if_node = self
            .syntax()
            .children()
            .find(|it| it.kind() == CONDITIONAL_IF)?;
        // Inside CONDITIONAL_IF there is one EXPR node wrapping the args.
        let wrapper = if_node.children().find(|it| it.kind() == EXPR)?;

        let text = wrapper.text().to_string();
        let stripped = text.trim();
        // Form 1: parenthesised — `(a, b)`. Split at the top-level comma,
        // ignoring commas inside nested `$(...)` / `${...}`.
        if let Some(inner) = stripped
            .strip_prefix('(')
            .and_then(|s| s.trim_end().strip_suffix(')'))
        {
            if let Some((a, b)) = split_top_level_comma(inner) {
                return Some((a.trim().to_string(), b.trim().to_string()));
            }
        }

        // Form 2: quoted — `"a" "b"` or `'a' 'b'`.
        let mut parts = quoted_pair(&text)?;
        let b = parts.pop()?;
        let a = parts.pop()?;
        Some((a, b))
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

    /// Add a matching `endif` to close this conditional, if it doesn't already
    /// have one.
    ///
    /// Returns `Ok(true)` if a CONDITIONAL_ENDIF was inserted, `Ok(false)` if
    /// the conditional was already terminated. Returns an error if the
    /// conditional has no recognized opener (e.g. a bare `else`/`endif` that
    /// the parser wrapped in a CONDITIONAL node).
    ///
    /// If the existing body does not end with a newline, one is inserted
    /// before the `endif` so it lands on its own line.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef DEBUG\nVAR = 1\n".parse().unwrap();
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// assert!(cond.add_endif().unwrap());
    /// assert_eq!(makefile.code(), "ifdef DEBUG\nVAR = 1\nendif\n");
    /// ```
    pub fn add_endif(&mut self) -> Result<bool, Error> {
        if self.conditional_type().is_none() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot add endif to conditional with no opener".to_string(),
                    line: 1,
                    context: "conditional_add_endif".to_string(),
                }],
            }));
        }
        if self
            .syntax()
            .children_with_tokens()
            .any(|c| c.kind() == CONDITIONAL_ENDIF)
        {
            return Ok(false);
        }

        // Need a newline before `endif` if the current tail doesn't already end
        // with one.
        let needs_newline = self
            .syntax()
            .last_token()
            .is_none_or(|t| t.kind() != NEWLINE);

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(CONDITIONAL_ENDIF.into());
        if needs_newline {
            builder.token(NEWLINE.into(), "\n");
        }
        builder.token(IDENTIFIER.into(), "endif");
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let endif = SyntaxNode::new_root_mut(builder.finish());
        let count = self.syntax().children_with_tokens().count();
        self.syntax()
            .splice_children(count..count, vec![endif.into()]);

        Ok(true)
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

#[cfg(test)]
mod tests {

    use crate::lossless::Makefile;

    #[test]
    fn test_conditional_parent() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
endif
"#
        .parse()
        .unwrap();

        let cond = makefile.conditionals().next().unwrap();
        let parent = cond.parent();
        // Parent is ROOT node which doesn't cast to MakefileItem
        assert!(parent.is_none());
    }

    #[test]
    fn test_add_endif_to_unterminated() {
        let makefile: Makefile = "ifdef DEBUG\nVAR = 1\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.code(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_already_terminated_noop() {
        let makefile: Makefile = "ifdef DEBUG\nVAR = 1\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(!cond.add_endif().unwrap());
        assert_eq!(makefile.code(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_no_trailing_newline() {
        // Source with no final newline produces a parse error, but the tree
        // is still usable for mutations.
        let parsed = Makefile::parse("ifdef DEBUG\nVAR = 1");
        let makefile = parsed.tree();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.code(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_with_else() {
        let makefile: Makefile = "ifdef DEBUG\nA = 1\nelse\nA = 2\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.code(), "ifdef DEBUG\nA = 1\nelse\nA = 2\nendif\n");
    }

    #[test]
    fn test_add_endif_rejects_bare_else() {
        // A bare `else`/`endif` is wrapped in a Conditional node with no
        // CONDITIONAL_IF, so conditional_type() is None. We refuse to add
        // an `endif` to it — the parser already complains.
        let parsed = Makefile::parse("else\nVAR = 1\n");
        let makefile = parsed.tree();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.conditional_type().is_none());
        assert!(cond.add_endif().is_err());
    }

    #[test]
    fn test_add_endif_preserves_existing_body() {
        let makefile: Makefile = "ifeq ($(X),y)\nA = 1\nB = 2\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.code(), "ifeq ($(X),y)\nA = 1\nB = 2\nendif\n");
    }
}
