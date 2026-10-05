//! Accessors for lines that consist only of variable references or function
//! calls, such as `$(eval ...)` or `$(info ...)`.

use super::{logical_text, LineSyntax};
use crate::lossless::{lf_line_endings, ExpressionStatement, VariableReference};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;

impl ExpressionStatement {
    /// Returns the references on this line, in order.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let makefile: Makefile = "$(eval $(call gen_rule,foo))\n".parse().unwrap();
    /// let Some(MakefileItem::ExpressionStatement(stmt)) = makefile.items().next() else {
    ///     panic!("expected an expression statement");
    /// };
    /// let names: Vec<_> = stmt.references().map(|r| r.name()).collect();
    /// assert_eq!(names, vec![Some("eval".to_string())]);
    /// ```
    pub fn references(&self) -> impl Iterator<Item = VariableReference> + '_ {
        self.syntax().children().filter_map(VariableReference::cast)
    }

    /// Returns the text of the expression, without trailing whitespace,
    /// comment or newline.
    ///
    /// This is the logical line as GNU make expands it: line continuations
    /// are collapsed into a single space, CRLF line endings converted to LF
    /// and `\#` outside variable references unescaped to `#`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let makefile: Makefile = "$(info a) \\\n  $(info b) # log\n".parse().unwrap();
    /// let Some(MakefileItem::ExpressionStatement(stmt)) = makefile.items().next() else {
    ///     panic!("expected an expression statement");
    /// };
    /// assert_eq!(stmt.expression(), "$(info a) $(info b)");
    /// ```
    pub fn expression(&self) -> String {
        let mut exprs = self.syntax().children().filter(|c| c.kind() == EXPR);
        let Some(first) = exprs.next() else {
            return String::new();
        };
        let range = first
            .text_range()
            .cover(exprs.last().unwrap_or(first).text_range());
        let tokens = self
            .syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| range.contains_range(t.text_range()));
        // Expression statements are specific to GNU make.
        logical_text(self.syntax(), tokens, LineSyntax::Gnu, true)
    }

    /// Returns the text after a `;` following the references, or `None` if
    /// there is no `;`.
    ///
    /// GNU make ignores this text when the references expand to nothing. If
    /// they expand to a rule header such as `foo:`, it is that rule's
    /// recipe instead.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let makefile: Makefile = "$(info a); echo b\n".parse().unwrap();
    /// let Some(MakefileItem::ExpressionStatement(stmt)) = makefile.items().next() else {
    ///     panic!("expected an expression statement");
    /// };
    /// assert_eq!(stmt.expression(), "$(info a)");
    /// assert_eq!(stmt.after_semicolon(), Some("echo b".to_string()));
    /// ```
    pub fn after_semicolon(&self) -> Option<String> {
        let mut tokens = self
            .syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .skip_while(|t| !(t.kind() == OPERATOR && t.text() == ";"));
        tokens.next()?;
        let mut text: String = tokens
            .skip_while(|t| t.kind() == WHITESPACE)
            .map(|t| t.text().to_string())
            .collect();
        for eol in ["\n", "\r"] {
            if let Some(stripped) = text.strip_suffix(eol) {
                text.truncate(stripped.len());
            }
        }
        Some(lf_line_endings(&text))
    }
}

#[cfg(test)]
mod tests {
    use crate::{Makefile, MakefileItem};

    #[test]
    fn test_expression_and_references() {
        let makefile: Makefile = "$(foreach d,$(DIRS),$(eval $(call r,$(d)))) ${X}\n"
            .parse()
            .unwrap();
        let items: Vec<_> = makefile.items().collect();
        assert_eq!(items.len(), 1);
        let MakefileItem::ExpressionStatement(stmt) = &items[0] else {
            panic!("expected an expression statement");
        };
        assert_eq!(
            stmt.expression(),
            "$(foreach d,$(DIRS),$(eval $(call r,$(d)))) ${X}"
        );
        assert_eq!(
            stmt.references().map(|r| r.to_string()).collect::<Vec<_>>(),
            vec!["$(foreach d,$(DIRS),$(eval $(call r,$(d))))", "${X}"]
        );
    }

    fn expression_statement(src: &str) -> crate::lossless::ExpressionStatement {
        let makefile: Makefile = src.parse().unwrap();
        assert_eq!(makefile.to_string(), src);
        let Some(MakefileItem::ExpressionStatement(stmt)) = makefile.items().next() else {
            panic!("expected an expression statement");
        };
        stmt
    }

    #[test]
    fn test_semicolon() {
        let stmt = expression_statement("$(info a) ; echo x # y\n");
        assert_eq!(stmt.expression(), "$(info a)");
        assert_eq!(
            stmt.references().map(|r| r.to_string()).collect::<Vec<_>>(),
            vec!["$(info a)"]
        );
        assert_eq!(stmt.after_semicolon(), Some("echo x # y".to_string()));
    }

    #[test]
    fn test_semicolon_empty() {
        let stmt = expression_statement("$(info a);\n");
        assert_eq!(stmt.after_semicolon(), Some(String::new()));
    }

    #[test]
    fn test_semicolon_continuation() {
        let stmt = expression_statement("$(info a);echo \\\r\n  more\r\n");
        assert_eq!(stmt.after_semicolon(), Some("echo \\\n  more".to_string()));
    }

    #[test]
    fn test_no_semicolon() {
        let stmt = expression_statement("$(info a) # c ; x\n");
        assert_eq!(stmt.after_semicolon(), None);
    }

    #[test]
    fn test_in_conditional() {
        let makefile: Makefile = "ifeq ($(X),y)\n$(error bad)\nendif\n".parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        let items: Vec<_> = cond.if_items().collect();
        assert_eq!(items.len(), 1);
        let MakefileItem::ExpressionStatement(stmt) = &items[0] else {
            panic!("expected an expression statement");
        };
        assert_eq!(stmt.expression(), "$(error bad)");
    }

    fn statement_of(code: &str) -> crate::ExpressionStatement {
        let parsed = Makefile::parse(code);
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        assert_eq!(makefile.to_string(), code);
        let items: Vec<_> = makefile.items().collect();
        assert_eq!(items.len(), 1);
        let MakefileItem::ExpressionStatement(stmt) = &items[0] else {
            panic!("expected an expression statement");
        };
        stmt.clone()
    }

    #[test]
    fn test_expression_continuation_inside_reference() {
        let stmt = statement_of("$(info a \\\n   b) # c\n");
        assert_eq!(stmt.expression(), "$(info a b)");
    }

    #[test]
    fn test_expression_continuation_between_references() {
        let stmt = statement_of("$(info a) \\\n  $(info b) # c\n");
        assert_eq!(stmt.expression(), "$(info a) $(info b)");
        assert_eq!(
            stmt.references().map(|r| r.to_string()).collect::<Vec<_>>(),
            vec!["$(info a)", "$(info b)"]
        );
    }

    #[test]
    fn test_expression_escaped_hash_in_reference() {
        let stmt = statement_of("$(info a\\#b)\n");
        assert_eq!(stmt.expression(), "$(info a\\#b)");
    }
}
