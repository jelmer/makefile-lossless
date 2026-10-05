//! Accessors for lines that consist only of variable references or function
//! calls, such as `$(eval ...)` or `$(info ...)`.

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
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let makefile: Makefile = "$(info a) $(info b) # log\n".parse().unwrap();
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
        let start = first.text_range().start();
        let end = exprs.last().unwrap_or(first).text_range().end();
        let offset = self.syntax().text_range().start();
        lf_line_endings(
            &self
                .syntax()
                .text()
                .slice((start - offset)..(end - offset))
                .to_string(),
        )
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
}
