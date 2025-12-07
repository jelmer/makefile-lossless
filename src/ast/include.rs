use super::makefile::MakefileItem;
use crate::lossless::Include;
use crate::SyntaxKind::EXPR;
use rowan::ast::AstNode;

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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lossless::Makefile;

    #[test]
    fn test_include_parent() {
        let makefile: Makefile = "include common.mk\n".parse().unwrap();

        let inc = makefile.includes().next().unwrap();
        let parent = inc.parent();
        // Parent is ROOT node which doesn't cast to MakefileItem
        assert!(parent.is_none());
    }
}
