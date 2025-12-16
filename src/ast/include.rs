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
}
