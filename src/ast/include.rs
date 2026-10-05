use super::bsd::{directive_keyword, keyword_token};
use super::collapse_continuations;
use super::makefile::MakefileItem;
use crate::lossless::{
    remove_with_preceding_comments, Error, ErrorInfo, Include, Lang, ParseError,
};
use crate::SyntaxKind::{EXPR, IDENTIFIER, INCLUDE};
use rowan::ast::AstNode;
use rowan::{GreenNodeBuilder, SyntaxNode, SyntaxToken};

/// Strip the `<...>` or `"..."` delimiters from a BSD make include path.
fn strip_delimiters(path: &str) -> Option<&str> {
    path.strip_prefix('<')
        .and_then(|p| p.strip_suffix('>'))
        .or_else(|| path.strip_prefix('"').and_then(|p| p.strip_suffix('"')))
}

impl Include {
    /// Internal: the token holding the include keyword and the keyword
    /// name without any dot, such as `-include`.
    fn keyword(&self) -> Option<(SyntaxToken<Lang>, String)> {
        let (token, keyword) = keyword_token(self.syntax())?;
        let name = keyword.trim_start_matches('.').to_string();
        Some((token, name))
    }

    /// Whether this is a BSD make `.include` directive.
    fn is_bsd(&self) -> bool {
        directive_keyword(self.syntax()).is_some_and(|k| k.starts_with('.'))
    }

    /// Get the path of the include directive
    ///
    /// For BSD make, the `<...>` or `"..."` delimiters around the path are
    /// removed.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".include <bsd.prog.mk>\n".parse().unwrap();
    /// let inc = makefile.includes().next().unwrap();
    /// assert_eq!(inc.path(), Some("bsd.prog.mk".to_string()));
    /// ```
    pub fn path(&self) -> Option<String> {
        let raw = self.raw_path()?;
        if self.is_bsd() {
            if let Some(inner) = strip_delimiters(&raw) {
                return Some(inner.to_string());
            }
        }
        Some(raw)
    }

    /// The path as written, including any delimiters, with line
    /// continuations collapsed.
    fn raw_path(&self) -> Option<String> {
        self.syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .map(|it| collapse_continuations(&it).trim().to_string())
    }

    /// Get the text range of the path portion of the include directive.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include config.mk\n".parse().unwrap();
    /// let inc = makefile.includes().next().unwrap();
    /// let range = inc.path_range().unwrap();
    /// assert_eq!(&makefile.to_string()[std::ops::Range::from(range)], "config.mk");
    /// ```
    pub fn path_range(&self) -> Option<rowan::TextRange> {
        self.syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .map(|it| it.text_range())
    }

    /// Check if this is an optional include (-include or sinclude)
    ///
    /// For BSD make, `.-include`, `.sinclude` and `.dinclude` are optional.
    pub fn is_optional(&self) -> bool {
        self.keyword()
            .is_some_and(|(_, name)| matches!(name.as_str(), "-include" | "sinclude" | "dinclude"))
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
        // Keep the delimiters of a BSD include.
        let new_path = match self.raw_path() {
            Some(raw) if self.is_bsd() && strip_delimiters(&raw).is_some() => {
                format!("{}{}{}", &raw[..1], new_path, &raw[raw.len() - 1..])
            }
            _ => new_path.to_string(),
        };
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
            builder.token(IDENTIFIER.into(), &new_path);
            builder.finish_node();

            let new_expr = SyntaxNode::new_root_mut(builder.finish());

            // Replace the old EXPR with the new one
            self.syntax()
                .splice_children(expr_idx..expr_idx + 1, vec![new_expr.into()]);
        }
    }

    /// Make this include optional (change "include" to "-include")
    ///
    /// If the include is already optional, this has no effect. For BSD make
    /// this switches between `.include` and `.-include`.
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
        let Some((token, name)) = self.keyword() else {
            return;
        };
        // In the `.include` form the dot is part of the keyword token.
        let dot = if token.text().starts_with('.') {
            "."
        } else {
            ""
        };
        let new_name = match (optional, name.as_str()) {
            (true, "include") => "-include",
            (false, "-include" | "sinclude") => "include",
            _ => return,
        };

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(INCLUDE.into());
        builder.token(IDENTIFIER.into(), &format!("{}{}", dot, new_name));
        builder.finish_node();
        let new_token = SyntaxNode::new_root_mut(builder.finish())
            .first_token()
            .unwrap();
        let index = token.index();
        self.syntax()
            .splice_children(index..index + 1, vec![new_token.into()]);
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
    fn test_include_path_range() {
        let makefile: Makefile = "include config.mk\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        let range = inc.path_range().unwrap();
        assert_eq!(
            &makefile.to_string()[std::ops::Range::from(range)],
            "config.mk"
        );
    }

    #[test]
    fn test_include_path_range_optional() {
        let makefile: Makefile = "-include optional.mk\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        let range = inc.path_range().unwrap();
        assert_eq!(
            &makefile.to_string()[std::ops::Range::from(range)],
            "optional.mk"
        );
    }

    #[test]
    fn test_include_path_range_sinclude() {
        let makefile: Makefile = "sinclude silent.mk\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        let range = inc.path_range().unwrap();
        assert_eq!(
            &makefile.to_string()[std::ops::Range::from(range)],
            "silent.mk"
        );
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

    #[test]
    fn test_set_optional_keeps_variable_references() {
        let makefile: Makefile = "include $(TOP)/config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(true);
        assert_eq!(makefile.to_string(), "-include $(TOP)/config.mk\n");
        inc.set_optional(false);
        assert_eq!(makefile.to_string(), "include $(TOP)/config.mk\n");
    }

    #[test]
    fn test_bsd_set_optional() {
        let makefile: Makefile = ".include <bsd.prog.mk>\n.  include \"x.mk\"\n"
            .parse()
            .unwrap();
        for mut inc in makefile.includes() {
            inc.set_optional(true);
            assert!(inc.is_optional());
        }
        assert_eq!(
            makefile.to_string(),
            ".-include <bsd.prog.mk>\n.  -include \"x.mk\"\n"
        );
        for mut inc in makefile.includes() {
            inc.set_optional(false);
            assert!(!inc.is_optional());
        }
        assert_eq!(
            makefile.to_string(),
            ".include <bsd.prog.mk>\n.  include \"x.mk\"\n"
        );
    }

    #[test]
    fn test_bsd_optional_variants() {
        let makefile: Makefile = ".sinclude <a.mk>\n.dinclude <b.mk>\n.include <c.mk>\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile
                .includes()
                .map(|i| (i.path().unwrap(), i.is_optional()))
                .collect::<Vec<_>>(),
            vec![
                ("a.mk".to_string(), true),
                ("b.mk".to_string(), true),
                ("c.mk".to_string(), false),
            ]
        );
    }

    #[test]
    fn test_bsd_set_path_keeps_delimiters() {
        let makefile: Makefile = ".include <bsd.prog.mk>\n. include \"old.mk\"\n"
            .parse()
            .unwrap();
        for mut inc in makefile.includes() {
            inc.set_path("new.mk");
            assert_eq!(inc.path(), Some("new.mk".to_string()));
        }
        assert_eq!(
            makefile.to_string(),
            ".include <new.mk>\n. include \"new.mk\"\n"
        );
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["new.mk", "new.mk"]
        );
    }

    #[test]
    fn test_include_line_continuation() {
        for (code, keyword_optional) in [
            ("include a.mk \\\n  b.mk\n", false),
            ("-include a.mk \\\n  b.mk\n", true),
            ("sinclude a.mk\\\n\tb.mk\n", true),
        ] {
            let makefile: Makefile = code.parse().unwrap();
            assert_eq!(makefile.to_string(), code);
            let includes: Vec<_> = makefile.includes().collect();
            assert_eq!(includes.len(), 1);
            assert_eq!(includes[0].path(), Some("a.mk b.mk".to_string()));
            assert_eq!(includes[0].is_optional(), keyword_optional);
            assert_eq!(makefile.rules().count(), 0);
        }
    }

    #[test]
    fn test_include_line_continuation_before_path() {
        let code = "include \\\n  a.mk \\\n \\\n  b.mk\nc.mk: d\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["a.mk b.mk"]
        );
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_include_escaped_backslash_not_continuation() {
        let code = "include a.mk\\\\\nb.mk: c\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["a.mk\\\\"]
        );
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["b.mk"]);
    }

    #[test]
    fn test_path_excludes_comment() {
        let makefile: Makefile = "include foo.mk # comment\n.include <bsd.own.mk> # c\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile.includes().map(|i| i.path()).collect::<Vec<_>>(),
            vec![Some("foo.mk".to_string()), Some("bsd.own.mk".to_string())]
        );
        let mut inc = makefile.includes().next().unwrap();
        inc.set_path("bar.mk");
        assert_eq!(
            makefile.to_string(),
            "include bar.mk # comment\n.include <bsd.own.mk> # c\n"
        );
    }
}
