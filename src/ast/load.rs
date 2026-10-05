//! Accessors for GNU make `load` directives.

use super::is_continuation;
use super::makefile::MakefileItem;
use crate::lossless::{node_text, Load};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;

impl Load {
    /// The unexpanded words naming the objects to load.
    ///
    /// An entry point given in parentheses after an object, as in
    /// `foo.so(init)`, is kept as part of its word, since a word may only
    /// gain one after expansion.
    ///
    /// # Example
    /// ```
    /// use makefile_edit::{Makefile, MakefileItem};
    /// let makefile: Makefile = "load foo.so ./bar.so(init) $(OBJ)\n".parse().unwrap();
    /// let Some(MakefileItem::Load(load)) = makefile.items().next() else {
    ///     panic!("expected a load directive");
    /// };
    /// assert_eq!(load.objects(), vec!["foo.so", "./bar.so(init)", "$(OBJ)"]);
    /// ```
    pub fn objects(&self) -> Vec<String> {
        let Some(expr) = self.syntax().children().find(|it| it.kind() == EXPR) else {
            return vec![];
        };
        let mut objects = vec![];
        let mut word = String::new();
        for element in expr.children_with_tokens() {
            match element {
                rowan::NodeOrToken::Node(node) => word.push_str(&node_text(&node)),
                rowan::NodeOrToken::Token(token)
                    if token.kind() == WHITESPACE || is_continuation(&token.clone().into()) =>
                {
                    if !word.is_empty() {
                        objects.push(std::mem::take(&mut word));
                    }
                }
                rowan::NodeOrToken::Token(token) => word.push_str(token.text()),
            }
        }
        if !word.is_empty() {
            objects.push(word);
        }
        objects
    }

    /// Whether this is a `-load` directive, for which make ignores objects
    /// that fail to load.
    pub fn is_optional(&self) -> bool {
        self.syntax()
            .first_token()
            .is_some_and(|t| t.text() == "-load")
    }

    /// Get the parent item of this directive, if any.
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Load, Makefile, MakefileItem, MakefileVariant};

    fn parse_load(text: &str) -> Load {
        let parsed = Makefile::parse(text);
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        assert_eq!(makefile.to_string(), text);
        let Some(MakefileItem::Load(load)) = makefile.items().next() else {
            panic!("expected a load directive in {text:?}");
        };
        load
    }

    #[test]
    fn test_load() {
        let load = parse_load("load foo.so\n");
        assert_eq!(load.objects(), vec!["foo.so"]);
        assert!(!load.is_optional());
    }

    #[test]
    fn test_load_entry_point() {
        let load = parse_load("load ./bar.so(init_func)\n");
        assert_eq!(load.objects(), vec!["./bar.so(init_func)"]);
    }

    #[test]
    fn test_optional_load() {
        let load = parse_load("-load optional.so\n");
        assert_eq!(load.objects(), vec!["optional.so"]);
        assert!(load.is_optional());
    }

    #[test]
    fn test_load_multiple() {
        let load = parse_load("load a.so  b.so # comment\n");
        assert_eq!(load.objects(), vec!["a.so", "b.so"]);
    }

    #[test]
    fn test_load_continuation() {
        let load = parse_load("load a.so\\\n  b.so\\\r\n\tc.so\r\n");
        assert_eq!(load.objects(), vec!["a.so", "b.so", "c.so"]);
    }

    #[test]
    fn test_load_reference() {
        let load = parse_load("load $(DIR)/$(call obj, x).so\n");
        assert_eq!(load.objects(), vec!["$(DIR)/$(call obj, x).so"]);
    }

    #[test]
    fn test_load_without_objects() {
        // GNU make accepts this as a no-op.
        assert_eq!(parse_load("load\n").objects(), Vec::<String>::new());
        assert_eq!(parse_load("load # none\n").objects(), Vec::<String>::new());
    }

    #[test]
    fn test_load_in_conditional() {
        let makefile: Makefile = "ifdef X\nload foo.so\nendif\n".parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        let Some(MakefileItem::Load(load)) = cond.if_items().next() else {
            panic!("expected a load directive");
        };
        assert_eq!(load.objects(), vec!["foo.so"]);
        assert!(matches!(load.parent(), Some(MakefileItem::Conditional(_))));
    }

    #[test]
    fn test_load_after_rule() {
        let makefile: Makefile = "all: x\n\techo\nload foo.so\n".parse().unwrap();
        let items: Vec<_> = makefile.items().collect();
        assert_eq!(items.len(), 2);
        assert!(matches!(items[1], MakefileItem::Load(_)));
    }

    #[test]
    fn test_load_as_rule_or_variable() {
        let makefile: Makefile = "load:\n\techo\nload = x\n-load: y\n".parse().unwrap();
        assert_eq!(makefile.to_string(), "load:\n\techo\nload = x\n-load: y\n");
        assert_eq!(
            makefile
                .rules()
                .map(|r| r.targets().collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![vec!["load"], vec!["-load"]]
        );
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("load".to_string()));
        assert_eq!(var.raw_value(), Some("x".to_string()));
        assert_eq!(makefile.items().count(), 3);
    }

    #[test]
    fn test_load_variants() {
        let parsed = Makefile::parse_with_variant("load foo.so\n", MakefileVariant::GNUMake);
        assert_eq!(parsed.errors(), &[]);
        assert!(matches!(
            parsed.tree().items().next(),
            Some(MakefileItem::Load(_))
        ));
        // Only GNU make supports `load`; the others report an invalid line.
        for variant in [
            MakefileVariant::BSDMake,
            MakefileVariant::POSIXMake,
            MakefileVariant::NMake,
        ] {
            let parsed = Makefile::parse_with_variant("load foo.so\n", variant);
            assert_ne!(parsed.errors(), &[], "{variant:?}");
            assert!(
                !parsed
                    .tree()
                    .items()
                    .any(|i| matches!(i, MakefileItem::Load(_))),
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_load_as_rule_in_other_variants() {
        for variant in [MakefileVariant::POSIXMake, MakefileVariant::NMake] {
            let parsed = Makefile::parse_with_variant("load : x\n", variant);
            assert_eq!(parsed.errors(), &[], "{variant:?}");
            let makefile = parsed.tree();
            assert_eq!(makefile.to_string(), "load : x\n");
            assert_eq!(
                makefile
                    .rules()
                    .map(|r| r.targets().collect::<Vec<_>>())
                    .collect::<Vec<_>>(),
                vec![vec!["load"]],
                "{variant:?}"
            );
        }
    }
}
