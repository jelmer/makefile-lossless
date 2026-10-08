use crate::lossless::{node_text, ArchiveMember, ArchiveMembers};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::Direction;

impl ArchiveMembers {
    /// Get the archive name (e.g., "libfoo.a" from "libfoo.a(bar.o)")
    ///
    /// The name is returned as written, so variable references in it are
    /// not expanded: for `$(LIB)(bar.o)` this is `$(LIB)`.
    pub fn archive_name(&self) -> Option<String> {
        let mut before = self.syntax().siblings_with_tokens(Direction::Prev).skip(1);
        if before.next()?.kind() != LPAREN {
            return None;
        }
        let mut parts: Vec<_> = before
            .take_while(|e| !matches!(e.kind(), WHITESPACE | NEWLINE | INDENT))
            .map(|e| e.to_string())
            .collect();
        if parts.is_empty() {
            return None;
        }
        parts.reverse();
        Some(parts.concat())
    }

    /// Get all member nodes
    pub fn members(&self) -> impl Iterator<Item = ArchiveMember> + '_ {
        self.syntax().children().filter_map(ArchiveMember::cast)
    }

    /// Get all member names as strings
    pub fn member_names(&self) -> Vec<String> {
        self.members().map(|m| m.text()).collect()
    }
}

impl ArchiveMember {
    /// Get the text of this archive member
    pub fn text(&self) -> String {
        node_text(self.syntax()).trim().to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lossless::parse;
    use crate::MakefileVariant;
    use crate::SyntaxKind::ARCHIVE_MEMBERS;

    #[test]
    fn test_archive_member_parsing() {
        // Test basic archive member syntax
        let input = "libfoo.a(bar.o): bar.c\n\tgcc -c bar.c -o bar.o\n\tar r libfoo.a bar.o\n";
        let parsed = parse(input, None);
        assert!(
            parsed.errors.is_empty(),
            "Should parse archive member without errors"
        );

        let makefile = parsed.root();
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 1);

        // Check that the target is recognized as an archive member
        let target_text = rules[0].targets().next().unwrap();
        assert_eq!(target_text, "libfoo.a(bar.o)");
    }

    #[test]
    fn test_archive_member_multiple_members() {
        // Test archive with multiple members
        let input = "libfoo.a(bar.o baz.o): bar.c baz.c\n\tgcc -c bar.c baz.c\n\tar r libfoo.a bar.o baz.o\n";
        let parsed = parse(input, None);
        assert!(
            parsed.errors.is_empty(),
            "Should parse multiple archive members"
        );

        let makefile = parsed.root();
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 1);
    }

    #[test]
    fn test_archive_member_in_dependencies() {
        // Test archive members in dependencies
        let input =
            "program: main.o libfoo.a(bar.o) libfoo.a(baz.o)\n\tgcc -o program main.o libfoo.a\n";
        let parsed = parse(input, None);
        assert!(
            parsed.errors.is_empty(),
            "Should parse archive members in dependencies"
        );

        let makefile = parsed.root();
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 1);
    }

    #[test]
    fn test_archive_member_with_variables() {
        // Test archive members with variable references
        let input = "$(LIB)($(OBJ)): $(SRC)\n\t$(CC) -c $(SRC)\n\t$(AR) r $(LIB) $(OBJ)\n";
        let parsed = parse(input, None);
        // Variable references in archive members should parse without errors
        assert!(
            parsed.errors.is_empty(),
            "Should parse archive members with variables"
        );
    }

    #[test]
    fn test_archive_member_ast_access() {
        // Test that we can access archive member nodes through the AST
        let input = "libtest.a(foo.o bar.o): foo.c bar.c\n\tgcc -c foo.c bar.c\n";
        let parsed = parse(input, None);
        let makefile = parsed.root();

        // Find archive member nodes in the syntax tree
        let archive_member_count = makefile
            .syntax()
            .descendants()
            .filter(|n| n.kind() == ARCHIVE_MEMBERS)
            .count();

        assert!(
            archive_member_count > 0,
            "Should find ARCHIVE_MEMBERS nodes in AST"
        );
    }

    fn member_lists(parsed: &crate::lossless::Parse) -> Vec<Vec<String>> {
        parsed
            .root()
            .syntax()
            .descendants()
            .filter_map(ArchiveMembers::cast)
            .map(|m| m.member_names())
            .collect()
    }

    #[test]
    fn test_archive_member_target_line_continuation() {
        let input = "lib(a.o \\\n b.o): x\n";
        let parsed = parse(input, None);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(parsed.root().syntax().to_string(), input);
        assert_eq!(member_lists(&parsed), vec![vec!["a.o", "b.o"]]);
        let rules: Vec<_> = parsed.root().rules().collect();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["lib(a.o b.o)"]);
        assert_eq!(rules[0].prerequisites().collect::<Vec<_>>(), vec!["x"]);
    }

    #[test]
    fn test_archive_member_prerequisite_line_continuation() {
        let input = "all: lib(a.o \\\n b.o) c\n";
        let parsed = parse(input, None);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(parsed.root().syntax().to_string(), input);
        assert_eq!(member_lists(&parsed), vec![vec!["a.o", "b.o"]]);
        let rules: Vec<_> = parsed.root().rules().collect();
        assert_eq!(rules.len(), 1);
        assert_eq!(
            rules[0].prerequisites().collect::<Vec<_>>(),
            vec!["lib(a.o b.o)", "c"]
        );
    }

    #[test]
    fn test_archive_name() {
        let parsed = parse("lib.a(m.o): x\nall: $(LIB)(a.o b.o) c\n", None);
        assert_eq!(parsed.errors, vec![]);
        let archives: Vec<_> = parsed
            .root()
            .syntax()
            .descendants()
            .filter_map(ArchiveMembers::cast)
            .map(|m| (m.archive_name(), m.member_names()))
            .collect();
        assert_eq!(
            archives,
            vec![
                (Some("lib.a".to_string()), vec!["m.o".to_string()]),
                (
                    Some("$(LIB)".to_string()),
                    vec!["a.o".to_string(), "b.o".to_string()]
                ),
            ]
        );
    }

    #[test]
    fn test_archive_name_with_variable_reference() {
        // Both GNU make and BSD make expand the archive name, so it may
        // contain or consist of variable references.
        let input =
            "$(LIB)(m.o n.o) lib$(V).a(p.o q.o): y\nall: ${LIB}(a.o b.o) lib$(V).a(c.o d.o) e\n";
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::BSDMake),
            Some(MakefileVariant::POSIXMake),
        ] {
            let parsed = parse(input, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?}");
            assert_eq!(parsed.root().syntax().to_string(), input);
            assert_eq!(
                member_lists(&parsed),
                vec![
                    vec!["m.o", "n.o"],
                    vec!["p.o", "q.o"],
                    vec!["a.o", "b.o"],
                    vec!["c.o", "d.o"]
                ],
                "{variant:?}"
            );
            let rules: Vec<_> = parsed.root().rules().collect();
            assert_eq!(rules.len(), 2, "{variant:?}");
            assert_eq!(
                rules[0].targets().collect::<Vec<_>>(),
                vec!["$(LIB)(m.o n.o)", "lib$(V).a(p.o q.o)"],
                "{variant:?}"
            );
            assert_eq!(
                rules[1].prerequisites().collect::<Vec<_>>(),
                vec!["${LIB}(a.o b.o)", "lib$(V).a(c.o d.o)", "e"],
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_archive_member_prerequisite_followed_by_text() {
        // GNU make keeps text after the `)` in the same word, while BSD make
        // ends the word at the `)`.
        let input = "all: lib.a(m.o)x y\n";
        for (variant, expected) in [
            (None, vec!["lib.a(m.o)x", "y"]),
            (Some(MakefileVariant::GNUMake), vec!["lib.a(m.o)x", "y"]),
            (Some(MakefileVariant::BSDMake), vec!["lib.a(m.o)", "x", "y"]),
        ] {
            let parsed = parse(input, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?}");
            assert_eq!(member_lists(&parsed), vec![vec!["m.o"]], "{variant:?}");
            let rules: Vec<_> = parsed.root().rules().collect();
            assert_eq!(
                rules[0].prerequisites().collect::<Vec<_>>(),
                expected,
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_escaped_dollar_before_paren_is_not_archive() {
        let parsed = parse("$$(x): $$(y) z\n", None);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(member_lists(&parsed), Vec::<Vec<String>>::new());
        let rules: Vec<_> = parsed.root().rules().collect();
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["$$(x)"]);
        assert_eq!(
            rules[0].prerequisites().collect::<Vec<_>>(),
            vec!["$$(y)", "z"]
        );
    }

    #[test]
    fn test_word_starting_with_paren_is_not_archive() {
        // GNU make takes no archive name from a word that starts with `(`.
        let parsed = parse(
            "(a(b c)): y\nall: (a(b c))\n",
            Some(MakefileVariant::GNUMake),
        );
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(member_lists(&parsed), Vec::<Vec<String>>::new());
        let rules: Vec<_> = parsed.root().rules().collect();
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["(a(b", "c))"]);
        assert_eq!(
            rules[1].prerequisites().collect::<Vec<_>>(),
            vec!["(a(b", "c))"]
        );
    }

    #[test]
    fn test_archive_member_line_continuation_crlf() {
        let input = "lib(a.o \\\r\n\tb.o): x\r\n";
        let parsed = parse(input, None);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(parsed.root().syntax().to_string(), input);
        assert_eq!(member_lists(&parsed), vec![vec!["a.o", "b.o"]]);
        let rules: Vec<_> = parsed.root().rules().collect();
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["lib(a.o b.o)"]);
    }

    #[test]
    fn test_archive_member_with_reference_inside_word() {
        // GNU make and BSD make split the member list at whitespace only,
        // so a reference is part of the word around it.
        let input = "lib.a(a$(X).o b.o ${Y}c $(A)$(B) $$d): x\nall: lib.a(p$(Z) \\\n q$(W)r)\n";
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::BSDMake),
            Some(MakefileVariant::POSIXMake),
        ] {
            let parsed = parse(input, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?}");
            assert_eq!(parsed.root().syntax().to_string(), input);
            let members: Vec<Vec<(String, String)>> = parsed
                .root()
                .syntax()
                .descendants()
                .filter_map(ArchiveMembers::cast)
                .map(|m| {
                    m.members()
                        .map(|m| (m.text(), format!("{:?}", m.syntax().text_range())))
                        .collect()
                })
                .collect();
            assert_eq!(
                members,
                vec![
                    vec![
                        ("a$(X).o".to_string(), "6..13".to_string()),
                        ("b.o".to_string(), "14..17".to_string()),
                        ("${Y}c".to_string(), "18..23".to_string()),
                        ("$(A)$(B)".to_string(), "24..32".to_string()),
                        ("$$d".to_string(), "33..36".to_string()),
                    ],
                    vec![
                        ("p$(Z)".to_string(), "52..57".to_string()),
                        ("q$(W)r".to_string(), "61..67".to_string()),
                    ],
                ],
                "{variant:?}"
            );
            let rules: Vec<_> = parsed.root().rules().collect();
            assert_eq!(
                rules[0].targets().collect::<Vec<_>>(),
                vec!["lib.a(a$(X).o b.o ${Y}c $(A)$(B) $$d)"],
                "{variant:?}"
            );
        }
    }
}
