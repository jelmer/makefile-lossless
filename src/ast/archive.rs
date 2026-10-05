use crate::lossless::{node_text, ArchiveMember, ArchiveMembers};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;

impl ArchiveMembers {
    /// Get the archive name (e.g., "libfoo.a" from "libfoo.a(bar.o)")
    pub fn archive_name(&self) -> Option<String> {
        // Get the first identifier before the opening parenthesis
        for element in self.syntax().children_with_tokens() {
            if let Some(token) = element.as_token() {
                if token.kind() == IDENTIFIER {
                    return Some(token.text().to_string());
                } else if token.kind() == LPAREN {
                    // Reached the opening parenthesis without finding an identifier
                    break;
                }
            }
        }
        None
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
    fn test_archive_member_line_continuation_crlf() {
        let input = "lib(a.o \\\r\n\tb.o): x\r\n";
        let parsed = parse(input, None);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(parsed.root().syntax().to_string(), input);
        assert_eq!(member_lists(&parsed), vec![vec!["a.o", "b.o"]]);
        let rules: Vec<_> = parsed.root().rules().collect();
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["lib(a.o b.o)"]);
    }
}
