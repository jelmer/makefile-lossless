use crate::lossless::{ArchiveMember, ArchiveMembers};
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
        self.syntax().text().to_string().trim().to_string()
    }
}
