//! Accessors for `vpath` directives.

use crate::lossless::Vpath;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;

impl Vpath {
    /// Returns the pattern argument of the `vpath` directive, if any.
    ///
    /// `vpath` (no args) returns `None`.
    /// `vpath PATTERN`     returns `Some("PATTERN")`.
    /// `vpath PATTERN DIRS` returns `Some("PATTERN")`.
    pub fn pattern(&self) -> Option<String> {
        // Walk tokens: skip the leading `vpath` keyword and whitespace,
        // then collect tokens up to the next whitespace or to the EXPR
        // (directories) node.
        let mut after_keyword = false;
        let mut out = String::new();
        for child in self.syntax().children_with_tokens() {
            match child {
                rowan::NodeOrToken::Token(t) => {
                    if !after_keyword {
                        if t.kind() == IDENTIFIER && t.text() == "vpath" {
                            after_keyword = true;
                        }
                        continue;
                    }
                    if t.kind() == WHITESPACE {
                        if out.is_empty() {
                            continue;
                        } else {
                            break;
                        }
                    }
                    if t.kind() == NEWLINE {
                        break;
                    }
                    out.push_str(t.text());
                }
                rowan::NodeOrToken::Node(_) => {
                    // The EXPR (directories) node marks the end of the
                    // pattern.
                    break;
                }
            }
        }
        if out.is_empty() {
            None
        } else {
            Some(out)
        }
    }

    /// Returns the raw directory-list text (everything after the pattern),
    /// or `None` if the directive has no directories.
    pub fn directories_text(&self) -> Option<String> {
        self.syntax()
            .children()
            .find(|c| c.kind() == EXPR)
            .map(|n| n.text().to_string())
    }
}
