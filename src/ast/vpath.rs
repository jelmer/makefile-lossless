//! Accessors for `vpath` directives.

use super::{collapse_continuations, is_continuation};
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
                    if t.kind() == WHITESPACE || is_continuation(&t.clone().into()) {
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

    /// Returns the raw directory-list text (everything after the pattern)
    /// with line continuations collapsed, or `None` if the directive has no
    /// directories.
    pub fn directories_text(&self) -> Option<String> {
        self.syntax()
            .children()
            .find(|c| c.kind() == EXPR)
            .map(|n| collapse_continuations(&n))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lossless::parse;

    fn vpath_of(input: &str) -> Vpath {
        let parsed = parse(input, None);
        assert!(
            parsed.errors.is_empty(),
            "unexpected errors: {:?}",
            parsed.errors
        );
        parsed
            .root()
            .syntax()
            .descendants()
            .find_map(Vpath::cast)
            .expect("no VPATH node")
    }

    #[test]
    fn test_pattern_keyword_only() {
        assert_eq!(vpath_of("vpath\n").pattern(), None);
    }

    #[test]
    fn test_pattern_with_pattern_only() {
        assert_eq!(vpath_of("vpath %.c\n").pattern(), Some("%.c".to_string()));
    }

    #[test]
    fn test_pattern_with_pattern_and_dirs() {
        assert_eq!(
            vpath_of("vpath %.c src:lib\n").pattern(),
            Some("%.c".to_string())
        );
    }

    #[test]
    fn test_directories_text_none_when_keyword_only() {
        assert_eq!(vpath_of("vpath\n").directories_text(), None);
    }

    #[test]
    fn test_directories_text_none_when_pattern_only() {
        assert_eq!(vpath_of("vpath %.c\n").directories_text(), None);
    }

    #[test]
    fn test_directories_text_present() {
        assert_eq!(
            vpath_of("vpath %.c src:lib\n").directories_text(),
            Some("src:lib".to_string())
        );
    }

    #[test]
    fn test_line_continuation() {
        let code = "vpath %.c src \\\n  lib\n";
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(parsed.root().syntax().to_string(), code);
        let vpath = vpath_of(code);
        assert_eq!(vpath.syntax().to_string(), code);
        assert_eq!(vpath.pattern(), Some("%.c".to_string()));
        assert_eq!(vpath.directories_text(), Some("src lib".to_string()));
    }

    #[test]
    fn test_line_continuation_after_pattern() {
        let code = "vpath \\\n  %.c\\\n  src:lib\n";
        let vpath = vpath_of(code);
        assert_eq!(vpath.syntax().to_string(), code);
        assert_eq!(vpath.pattern(), Some("%.c".to_string()));
        assert_eq!(vpath.directories_text(), Some("src:lib".to_string()));
    }
}
