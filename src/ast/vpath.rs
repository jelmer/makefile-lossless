//! Accessors for `vpath` directives.

use super::{is_continuation, logical_text, LineSyntax};
use crate::lossless::Vpath;
use crate::MakefileVariant;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;

impl Vpath {
    /// Returns the pattern argument of the `vpath` directive, if any.
    ///
    /// `vpath` (no args) returns `None`.
    /// `vpath PATTERN`     returns `Some("PATTERN")`.
    /// `vpath PATTERN DIRS` returns `Some("PATTERN")`.
    ///
    /// `\#` is unescaped as GNU make does.
    pub fn pattern(&self) -> Option<String> {
        // Walk tokens: skip the leading `vpath` keyword and whitespace,
        // then collect tokens up to the next whitespace or to the EXPR
        // (directories) node.
        let mut after_keyword = false;
        let mut tokens = Vec::new();
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
                        if tokens.is_empty() {
                            continue;
                        } else {
                            break;
                        }
                    }
                    if matches!(t.kind(), NEWLINE | COMMENT) {
                        break;
                    }
                    tokens.push(t);
                }
                rowan::NodeOrToken::Node(_) => {
                    // The EXPR (directories) node marks the end of the
                    // pattern.
                    break;
                }
            }
        }
        if tokens.is_empty() {
            None
        } else {
            Some(logical_text(self.syntax(), tokens, LineSyntax::Gnu, true))
        }
    }

    /// Returns the directory-list text (everything after the pattern,
    /// excluding any trailing comment) as GNU make reads it, with line
    /// continuations collapsed and `\#` unescaped, or `None` if the
    /// directive has no directories.
    pub fn directories_text(&self) -> Option<String> {
        self.directories_text_with(LineSyntax::Gnu)
    }

    /// Like [`Self::directories_text`], but as `variant` reads it. Unlike GNU make by default, GNU make
    /// after `.POSIX:` keeps the whitespace before a line continuation;
    /// use [`MakefileVariant::POSIXMake`] for that.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem, MakefileVariant};
    /// let makefile: Makefile = "vpath %.c a \\\n  b\n".parse().unwrap();
    /// let Some(MakefileItem::Vpath(vpath)) = makefile.items().next() else {
    ///     panic!("expected a vpath directive");
    /// };
    /// assert_eq!(
    ///     vpath.directories_text_for(MakefileVariant::GNUMake),
    ///     Some("a b".to_string())
    /// );
    /// assert_eq!(
    ///     vpath.directories_text_for(MakefileVariant::POSIXMake),
    ///     Some("a  b".to_string())
    /// );
    /// ```
    pub fn directories_text_for(&self, variant: MakefileVariant) -> Option<String> {
        self.directories_text_with(variant.into())
    }

    fn directories_text_with(&self, syntax: LineSyntax) -> Option<String> {
        self.syntax()
            .children()
            .find(|c| c.kind() == EXPR)
            .map(|n| {
                let tokens = n.descendants_with_tokens().filter_map(|it| it.into_token());
                logical_text(&n, tokens, syntax, true)
                    .trim_end()
                    .to_string()
            })
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

    #[test]
    fn test_directories_text_excludes_comment() {
        let code = "vpath %.c src lib # comment\n";
        let vpath = vpath_of(code);
        assert_eq!(vpath.syntax().to_string(), code);
        assert_eq!(vpath.pattern(), Some("%.c".to_string()));
        assert_eq!(vpath.directories_text(), Some("src lib".to_string()));
        assert_eq!(
            vpath
                .syntax()
                .children_with_tokens()
                .map(|c| c.kind())
                .collect::<Vec<_>>(),
            vec![
                IDENTIFIER, WHITESPACE, IDENTIFIER, WHITESPACE, EXPR, WHITESPACE, COMMENT, NEWLINE
            ]
        );
    }

    #[test]
    fn test_directories_text_excludes_comment_without_space() {
        assert_eq!(
            vpath_of("vpath %.c src#comment\n").directories_text(),
            Some("src".to_string())
        );
    }

    #[test]
    fn test_directories_text_escaped_hash() {
        assert_eq!(
            vpath_of("vpath %.c a\\#b # comment\n").directories_text(),
            Some("a#b".to_string())
        );
    }

    #[test]
    fn test_pattern_escaped_hash() {
        let vpath = vpath_of("vpath %\\#y.h d\\\\#x\n");
        assert_eq!(vpath.pattern(), Some("%#y.h".to_string()));
        assert_eq!(vpath.directories_text(), Some("d\\".to_string()));
    }

    #[test]
    fn test_directories_text_comment_after_continuation() {
        let code = "vpath %.c src \\\n  lib # comment\n";
        let vpath = vpath_of(code);
        assert_eq!(vpath.syntax().to_string(), code);
        assert_eq!(vpath.directories_text(), Some("src lib".to_string()));
    }

    #[test]
    fn test_comment_on_continued_line() {
        let code = "vpath %.c src \\\n  # comment\n";
        let vpath = vpath_of(code);
        assert_eq!(vpath.syntax().to_string(), code);
        assert_eq!(vpath.directories_text(), Some("src".to_string()));
    }

    #[test]
    fn test_continuation_after_backslashes() {
        // GNU make halves the backslashes before a continuation.
        let vpath = vpath_of("vpath %.c a\\\\\\\n  b\n");
        assert_eq!(vpath.directories_text(), Some("a\\ b".to_string()));
    }

    #[test]
    fn test_pattern_followed_by_comment() {
        let code = "vpath %.c # comment\n";
        let vpath = vpath_of(code);
        assert_eq!(vpath.syntax().to_string(), code);
        assert_eq!(vpath.pattern(), Some("%.c".to_string()));
        assert_eq!(vpath.directories_text(), None);
    }

    #[test]
    fn test_keyword_followed_by_comment() {
        let code = "vpath # comment\n";
        let vpath = vpath_of(code);
        assert_eq!(vpath.syntax().to_string(), code);
        assert_eq!(vpath.pattern(), None);
        assert_eq!(vpath.directories_text(), None);
    }

    #[test]
    fn test_directories_text_for_variant() {
        use crate::MakefileVariant;
        let vpath = vpath_of("vpath %.c $(subst a \\\n  b,c,a  b) \\\n  src\n");
        assert_eq!(
            vpath.directories_text(),
            Some("$(subst a b,c,a  b) src".to_string())
        );
        assert_eq!(
            vpath.directories_text_for(MakefileVariant::GNUMake),
            Some("$(subst a b,c,a  b) src".to_string())
        );
        assert_eq!(
            vpath.directories_text_for(MakefileVariant::POSIXMake),
            Some("$(subst a  b,c,a  b)  src".to_string())
        );
    }
}
