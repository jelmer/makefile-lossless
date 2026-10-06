//! Accessors for `vpath` directives.

use super::{is_continuation, logical_text, LineSyntax};
use crate::lossless::{SyntaxElement, Vpath};
use crate::MakefileVariant;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;

impl Vpath {
    /// The source range of the `vpath` keyword.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem, TextRange};
    /// let makefile: Makefile = "vpath %.c src\n".parse().unwrap();
    /// let Some(MakefileItem::Vpath(vpath)) = makefile.items().next() else { panic!() };
    /// assert_eq!(vpath.keyword_range(), Some(TextRange::new(0.into(), 5.into())));
    /// ```
    pub fn keyword_range(&self) -> Option<rowan::TextRange> {
        super::bsd::keyword_range(self.syntax())
    }

    /// Returns the pattern argument of the `vpath` directive, if any.
    ///
    /// `vpath` (no args) returns `None`.
    /// `vpath PATTERN`     returns `Some("PATTERN")`.
    /// `vpath PATTERN DIRS` returns `Some("PATTERN")`.
    ///
    /// `\#` is unescaped as GNU make does.
    pub fn pattern(&self) -> Option<String> {
        let elements = self.pattern_elements();
        if elements.is_empty() {
            return None;
        }
        let tokens = elements.into_iter().flat_map(|it| match it {
            rowan::NodeOrToken::Token(t) => vec![t],
            rowan::NodeOrToken::Node(n) => n
                .descendants_with_tokens()
                .filter_map(|it| it.into_token())
                .collect(),
        });
        Some(logical_text(self.syntax(), tokens, LineSyntax::Gnu, true))
    }

    /// The tokens and variable reference nodes making up the pattern: those
    /// after the `vpath` keyword up to the next whitespace.
    fn pattern_elements(&self) -> Vec<SyntaxElement> {
        self.syntax()
            .children_with_tokens()
            .skip_while(|it| !(it.kind() == IDENTIFIER && it.to_string() == "vpath"))
            .skip(1)
            .skip_while(|it| it.kind() == WHITESPACE || is_continuation(it))
            .take_while(|it| {
                !matches!(it.kind(), WHITESPACE | NEWLINE | COMMENT) && !is_continuation(it)
            })
            .collect()
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
        let pattern_end = self.pattern_elements().last()?.index();
        self.syntax()
            .children()
            .find(|c| c.kind() == EXPR && c.index() > pattern_end)
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

    fn references(input: &str) -> Vec<(String, Option<String>, std::ops::Range<u32>)> {
        let makefile = parse(input, None).root();
        assert_eq!(makefile.syntax().to_string(), input);
        makefile
            .variable_references()
            .map(|r| {
                let range = r.syntax().text_range();
                (
                    r.syntax().to_string(),
                    r.name(),
                    range.start().into()..range.end().into(),
                )
            })
            .collect()
    }

    fn reference(
        text: &str,
        name: &str,
        range: std::ops::Range<u32>,
    ) -> (String, Option<String>, std::ops::Range<u32>) {
        (text.to_string(), Some(name.to_string()), range)
    }

    #[test]
    fn test_references_in_directories() {
        let code = "vpath %.c $(A) $(B)\n";
        assert_eq!(
            references(code),
            vec![
                reference("$(A)", "A", 10..14),
                reference("$(B)", "B", 15..19)
            ]
        );
        let vpath = vpath_of(code);
        assert_eq!(vpath.pattern(), Some("%.c".to_string()));
        assert_eq!(vpath.directories_text(), Some("$(A) $(B)".to_string()));
    }

    #[test]
    fn test_reference_in_pattern() {
        let code = "vpath $(P) dir\n";
        assert_eq!(references(code), vec![reference("$(P)", "P", 6..10)]);
        let vpath = vpath_of(code);
        assert_eq!(vpath.pattern(), Some("$(P)".to_string()));
        assert_eq!(vpath.directories_text(), Some("dir".to_string()));
    }

    #[test]
    fn test_references_joined_by_colon() {
        let code = "vpath %.h $(INC):$(OTHER)\n";
        assert_eq!(
            references(code),
            vec![
                reference("$(INC)", "INC", 10..16),
                reference("$(OTHER)", "OTHER", 17..25)
            ]
        );
        assert_eq!(
            vpath_of(code).directories_text(),
            Some("$(INC):$(OTHER)".to_string())
        );
    }

    #[test]
    fn test_references_in_pattern_and_directories() {
        let code = "vpath ${P} $(D)/sub\n";
        assert_eq!(
            references(code),
            vec![
                reference("${P}", "P", 6..10),
                reference("$(D)", "D", 11..15)
            ]
        );
        let vpath = vpath_of(code);
        assert_eq!(vpath.pattern(), Some("${P}".to_string()));
        assert_eq!(vpath.directories_text(), Some("$(D)/sub".to_string()));
    }

    #[test]
    fn test_reference_as_only_pattern() {
        let code = "vpath $(P)\n";
        assert_eq!(references(code), vec![reference("$(P)", "P", 6..10)]);
        let vpath = vpath_of(code);
        assert_eq!(vpath.pattern(), Some("$(P)".to_string()));
        assert_eq!(vpath.directories_text(), None);
    }

    #[test]
    fn test_nested_references() {
        let code = "vpath %$(S) $(addprefix $(R)/,a b) # c\n";
        assert_eq!(
            references(code),
            vec![
                reference("$(S)", "S", 7..11),
                reference("$(addprefix $(R)/,a b)", "addprefix", 12..34),
                reference("$(R)", "R", 24..28),
            ]
        );
        let vpath = vpath_of(code);
        assert_eq!(vpath.pattern(), Some("%$(S)".to_string()));
        assert_eq!(
            vpath.directories_text(),
            Some("$(addprefix $(R)/,a b)".to_string())
        );
    }

    #[test]
    fn test_references_in_vpath_variable() {
        assert_eq!(
            references("VPATH = $(A) $(B)\n"),
            vec![
                reference("$(A)", "A", 8..12),
                reference("$(B)", "B", 13..17)
            ]
        );
    }

    #[test]
    fn test_reference_tree() {
        let vpath = vpath_of("vpath $(P) $(D)\n");
        assert_eq!(
            vpath
                .syntax()
                .children_with_tokens()
                .map(|c| c.kind())
                .collect::<Vec<_>>(),
            vec![IDENTIFIER, WHITESPACE, EXPR, WHITESPACE, EXPR, NEWLINE]
        );
        let dirs = vpath.syntax().children().nth(1).unwrap();
        assert_eq!(
            dirs.children_with_tokens()
                .map(|c| c.kind())
                .collect::<Vec<_>>(),
            vec![EXPR]
        );
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

    #[test]
    fn test_keyword_range() {
        let text = "ifdef X\n  vpath\nendif\nvpath %.c \\\n src\n";
        let makefile: crate::Makefile = text.parse().unwrap();
        let ranges: Vec<_> = makefile
            .syntax()
            .descendants()
            .filter_map(Vpath::cast)
            .map(|v| v.keyword_range())
            .collect();
        assert_eq!(
            ranges,
            vec![
                Some(rowan::TextRange::new(10.into(), 15.into())),
                Some(rowan::TextRange::new(22.into(), 27.into())),
            ]
        );
    }
}
