//! Parse wrapper type following rust-analyzer's pattern for thread-safe storage in Salsa.

use crate::lossless::{
    Error, ErrorInfo, Lang, Makefile, ParseError, ParseErrorKind, PositionedParseError, Rule,
};
use crate::{MakefileVariant, SyntaxKind};
use rowan::ast::AstNode;
use rowan::{GreenNode, SyntaxNode, TextRange};
use std::marker::PhantomData;

/// The result of parsing: a syntax tree and a collection of errors.
///
/// This type is designed to be stored in Salsa databases as it contains
/// the thread-safe `GreenNode` instead of the non-thread-safe `SyntaxNode`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parse<T> {
    green: GreenNode,
    errors: Vec<ErrorInfo>,
    positioned_errors: Vec<PositionedParseError>,
    /// The make variant the text was parsed for.
    variant: Option<MakefileVariant>,
    /// Whether the variant was detected from the text, rather than given.
    detected: bool,
    _ty: PhantomData<fn() -> T>,
}

impl<T> Parse<T> {
    /// Create a new Parse result from a GreenNode, errors, and positioned errors
    pub fn new(
        green: GreenNode,
        errors: Vec<ErrorInfo>,
        positioned_errors: Vec<PositionedParseError>,
    ) -> Self {
        Parse {
            green,
            errors,
            positioned_errors,
            variant: None,
            detected: false,
            _ty: PhantomData,
        }
    }

    pub(crate) fn with_variant(mut self, variant: Option<MakefileVariant>) -> Self {
        self.variant = variant;
        self
    }

    /// Get the make variant the text was parsed for, if any
    pub fn variant(&self) -> Option<MakefileVariant> {
        self.variant
    }

    /// Get the green node (thread-safe representation)
    pub fn green(&self) -> &GreenNode {
        &self.green
    }

    /// Get the syntax errors
    pub fn errors(&self) -> &[ErrorInfo] {
        &self.errors
    }

    /// Get parse errors with position information
    pub fn positioned_errors(&self) -> &[PositionedParseError] {
        &self.positioned_errors
    }

    /// Check that there are no errors
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }

    /// Check that there are no errors
    #[deprecated(since = "0.4.2", note = "use `is_ok` instead")]
    pub fn ok(&self) -> bool {
        self.is_ok()
    }

    /// Convert to a Result, returning the tree if there are no errors
    pub fn into_result(self) -> Result<T, Error>
    where
        T: AstNode<Language = crate::lossless::Lang>,
    {
        if self.errors.is_empty() {
            Ok(self.tree())
        } else {
            Err(Error::Parse(ParseError {
                errors: self.errors,
            }))
        }
    }

    /// Convert to a Result, returning the tree if there are no errors
    #[deprecated(since = "0.4.2", note = "use `into_result` instead")]
    pub fn to_result(self) -> Result<T, Error>
    where
        T: AstNode<Language = crate::lossless::Lang>,
    {
        self.into_result()
    }

    /// Get the parsed syntax tree
    ///
    /// Returns the tree even if there are parse errors. Use `errors()`,
    /// `positioned_errors()`, or `is_ok()` to check for errors separately if needed.
    /// This allows for error-resilient tooling that can work with partial/invalid input.
    ///
    /// For a `Parse<Rule>`, this is the rule within the tree of the whole
    /// text, so surrounding comments and any other items are kept.
    ///
    /// # Panics
    ///
    /// Panics if the text has no node of this type, which happens for a
    /// `Parse<Rule>` of text without a rule. `is_ok()` is false in that case.
    pub fn tree(&self) -> T
    where
        T: AstNode<Language = crate::lossless::Lang>,
    {
        let root = SyntaxNode::new_root_mut(self.green.clone());
        T::cast(root.clone())
            .or_else(|| root.children().find_map(T::cast))
            .expect("no node of the requested type in the parsed text")
    }

    /// Get the root syntax node of the parsed text
    ///
    /// Like `tree()`, this returns a fresh mutable tree, so AST nodes
    /// reached from it can be edited in place. Each call creates a new
    /// tree; edits are not shared between calls or stored in the `Parse`.
    pub fn syntax_node(&self) -> SyntaxNode<crate::lossless::Lang> {
        SyntaxNode::new_root_mut(self.green.clone())
    }
}

impl Parse<Makefile> {
    /// Parse makefile text, returning a Parse result
    ///
    /// See [`Makefile::parse`] for which variant the text is parsed for.
    pub fn parse_makefile(text: &str) -> Self {
        let parsed = crate::lossless::parse(text, None);
        let mut parse = Parse::new(parsed.green_node, parsed.errors, parsed.positioned_errors);
        if crate::lossless::may_have_nmake_directives(text)
            && crate::lossless::has_nmake_directive(&parse.syntax_node())
        {
            parse = Self::parse_makefile_with_variant(text, MakefileVariant::NMake);
        }
        parse.detected = true;
        parse
    }

    /// Whether the variant this was parsed for was detected from the
    /// text, so that edits may change it.
    pub(crate) fn variant_detected(&self) -> bool {
        self.detected
    }

    pub(crate) fn with_detected_variant(mut self, detected: bool) -> Self {
        self.detected = detected;
        self
    }

    /// Parse makefile text written for a specific make variant
    pub fn parse_makefile_with_variant(text: &str, variant: MakefileVariant) -> Self {
        let parsed = crate::lossless::parse(text, Some(variant));
        Parse::new(parsed.green_node, parsed.errors, parsed.positioned_errors)
            .with_variant(Some(variant))
    }
}

impl Parse<Rule> {
    /// Parse the text of a single rule, returning a Parse result
    ///
    /// The text may have comments and blank lines around the rule. Text
    /// without a rule, or with other items such as a second rule or a
    /// variable definition, is reported as an error. Either way the tree
    /// holds all of the text.
    pub fn parse_rule(text: &str) -> Self {
        let parsed = crate::lossless::parse(text, None);
        let root = SyntaxNode::<Lang>::new_root(parsed.green_node.clone());
        let mut errors = parsed.errors;
        let mut positioned_errors = parsed.positioned_errors;

        let mut seen_rule = false;
        let unexpected = root
            .children_with_tokens()
            .find(|item| match item.kind() {
                SyntaxKind::RULE if !seen_rule => {
                    seen_rule = true;
                    false
                }
                SyntaxKind::BLANK_LINE
                | SyntaxKind::COMMENT
                | SyntaxKind::NEWLINE
                | SyntaxKind::WHITESPACE => false,
                _ => true,
            })
            .map(|item| item.text_range());
        let range = match unexpected {
            Some(range) => range,
            None if seen_rule => {
                return Parse::new(parsed.green_node, errors, positioned_errors);
            }
            None => TextRange::empty(0.into()),
        };

        let line = text[..usize::from(range.start())].matches('\n').count() + 1;
        let kind = ParseErrorKind::Other;
        let message = "expected a single rule".to_string();
        errors.push(ErrorInfo {
            message: message.clone(),
            line,
            context: text.lines().nth(line - 1).unwrap_or("").to_string(),
            kind,
        });
        let mut error = PositionedParseError {
            message,
            range,
            code: None,
            kind,
            line_range: range,
            space_indent_range: None,
        };
        crate::lossless::locate_error_line(&parsed.line_ends, text, &mut error);
        positioned_errors.push(error);
        Parse::new(parsed.green_node, errors, positioned_errors)
    }

    /// Convert to a Result, returning the rule if there are no errors
    #[deprecated(since = "0.4.2", note = "use `into_result` instead")]
    pub fn to_rule_result(self) -> Result<Rule, Error> {
        self.into_result()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lossless::Lang;
    use crate::SyntaxKind;

    #[test]
    #[should_panic(expected = "invalid SyntaxKind 60000")]
    fn test_syntax_node_with_unknown_kind() {
        let green = GreenNode::new(rowan::SyntaxKind(60000), []);
        Parse::<Makefile>::new(green, vec![], vec![])
            .syntax_node()
            .kind();
    }

    #[test]
    fn test_syntax_node_is_mutable() {
        let parsed = Parse::<Makefile>::parse_makefile("all: foo\n\techo foo\n");
        let makefile = Makefile::cast(parsed.syntax_node()).unwrap();
        let mut rule = makefile.rules().next().unwrap();
        rule.push_command("echo bar");
        assert_eq!(makefile.to_string(), "all: foo\n\techo foo\n\techo bar\n");
    }

    #[test]
    fn test_syntax_kind_round_trip() {
        use rowan::Language;
        for (i, &kind) in SyntaxKind::ALL.iter().enumerate() {
            let raw = Lang::kind_to_raw(kind);
            assert_eq!(usize::from(raw.0), i);
            assert_eq!(Lang::kind_from_raw(raw), kind);
        }
        assert_eq!(
            SyntaxKind::try_from(SyntaxKind::ALL.len() as u16),
            Err(SyntaxKind::ALL.len() as u16)
        );
    }

    fn parsed_variant(text: &str) -> Option<MakefileVariant> {
        Parse::<Makefile>::parse_makefile(text).variant()
    }

    #[test]
    fn test_parse_detects_nmake() {
        let text = "!IFDEF DEBUG\nCFLAGS = /Zi\n!ENDIF\n";
        let parsed = Parse::<Makefile>::parse_makefile(text);
        assert_eq!(parsed.variant(), Some(MakefileVariant::NMake));
        assert_eq!(
            parsed.green(),
            Parse::<Makefile>::parse_makefile_with_variant(text, MakefileVariant::NMake).green()
        );
        let kinds: Vec<_> = parsed
            .tree()
            .conditionals()
            .flat_map(|c| {
                c.branches()
                    .map(|b| b.conditional_kind())
                    .collect::<Vec<_>>()
            })
            .collect();
        assert_eq!(kinds, vec![Some(crate::ConditionalKind::NmakeIfdef)]);
    }

    #[test]
    fn test_parse_detects_nmake_lines() {
        for text in [
            "!IF \"$(CFG)\" == \"Debug\"\nX = 1\n!  endif # done\n",
            "!INCLUDE <win32.mak>\n",
            "!MESSAGE Building\nall:\n\techo\n",
            "X = 1\n!UNDEF X\n",
            "!CMDSWITCHES +D\n",
            "all:\n!IF 1\n\techo\n!ENDIF\n",
        ] {
            assert_eq!(
                parsed_variant(text),
                Some(MakefileVariant::NMake),
                "{text:?}"
            );
        }
    }

    #[test]
    fn test_parse_does_not_detect_nmake_in_gnu_makefiles() {
        for text in [
            "all:\n\techo\n",
            // Lines GNU make accepts, as a rule or an assignment.
            "!IFDEF X: y\n",
            "!IFDEF = 1\n",
            "!MESSAGE Building: x\n",
            // GNU make expands the line before looking for a separator.
            "!IFDEF $(X)\n",
            // Not at the start of a logical line.
            "A = b \\\n!ENDIF\n",
            "# comment \\\n!ENDIF\n",
            "  !ENDIF\n",
            "all:\n\t!ENDIF\n",
            "define X\n!ENDIF\nendef\n",
            // Not an nmake directive.
            "!ENDIFX\n",
            "!FOO\n",
        ] {
            assert_eq!(parsed_variant(text), None, "{text:?}");
        }
    }

    #[test]
    fn test_parse_with_variant_does_not_detect() {
        let text = "!IFDEF DEBUG\n!ENDIF\n";
        assert_eq!(
            Parse::<Makefile>::parse_makefile_with_variant(text, MakefileVariant::GNUMake)
                .variant(),
            Some(MakefileVariant::GNUMake)
        );
    }

    #[test]
    fn test_apply_edit_detects_nmake() {
        let old_text = "X = 1\n";
        let parsed = Parse::<Makefile>::parse_makefile(old_text);
        assert_eq!(parsed.variant(), None);
        let edit = crate::TextEdit::new(
            rowan::TextRange::empty(rowan::TextSize::of(old_text)),
            "!IFDEF DEBUG\n!ENDIF\n".to_string(),
        );
        let (new_parse, new_text) = parsed.apply_edit(old_text, &edit).unwrap();
        assert_eq!(new_text, "X = 1\n!IFDEF DEBUG\n!ENDIF\n");
        assert_eq!(new_parse, Parse::parse_makefile(&new_text));
        assert_eq!(new_parse.variant(), Some(MakefileVariant::NMake));

        let edit = crate::TextEdit::new(
            rowan::TextRange::new(6.into(), new_text.len().try_into().unwrap()),
            String::new(),
        );
        let (gnu_parse, gnu_text) = new_parse.apply_edit(&new_text, &edit).unwrap();
        assert_eq!(gnu_text, "X = 1\n");
        assert_eq!(gnu_parse, Parse::parse_makefile(&gnu_text));
        assert_eq!(gnu_parse.variant(), None);
    }

    #[test]
    #[allow(deprecated)]
    fn test_deprecated_result_methods() {
        let parsed = Parse::<Makefile>::parse_makefile("all:\n");
        assert!(parsed.ok());
        assert_eq!(parsed.to_result().unwrap().to_string(), "all:\n");
        let parsed = Parse::<Makefile>::parse_makefile("all\n");
        assert!(!parsed.ok());
        assert!(parsed.to_result().is_err());
        let parsed = Parse::<Rule>::parse_rule("all:\n");
        assert_eq!(parsed.to_rule_result().unwrap().to_string(), "all:\n");
        let parsed = Parse::<Rule>::parse_rule("X = 1\n");
        assert!(parsed.to_rule_result().is_err());
    }

    #[test]
    fn test_parse_is_send_and_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Parse<Makefile>>();
        assert_send_sync::<Parse<Rule>>();
    }
}
