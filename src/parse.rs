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
    _ty: PhantomData<T>,
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

    /// Check if there are any errors
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }

    /// Convert to a Result, returning the tree if there are no errors
    pub fn to_result(self) -> Result<T, Error>
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

    /// Get the parsed syntax tree
    ///
    /// Returns the tree even if there are parse errors. Use `errors()`,
    /// `positioned_errors()`, or `ok()` to check for errors separately if needed.
    /// This allows for error-resilient tooling that can work with partial/invalid input.
    ///
    /// For a `Parse<Rule>`, this is the rule within the tree of the whole
    /// text, so surrounding comments and any other items are kept.
    ///
    /// # Panics
    ///
    /// Panics if the text has no node of this type, which happens for a
    /// `Parse<Rule>` of text without a rule. `ok()` is false in that case.
    pub fn tree(&self) -> T
    where
        T: AstNode<Language = crate::lossless::Lang>,
    {
        let root = SyntaxNode::new_root_mut(self.green.clone());
        T::cast(root.clone())
            .or_else(|| root.children().find_map(T::cast))
            .expect("no node of the requested type in the parsed text")
    }

    /// Get the syntax node
    pub fn syntax_node(&self) -> SyntaxNode<crate::lossless::Lang> {
        SyntaxNode::new_root(self.green.clone())
    }
}

// Implement Send + Sync since GreenNode is thread-safe
unsafe impl<T> Send for Parse<T> {}
unsafe impl<T> Sync for Parse<T> {}

impl Parse<Makefile> {
    /// Parse makefile text, returning a Parse result
    pub fn parse_makefile(text: &str) -> Self {
        let parsed = crate::lossless::parse(text, None);
        Parse::new(parsed.green_node, parsed.errors, parsed.positioned_errors)
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
        crate::lossless::locate_error_lines(&root, text, std::slice::from_mut(&mut error));
        positioned_errors.push(error);
        Parse::new(parsed.green_node, errors, positioned_errors)
    }

    /// Convert to a Result, returning the rule if there are no errors
    pub fn to_rule_result(self) -> Result<Rule, Error> {
        self.to_result()
    }
}
