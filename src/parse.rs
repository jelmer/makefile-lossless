//! Parse wrapper type following rust-analyzer's pattern for thread-safe storage in Salsa.

use crate::lossless::{Error, ErrorInfo, Makefile, ParseError, Rule};
use rowan::ast::AstNode;
use rowan::{GreenNode, SyntaxNode};
use std::marker::PhantomData;

/// The result of parsing: a syntax tree and a collection of errors.
///
/// This type is designed to be stored in Salsa databases as it contains
/// the thread-safe `GreenNode` instead of the non-thread-safe `SyntaxNode`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parse<T> {
    green: GreenNode,
    errors: Vec<ErrorInfo>,
    _ty: PhantomData<T>,
}

impl<T> Parse<T> {
    /// Create a new Parse result from a GreenNode and errors
    pub fn new(green: GreenNode, errors: Vec<ErrorInfo>) -> Self {
        Parse {
            green,
            errors,
            _ty: PhantomData,
        }
    }

    /// Get the green node (thread-safe representation)
    pub fn green(&self) -> &GreenNode {
        &self.green
    }

    /// Get the syntax errors
    pub fn errors(&self) -> &[ErrorInfo] {
        &self.errors
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
            let node = SyntaxNode::new_root_mut(self.green);
            Ok(T::cast(node).expect("root node has wrong type"))
        } else {
            Err(Error::Parse(ParseError {
                errors: self.errors,
            }))
        }
    }

    /// Get the parsed syntax tree
    ///
    /// Returns the tree even if there are parse errors. Use `errors()` or `ok()` to check
    /// for errors separately if needed.
    pub fn tree(&self) -> T
    where
        T: AstNode<Language = crate::lossless::Lang>,
    {
        let node = SyntaxNode::new_root_mut(self.green.clone());
        T::cast(node).expect("root node has wrong type")
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
        Parse::new(parsed.green_node, parsed.errors)
    }
}

impl Parse<Rule> {
    /// Parse rule text, returning a Parse result
    pub fn parse_rule(text: &str) -> Self {
        let parsed = crate::lossless::parse(text, None);
        Parse::new(parsed.green_node, parsed.errors)
    }

    /// Convert to a Result, extracting a single rule from the makefile
    pub fn to_rule_result(self) -> Result<Rule, Error> {
        if !self.errors.is_empty() {
            return Err(Error::Parse(ParseError {
                errors: self.errors,
            }));
        }

        let makefile =
            Makefile::cast(SyntaxNode::new_root_mut(self.green)).expect("root node has wrong type");
        let rules: Vec<_> = makefile.rules().collect();

        if rules.len() == 1 {
            Ok(rules.into_iter().next().unwrap())
        } else {
            Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "expected a single rule".to_string(),
                    line: 1,
                    context: "".to_string(),
                }],
            }))
        }
    }
}
