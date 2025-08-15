#![allow(clippy::tabs_in_doc_comments)] // Makefile uses tabs
#![deny(missing_docs)]

//! A lossless parser for Makefiles
//!
//! Example:
//!
//! ```rust
//! use std::io::Read;
//! let contents = r#"PYTHON = python3
//!
//! .PHONY: all
//!
//! all: build
//!
//! build:
//! 	$(PYTHON) setup.py build
//! "#;
//! let makefile: makefile_lossless::Makefile = contents.parse().unwrap();
//!
//! assert_eq!(makefile.rules().count(), 3);
//! ```

mod lex;
mod lossless;
mod parse;

pub use lossless::{
    Error, Identifier, Include, Lang, Makefile, ParseError, Rule, VariableDefinition,
};
pub use parse::Parse;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(non_camel_case_types)]
#[repr(u16)]
#[allow(missing_docs)]
pub enum SyntaxKind {
    IDENTIFIER = 0,
    INDENT,
    TEXT,
    WHITESPACE,
    NEWLINE,
    DOLLAR,
    LPAREN,
    RPAREN,
    QUOTE,
    BACKSLASH,
    COMMA,
    OPERATOR,

    COMMENT,
    ERROR,

    // composite nodes
    ROOT, // The entire file
    RULE, // A single rule
    RECIPE,
    VARIABLE,
    EXPR,

    // Directives
    CONDITIONAL,
    INCLUDE,
}

/// Convert our `SyntaxKind` into the rowan `SyntaxKind`.
impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}
