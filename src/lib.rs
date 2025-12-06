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
    ArchiveMember, ArchiveMembers, Conditional, Error, Identifier, Include, Lang, Makefile,
    MakefileItem, MakefileVariant, ParseError, Rule, RuleItem, VariableDefinition,
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
    ROOT,          // The entire file
    RULE,          // A single rule
    RECIPE,        // A command/recipe line
    VARIABLE,      // A variable definition
    EXPR,          // An expression (e.g., targets before colon, or old-style prerequisites)
    TARGETS,       // Container for targets before the colon
    PREREQUISITES, // Container for prerequisites after the colon
    PREREQUISITE,  // A single prerequisite item

    // Directives
    CONDITIONAL,       // The entire conditional block (ifdef...endif)
    CONDITIONAL_IF,    // The initial conditional (ifdef/ifndef/ifeq/ifneq)
    CONDITIONAL_ELSE,  // An else or else-conditional clause
    CONDITIONAL_ENDIF, // The endif keyword
    INCLUDE,

    // Archive members
    ARCHIVE_MEMBERS, // Container for just the members inside parentheses
    ARCHIVE_MEMBER,  // Individual member like "bar.o" or "baz.o"

    // Blank lines
    BLANK_LINE, // A blank line between top-level items
}

/// Convert our `SyntaxKind` into the rowan `SyntaxKind`.
impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}
