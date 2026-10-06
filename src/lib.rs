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
//!
//! Editing methods that add new lines end them the same way as the first
//! line of the file, so that files with CRLF line endings keep them. Nodes
//! that are not yet part of a file, such as those created by [`Rule::new`],
//! use `"\n"`.

mod ast;
mod bsd_condition;
mod incremental;
mod lex;
mod lossless;
mod parse;
mod pattern;
mod reference;
mod text;

pub use ast::conditional::{ConditionalBranch, ConditionalItem};
pub use ast::makefile::MakefileItem;
pub use ast::rule::RuleItem;
pub use bsd_condition::{
    parse_bsd_condition, parse_bsd_if_else_condition, BsdComparisonOp, BsdCondition,
    BsdConditionError, BsdFunction, BsdOperand,
};
pub use incremental::{apply_edit_to_text, TextEdit};
pub use lossless::{
    ArchiveMember, ArchiveMembers, Conditional, Directive, Error, ErrorInfo, ExpressionStatement,
    ForLoop, Identifier, Include, Lang, Load, Makefile, ParseError, ParseErrorKind,
    PositionedParseError, Recipe, RecipeVariableReference, Rule, VariableDefinition,
    VariableReference, Vpath,
};
pub use parse::Parse;
pub use reference::{
    AssignOp, Modifier, ModifierArg, ModifierArgPart, ParsedReference, ReferenceError, SortOrder,
    SubstituteFlags, WordSelector,
};
pub use rowan::TextRange;
pub use text::{is_in_prerequisites, variable_at_offset, word_at_offset};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// The variant of makefile being parsed
#[non_exhaustive]
pub enum MakefileVariant {
    /// GNU Make (most common, supports ifeq/ifneq/ifdef/ifndef conditionals, pattern rules, etc.)
    GNUMake,
    /// BSD Make, including NetBSD make and its portable version bmake (also used
    /// by FreeBSD). Uses `.if`/`.for`/`.include` style directives.
    BSDMake,
    /// Microsoft nmake (Windows - uses !IF/!IFDEF/!IFNDEF directives)
    NMake,
    /// POSIX-compliant make (basic portable subset, no extensions)
    POSIXMake,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(non_camel_case_types)]
#[repr(u16)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum SyntaxKind {
    IDENTIFIER = 0,
    INDENT,
    TEXT,
    WHITESPACE,
    NEWLINE,
    DOLLAR,
    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,
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
    VPATH, // A `vpath PATTERN DIRS` / `vpath PATTERN` / `vpath` directive

    // Archive members
    ARCHIVE_MEMBERS, // Container for just the members inside parentheses
    ARCHIVE_MEMBER,  // Individual member like "bar.o" or "baz.o"

    // Blank lines
    BLANK_LINE, // A blank line between top-level items

    // BSD make
    FOR_LOOP,   // A `.for` ... `.endfor` block
    FOR_HEADER, // The `.for VAR in LIST` line
    FOR_END,    // The `.endfor` line
    DIRECTIVE,  // A single-line directive such as `.undef` or `.error`

    EXPRESSION_STATEMENT, // A line of only references, e.g. `$(eval ...)` or `$(info ...)`, optionally followed by `;` and text
    TARGET_PATTERN,       // The target pattern of a static pattern rule
    LOAD,                 // A GNU make `load` or `-load` directive
}

/// Convert our `SyntaxKind` into the rowan `SyntaxKind`.
impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}
