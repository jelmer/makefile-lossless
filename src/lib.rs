#![allow(clippy::tabs_in_doc_comments)] // Makefile uses tabs
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]

//! A lossless parser and editor for makefiles.
//!
//! Parsing produces a concrete syntax tree, built on [`rowan`], that keeps
//! every byte of the input: whitespace, comments, line continuations and
//! anything the parser did not understand. Converting the tree back to text
//! gives the original input, so a makefile can be edited and written out
//! with only the intended changes.
//!
//! [`Makefile`] is the root of the tree. Its [`items`](Makefile::items) are
//! [`MakefileItem`]s: a [`Rule`] (targets, prerequisites and [`Recipe`]
//! lines), a [`VariableDefinition`], an [`Include`], a [`Conditional`]
//! (whose branches contain further items) and a few others. These types
//! are views into the same tree; editing through one of them, e.g. with
//! [`VariableDefinition::set_value`] or [`Rule::add_prerequisite`], changes
//! the [`Makefile`] it belongs to.
//!
//! Parsing never fails. [`Makefile::parse`] returns a [`Parse`], which holds
//! the tree together with any syntax errors found, recorded as
//! [`ErrorInfo`]. Text that could not be parsed ends up in the tree as
//! error nodes rather than being dropped. The [`FromStr`](std::str::FromStr)
//! implementation of [`Makefile`] is stricter, and returns
//! [`Error::Parse`] if there were any errors.
//!
//! GNU make, BSD make, nmake and POSIX make differ in syntax, so parsing
//! and some accessors take a [`MakefileVariant`]. [`Makefile::parse`]
//! accepts the syntax of any of them, while [`Makefile::parse_with_variant`]
//! only accepts what that variant does. Methods that interpret text, such
//! as [`Rule::targets`], read it the way GNU make does; their `_for`
//! counterparts, such as [`Rule::targets_for`], take the variant to use.
//!
//! # Example
//!
//! ```rust
//! use makefile_lossless::Makefile;
//!
//! let contents = r#"PYTHON = python3
//!
//! .PHONY: all
//!
//! all: build
//!
//! build:
//! 	$(PYTHON) setup.py build
//! "#;
//! let parsed = Makefile::parse(contents);
//! assert!(parsed.ok());
//! let makefile = parsed.tree();
//! assert_eq!(makefile.code(), contents);
//!
//! let mut var = makefile.find_variable("PYTHON").next().unwrap();
//! var.set_value("python3.13");
//!
//! let mut rule = makefile.find_rule_by_target("all").unwrap();
//! rule.add_prerequisite("test").unwrap();
//!
//! assert_eq!(
//!     makefile.to_string(),
//!     r#"PYTHON = python3.13
//!
//! .PHONY: all
//!
//! all: build test
//!
//! build:
//! 	$(PYTHON) setup.py build
//! "#
//! );
//! ```
//!
//! Errors are recorded rather than raised:
//!
//! ```rust
//! use makefile_lossless::Makefile;
//!
//! let contents = "all: build\nthis is not valid\n";
//! let parsed = Makefile::parse(contents);
//! assert!(!parsed.ok());
//! assert_eq!(parsed.tree().code(), contents);
//! assert!(contents.parse::<Makefile>().is_err());
//! ```
//!
//! Editing methods that add new lines end them the same way as the first
//! line of the file, so that files with CRLF line endings keep them. Nodes
//! that are not yet part of a file, such as those created by [`Rule::new`],
//! use `"\n"`. Rules and other items inserted into a file are converted to
//! its line ending, except for line breaks after a backslash, since whether
//! a backslash before a CRLF continues the line depends on the make variant.
//!
//! New recipe lines start with the recipe prefix in effect where they are
//! added: a tab, or the character set with GNU make's `.RECIPEPREFIX` in
//! the lines before them. Recipe lines of inserted rules and other items
//! are converted the same way, including the prefix at the start of their
//! continuation lines, which make strips.

mod ast;
mod bsd_condition;
mod incremental;
mod lex;
mod lossless;
mod nmake_condition;
mod parse;
mod pattern;
mod reference;
mod syntax_rules;
#[cfg(test)]
mod test_util;
mod text;

#[cfg(doctest)]
#[doc = include_str!("../README.md")]
struct ReadmeDoctests;

pub use ast::bsd::DirectiveKind;
pub use ast::conditional::{BranchKind, ConditionalBranch, ConditionalItem, ConditionalKind};
pub use ast::include::IncludeKind;
pub use ast::makefile::MakefileItem;
pub use ast::rule::{RuleItem, RuleOperator};
pub use ast::variable::{AssignmentOperator, ExportState};
pub use bsd_condition::{
    parse_bsd_condition, parse_bsd_if_else_condition, BsdComparisonOp, BsdCondition,
    BsdConditionError, BsdConditionErrorKind, BsdFunction, BsdOperand,
};
pub use incremental::{apply_edit_to_text, EditError, TextEdit};
pub use lossless::{
    ArchiveMember, ArchiveMembers, Conditional, Directive, Error, ErrorInfo, ExpressionStatement,
    ForLoop, Identifier, Include, InvalidEdit, InvalidEditKind, Lang, Load, Makefile, ParseError,
    ParseErrorKind, ParseKeywordError, PositionedParseError, Recipe, RecipeVariableReference,
    ReferenceLocation, Rule, VariableDefinition, VariableReference, Vpath,
};
pub use nmake_condition::{
    parse_nmake_condition, NmakeBinaryOp, NmakeCondition, NmakeConditionError,
    NmakeConditionErrorKind, NmakeUnaryOp,
};
pub use parse::Parse;
pub use reference::{split_references, TextPart};
pub use reference::{
    AssignOp, FunctionCall, Modifier, ModifierArg, ModifierArgPart, ParsedReference,
    ReferenceError, ReferenceSyntaxErrorKind, SortOrder, SubstituteFlags, WordSelector,
};
pub use rowan::{TextRange, TextSize};
// Re-exported for compatibility until they are removed.
#[allow(deprecated)]
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

impl MakefileVariant {
    fn short_name(self) -> &'static str {
        match self {
            MakefileVariant::GNUMake => "gnu",
            MakefileVariant::BSDMake => "bsd",
            MakefileVariant::NMake => "nmake",
            MakefileVariant::POSIXMake => "posix",
        }
    }
}

/// The name of the make variant, such as `GNU make`.
impl std::fmt::Display for MakefileVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            MakefileVariant::GNUMake => "GNU make",
            MakefileVariant::BSDMake => "BSD make",
            MakefileVariant::NMake => "nmake",
            MakefileVariant::POSIXMake => "POSIX make",
        })
    }
}

/// Parse a make variant from its name as written by `Display`, such as
/// `GNU make`, or a short name: `gnu`, `bsd`, `nmake` or `posix`. Case is
/// ignored.
///
/// # Example
/// ```
/// use makefile_lossless::MakefileVariant;
/// assert_eq!("bsd".parse(), Ok(MakefileVariant::BSDMake));
/// assert_eq!("GNU make".parse(), Ok(MakefileVariant::GNUMake));
/// assert!("gmake".parse::<MakefileVariant>().is_err());
/// ```
impl std::str::FromStr for MakefileVariant {
    type Err = ParseVariantError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        [
            MakefileVariant::GNUMake,
            MakefileVariant::BSDMake,
            MakefileVariant::NMake,
            MakefileVariant::POSIXMake,
        ]
        .into_iter()
        .find(|variant| {
            s.eq_ignore_ascii_case(variant.short_name())
                || s.eq_ignore_ascii_case(&variant.to_string())
        })
        .ok_or_else(|| ParseVariantError(s.to_string()))
    }
}

/// The error returned when parsing an unknown [`MakefileVariant`] name.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParseVariantError(String);

impl std::fmt::Display for ParseVariantError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unknown make variant: {:?}", self.0)
    }
}

impl std::error::Error for ParseVariantError {}

/// Define `SyntaxKind` along with `SyntaxKind::ALL`, which lists every
/// variant in discriminant order.
macro_rules! syntax_kinds {
    ($($kind:ident,)*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[allow(non_camel_case_types)]
        #[repr(u16)]
        #[allow(missing_docs)]
        #[non_exhaustive]
        pub enum SyntaxKind {
            $($kind,)*
        }

        impl SyntaxKind {
            /// Every kind, indexed by its raw value.
            const ALL: &'static [SyntaxKind] = &[$(SyntaxKind::$kind,)*];
        }
    };
}

syntax_kinds! {
    IDENTIFIER,
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

impl TryFrom<u16> for SyntaxKind {
    type Error = u16;

    /// Convert a raw kind back, returning it as the error if it is unknown.
    fn try_from(raw: u16) -> Result<Self, u16> {
        Self::ALL.get(usize::from(raw)).copied().ok_or(raw)
    }
}

/// Convert our `SyntaxKind` into the rowan `SyntaxKind`.
impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

#[cfg(test)]
mod tests {
    use super::MakefileVariant;

    #[test]
    fn test_variant_display_round_trip() {
        for variant in [
            MakefileVariant::GNUMake,
            MakefileVariant::BSDMake,
            MakefileVariant::NMake,
            MakefileVariant::POSIXMake,
        ] {
            assert_eq!(variant.to_string().parse(), Ok(variant));
            assert_eq!(variant.to_string().to_uppercase().parse(), Ok(variant));
        }
        assert_eq!(MakefileVariant::GNUMake.to_string(), "GNU make");
        assert_eq!("NMAKE".parse(), Ok(MakefileVariant::NMake));
        assert_eq!("posix".parse(), Ok(MakefileVariant::POSIXMake));
        let err = "gmake".parse::<MakefileVariant>().unwrap_err();
        assert_eq!(err.to_string(), "unknown make variant: \"gmake\"");
    }
}
