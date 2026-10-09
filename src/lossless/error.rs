#[derive(Debug)]
/// An error that can occur when parsing a makefile
#[non_exhaustive]
pub enum Error {
    /// An I/O error occurred
    Io(std::io::Error),

    /// A parse error occurred
    Parse(ParseError),

    /// An editing method could not make the requested change
    InvalidEdit(InvalidEdit),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            Error::Io(e) => write!(f, "IO error: {}", e),
            Error::Parse(e) => write!(f, "Parse error: {}", e),
            Error::InvalidEdit(e) => write!(f, "Invalid edit: {}", e),
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::Io(e)
    }
}

impl std::error::Error for Error {}

impl From<InvalidEdit> for Error {
    fn from(e: InvalidEdit) -> Self {
        Error::InvalidEdit(e)
    }
}

/// The class of an [`InvalidEdit`].
///
/// Use this rather than matching on error messages, which are meant for
/// humans and may change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum InvalidEditKind {
    /// An argument is not valid for this edit, such as an empty list of
    /// targets or an unknown conditional type.
    InvalidArgument,
    /// An index is past the end of the items it refers to.
    IndexOutOfRange,
    /// The result of the edit cannot be written so that it reads back as
    /// requested, such as a value containing a newline that would start
    /// another line.
    NotRepresentable,
    /// An item cannot go at the requested position, such as a variable
    /// between two recipe lines of a rule.
    InvalidPosition,
    /// The item being edited does not support this edit, for example
    /// because it is not attached to a makefile or lacks the part the
    /// edit changes.
    Unsupported,
}

/// An error from an editing method that could not make the requested
/// change.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InvalidEdit {
    kind: InvalidEditKind,
    operation: &'static str,
    message: String,
}

impl InvalidEdit {
    pub(crate) fn new(
        kind: InvalidEditKind,
        operation: &'static str,
        message: impl Into<String>,
    ) -> Self {
        InvalidEdit {
            kind,
            operation,
            message: message.into(),
        }
    }

    /// The class of this error.
    pub fn kind(&self) -> InvalidEditKind {
        self.kind
    }

    /// The editing method that failed, such as `Rule::set_targets`.
    pub fn operation(&self) -> &'static str {
        self.operation
    }

    /// A description of why the edit failed, meant for humans.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl std::fmt::Display for InvalidEdit {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}: {}", self.operation, self.message)
    }
}

impl std::error::Error for InvalidEdit {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invalid_edit_display() {
        let error = invalid_edit(
            InvalidEditKind::InvalidArgument,
            "Rule::set_targets",
            "Cannot set empty targets list for a rule",
        );
        assert_eq!(
            error.to_string(),
            "Invalid edit: Rule::set_targets: Cannot set empty targets list for a rule"
        );
    }
}

/// An [`Error::InvalidEdit`] for the editing method `operation`.
pub(crate) fn invalid_edit(
    kind: InvalidEditKind,
    operation: &'static str,
    message: impl Into<String>,
) -> Error {
    Error::InvalidEdit(InvalidEdit::new(kind, operation, message))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// An error that occurred while parsing a makefile
pub struct ParseError {
    /// The list of individual parsing errors
    pub errors: Vec<ErrorInfo>,
}

/// The class of a parse error.
///
/// Use this rather than matching on error messages, which are meant for
/// humans and may change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// A line that is not a rule, variable assignment or directive, such as
    /// a rule without a `:` (GNU make: "missing separator").
    MissingSeparator,
    /// An indented line outside of a rule (GNU make: "recipe commences
    /// before first target").
    RecipeBeforeFirstTarget,
    /// A rule without a target.
    MissingTarget,
    /// An archive member reference such as `lib(member` without a closing
    /// parenthesis. Only BSD make rejects this; GNU make takes `lib(member`
    /// as a plain file name.
    UnclosedArchiveMember,
    /// A variable reference such as `$(FOO` without a closing delimiter.
    UnclosedReference,
    /// A parenthesized conditional argument without a closing parenthesis.
    UnclosedParenthesis,
    /// A missing or empty variable name, e.g. in `export` or `define`.
    ExpectedVariableName,
    /// A variable name not followed by a valid assignment operator.
    ExpectedAssignmentOperator,
    /// A malformed conditional directive, such as `ifeq` without arguments
    /// (GNU make: "invalid syntax in conditional").
    InvalidConditional,
    /// A conditional that is not closed before the end of the input
    /// (GNU make: "missing 'endif'").
    MissingEndif,
    /// An `endif` without a matching conditional (GNU make: "extraneous
    /// 'endif'").
    ExtraneousEndif,
    /// An `else` (or BSD `.elif`) without a matching conditional.
    ElseWithoutIf,
    /// An `else` after the final `else` of a conditional (GNU make: "only
    /// one 'else' per conditional").
    DuplicateElse,
    /// A BSD `.for` loop variable name with a character that BSD make
    /// does not allow, such as `$` or `:`.
    InvalidForLoop,
    /// A BSD `.for` loop without variables before `in`, as in `.for in 1`
    /// (BSD make: "Missing iteration variables in .for loop").
    MissingForVariables,
    /// A BSD `.for` loop without `in` after its variables, as in `.for x`
    /// (BSD make: "Missing \"in\" in .for loop").
    MissingForIn,
    /// A BSD `.for` loop that is not closed before the end of the input.
    MissingEndfor,
    /// A BSD `.endfor` without a matching `.for`.
    ExtraneousEndfor,
    /// A `define` that is not closed before the end of the input
    /// (GNU make: "missing 'endef', unterminated 'define'").
    MissingEndef,
    /// An `include` directive without a file name.
    MissingIncludePath,
    /// A BSD make `.include` path without its closing `>` or `"`.
    UnclosedIncludePath,
    /// A BSD make `.include` path not delimited by `<...>` or `"..."`.
    UndelimitedIncludePath,
    /// A BSD make line starting with `.` that is neither a known directive
    /// nor a dependency line or variable assignment, such as `.iff`, or a
    /// `.for` without anything after it.
    UnknownDirective,
    /// Unexpected text where the end of the line was expected. GNU make
    /// only warns about text after a directive such as `else junk` or
    /// `endef junk`, while BSD make treats it as an error.
    ExtraneousText,
    /// A token that cannot start any construct.
    UnexpectedToken,
    /// Variable references, conditionals or loops nested more deeply than
    /// this crate supports.
    TooDeeplyNested,
    /// Any other error.
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Information about a specific parsing error
pub struct ErrorInfo {
    /// The error message
    pub message: String,
    /// The line number where the error occurred
    pub line: usize,
    /// The context around the error
    pub context: String,
    pub(crate) kind: ParseErrorKind,
}

impl ErrorInfo {
    /// The class of this error.
    pub fn kind(&self) -> ParseErrorKind {
        self.kind
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for err in &self.errors {
            writeln!(f, "Error at line {}: {}", err.line, err.message)?;
            writeln!(f, "{}| {}", err.line, err.context)?;
        }
        Ok(())
    }
}

impl std::error::Error for ParseError {}

impl From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Error::Parse(e)
    }
}

/// A positioned parse error containing location information.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PositionedParseError {
    /// The error message
    pub message: String,
    /// The text range where the error occurred
    pub range: rowan::TextRange,
    /// Optional error code for categorization
    pub code: Option<String>,
    pub(crate) kind: ParseErrorKind,
    pub(crate) line_range: rowan::TextRange,
    pub(crate) space_indent_range: Option<rowan::TextRange>,
}

impl PositionedParseError {
    /// The class of this error.
    pub fn kind(&self) -> ParseErrorKind {
        self.kind
    }

    /// The source range of the logical line the error is on, from the
    /// start of its first physical line to the end of its last one
    /// (joined by backslash-newline continuations), excluding the final
    /// line ending.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    ///
    /// let parsed = Makefile::parse("all:\n\nfoo \\\n  bar\n");
    /// let error = &parsed.positioned_errors()[0];
    /// assert_eq!(error.line_range(), TextRange::new(6.into(), 17.into()));
    /// ```
    pub fn line_range(&self) -> rowan::TextRange {
        self.line_range
    }

    /// For a [`ParseErrorKind::MissingSeparator`] error on a line indented
    /// with spaces, the source range of those spaces.
    ///
    /// Such a line is usually a recipe line that should have been indented
    /// with a tab.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, ParseErrorKind, TextRange};
    ///
    /// let parsed = Makefile::parse("all:\n\n  echo hi\n");
    /// let error = &parsed.positioned_errors()[0];
    /// assert_eq!(error.kind(), ParseErrorKind::MissingSeparator);
    /// assert_eq!(
    ///     error.space_indent_range(),
    ///     Some(TextRange::new(6.into(), 8.into()))
    /// );
    /// ```
    pub fn space_indent_range(&self) -> Option<rowan::TextRange> {
        self.space_indent_range
    }
}

impl std::fmt::Display for PositionedParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for PositionedParseError {}

/// An error from parsing a keyword enum such as
/// [`AssignmentOperator`](crate::AssignmentOperator) from a string that is
/// not one of its keywords.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParseKeywordError {
    pub(crate) keyword: String,
}

impl ParseKeywordError {
    /// The text that is not a known keyword.
    pub fn keyword(&self) -> &str {
        &self.keyword
    }
}

impl std::fmt::Display for ParseKeywordError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unknown keyword: {:?}", self.keyword)
    }
}

impl std::error::Error for ParseKeywordError {}
