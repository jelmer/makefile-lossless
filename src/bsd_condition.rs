//! Parser for the expressions in BSD make conditional directives such as
//! `.if`, `.elif` and `.ifdef`.
//!
//! The grammar follows NetBSD make(1) (and bmake):
//!
//! ```text
//! Or      -> And ('||' And)*
//! And     -> Term ('&&' Term)*
//! Term    -> '!' Term | '(' Or ')' | Function '(' Argument ')'
//!          | Leaf | Leaf CompareOp Leaf | BareWord
//! ```

use crate::reference::{ParsedReference, ReferenceError, ReferenceSyntaxErrorKind};
use crate::MakefileVariant;
use std::fmt;
use std::str::FromStr;

/// A parsed BSD make conditional expression.
///
/// Operands and arguments are kept as unexpanded text; expanding variable
/// references and evaluating the result is up to the caller.
///
/// How a lone [`Self::Value`] or [`Self::Bare`] word evaluates depends on
/// the directive (see [`crate::ConditionalBranch::conditional_type`]):
///
/// * For `.if`, a bare word `foo` means `defined(foo)`. A value is true if,
///   after expansion, it is a non-zero number or, when not a number, a
///   non-empty string.
/// * For `.ifdef` and `.ifmake`, a bare word is passed to `defined()` or
///   `make()` respectively. So is the expanded text of a value, unless it
///   is a quoted string (true if non-empty) or a number (true if non-zero).
/// * `.ifndef` and `.ifnmake` are the same as `.ifdef` and `.ifmake`, but
///   negate the result of each `defined()` / `make()` applied to a bare word
///   or value; `!`, `&&` and `||` apply on top of that. So `.ifndef A || B`
///   is true if either `A` or `B` is undefined.
///
/// # Example
/// ```
/// use makefile_lossless::{
///     parse_bsd_condition, BsdComparisonOp, BsdCondition, BsdFunction, BsdOperand,
/// };
/// assert_eq!(
///     parse_bsd_condition(r#"defined(MKMAN) && ${MKMAN} != "no""#).unwrap(),
///     BsdCondition::And(vec![
///         BsdCondition::Call {
///             function: BsdFunction::Defined,
///             argument: "MKMAN".to_string(),
///         },
///         BsdCondition::Compare {
///             lhs: BsdOperand::VariableReference("${MKMAN}".to_string()),
///             op: BsdComparisonOp::NotEqual,
///             rhs: BsdOperand::String("no".to_string()),
///         },
///     ])
/// );
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BsdCondition {
    /// `a || b || ...`, with at least two alternatives.
    Or(Vec<BsdCondition>),
    /// `a && b && ...`, with at least two operands.
    And(Vec<BsdCondition>),
    /// `!a`
    Not(Box<BsdCondition>),
    /// A function call such as `defined(VAR)` or `empty(VAR:Mfoo)`.
    Call {
        /// The function being called.
        function: BsdFunction,
        /// The unexpanded argument between the parentheses.
        ///
        /// For [`BsdFunction::Empty`] this is the inside of a variable
        /// reference, i.e. a variable name optionally followed by
        /// modifiers, such as `VAR:Mfoo`. Its value is that of `${VAR:Mfoo}`.
        /// For the other functions surrounding whitespace is stripped.
        argument: String,
    },
    /// A comparison such as `${VAR} == "value"` or `${VER:U0} >= 5`.
    ///
    /// make compares numerically if neither operand is a quoted string and
    /// both are numbers after expansion. Otherwise it compares the strings,
    /// in which case only `==` and `!=` are allowed.
    Compare {
        /// The left-hand side. As in make, unquoted text is rejected here
        /// unless the operand starts with a variable reference or digit,
        /// except by [`parse_bsd_if_else_condition`].
        lhs: BsdOperand,
        /// The comparison operator.
        op: BsdComparisonOp,
        /// The right-hand side.
        rhs: BsdOperand,
    },
    /// An operand on its own, such as `${VAR}`, `0` or `"string"`.
    Value(BsdOperand),
    /// A bare word on its own, such as `foo` in `.if foo` or `.ifmake foo`,
    /// passed to the default function of the directive. It may contain
    /// variable references, e.g. `V${:UA}R`.
    Bare(String),
}

/// The functions that can be called in a BSD make conditional.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BsdFunction {
    /// `defined(VAR)`: whether the variable is defined.
    Defined,
    /// `make(target)`: whether the target was requested on the command line
    /// (or in `.MAKEFLAGS`); the argument is a pattern.
    Make,
    /// `empty(VAR:modifiers)`: whether the (modified) value is empty.
    Empty,
    /// `exists(file)`: whether the file exists, searching `.PATH`.
    Exists,
    /// `target(t)`: whether the target has been defined.
    Target,
    /// `commands(t)`: whether the target has been defined and has commands.
    Commands,
}

impl BsdFunction {
    const ALL: [BsdFunction; 6] = [
        BsdFunction::Defined,
        BsdFunction::Make,
        BsdFunction::Empty,
        BsdFunction::Exists,
        BsdFunction::Target,
        BsdFunction::Commands,
    ];

    /// The name of the function as written in a makefile, e.g. `defined`.
    pub fn name(&self) -> &'static str {
        match self {
            BsdFunction::Defined => "defined",
            BsdFunction::Make => "make",
            BsdFunction::Empty => "empty",
            BsdFunction::Exists => "exists",
            BsdFunction::Target => "target",
            BsdFunction::Commands => "commands",
        }
    }
}

impl fmt::Display for BsdFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A comparison operator in a BSD make conditional.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BsdComparisonOp {
    /// `==`
    Equal,
    /// `!=`
    NotEqual,
    /// `<`
    Less,
    /// `<=`
    LessOrEqual,
    /// `>`
    Greater,
    /// `>=`
    GreaterOrEqual,
}

impl BsdComparisonOp {
    /// The operator as written in a makefile, e.g. `==`.
    pub fn as_str(&self) -> &'static str {
        match self {
            BsdComparisonOp::Equal => "==",
            BsdComparisonOp::NotEqual => "!=",
            BsdComparisonOp::Less => "<",
            BsdComparisonOp::LessOrEqual => "<=",
            BsdComparisonOp::Greater => ">",
            BsdComparisonOp::GreaterOrEqual => ">=",
        }
    }
}

impl fmt::Display for BsdComparisonOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// An operand of a comparison, or a value tested on its own.
///
/// Backslash escapes outside variable references have been removed from
/// [`Self::String`] and [`Self::Word`]. An escaped `$` becomes `$$`, so
/// that expanding the text gives a literal `$`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BsdOperand {
    /// A single variable reference, including the `$` and delimiters,
    /// e.g. `${VAR:Mfoo}` or `$(VAR)`.
    VariableReference(String),
    /// The contents of a double-quoted string. It may contain variable
    /// references, e.g. `${PREFIX}/bin`.
    String(String),
    /// A decimal, hexadecimal (`0x1f`) or floating point number.
    Number(String),
    /// Any other unquoted text, possibly mixing literal text and variable
    /// references, e.g. `foo`, `${A}x` or `0x${HEX}`.
    Word(String),
}

impl BsdOperand {
    /// The unexpanded text of the operand, without surrounding quotes.
    pub fn text(&self) -> &str {
        match self {
            BsdOperand::VariableReference(s)
            | BsdOperand::String(s)
            | BsdOperand::Number(s)
            | BsdOperand::Word(s) => s,
        }
    }

    /// Whether this is a quoted string. Quoted strings are never compared
    /// numerically.
    pub fn is_quoted(&self) -> bool {
        matches!(self, BsdOperand::String(_))
    }
}

/// The class of a [`BsdConditionError`].
///
/// Use this rather than matching on error messages, which are meant for
/// humans and may change. Unless noted otherwise, make reports these errors
/// as "Malformed conditional".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BsdConditionErrorKind {
    /// The condition or an operand of `!`, `&&` or `||` is missing.
    MissingOperand,
    /// A `)` where an operand was expected, as in `()`.
    UnexpectedParenthesis,
    /// A `)` without a matching `(`.
    UnbalancedParenthesis,
    /// A `(` without a matching `)`.
    UnclosedParenthesis,
    /// `&&` or `||` where an operand was expected.
    UnexpectedOperator,
    /// Text after a complete condition that is not `&&` or `||`.
    UnexpectedText,
    /// A single `&` or `|` (make: "Unknown operator").
    UnknownOperator,
    /// A comparison operator at the end of the condition (make: "Missing
    /// right-hand side of operator").
    MissingRightHandSide,
    /// The argument of a function such as `defined` is not followed by `)`
    /// (make: "Missing ')' after argument").
    UnclosedFunctionCall,
    /// A quoted string without its closing `"` (make: "Unfinished string
    /// literal").
    UnfinishedStringLiteral,
    /// A backslash at the end of an operand (make: "Unfinished backslash
    /// escape sequence").
    UnfinishedEscape,
    /// An unquoted left-hand side of a comparison that does not start with
    /// a variable reference or a digit.
    UnquotedLeftHandSide,
    /// A variable reference with a modifier that make does not know (make:
    /// "Unknown modifier").
    UnknownModifier,
    /// A malformed variable reference.
    Reference(ReferenceSyntaxErrorKind),
}

/// A syntax error in a BSD make conditional expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BsdConditionError {
    /// A description of the problem.
    pub message: String,
    /// The byte offset in the condition text at which the problem was found.
    pub offset: usize,
    pub(crate) kind: BsdConditionErrorKind,
}

impl BsdConditionError {
    /// The class of this error.
    pub fn kind(&self) -> BsdConditionErrorKind {
        self.kind
    }
}

impl fmt::Display for BsdConditionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} at offset {}", self.message, self.offset)
    }
}

impl std::error::Error for BsdConditionError {}

/// Parse the expression of a BSD make conditional directive, i.e. the text
/// following `.if`, `.elif`, `.ifdef`, `.ifmake` and so on.
///
/// The text should have line continuations collapsed and comments removed,
/// as [`crate::ConditionalBranch::condition`] returns it. As in make, `\#`
/// stands for `#`, and an unescaped `#` ends the condition.
///
/// # Example
/// ```
/// use makefile_lossless::{parse_bsd_condition, BsdCondition, BsdFunction, BsdOperand};
/// assert_eq!(
///     parse_bsd_condition("!empty(MACHINE_ARCH:Mmips*) || ${MKPIC} == no").unwrap(),
///     BsdCondition::Or(vec![
///         BsdCondition::Not(Box::new(BsdCondition::Call {
///             function: BsdFunction::Empty,
///             argument: "MACHINE_ARCH:Mmips*".to_string(),
///         })),
///         BsdCondition::Compare {
///             lhs: BsdOperand::VariableReference("${MKPIC}".to_string()),
///             op: makefile_lossless::BsdComparisonOp::Equal,
///             rhs: BsdOperand::Word("no".to_string()),
///         },
///     ])
/// );
/// assert!(parse_bsd_condition("${A} == ").is_err());
/// ```
pub fn parse_bsd_condition(text: &str) -> Result<BsdCondition, BsdConditionError> {
    parse(text, false)
}

fn parse(text: &str, left_unquoted_ok: bool) -> Result<BsdCondition, BsdConditionError> {
    let mut parser = Parser::new(text, left_unquoted_ok);
    let condition = parser.parse_or()?;
    parser.skip_whitespace();
    match parser.peek() {
        None | Some(b'#') => Ok(condition),
        Some(b')') => Err(parser.error(
            BsdConditionErrorKind::UnbalancedParenthesis,
            "unbalanced \")\"",
        )),
        Some(_) => Err(parser.error(
            BsdConditionErrorKind::UnexpectedText,
            "expected \"&&\", \"||\" or end of condition",
        )),
    }
}

/// Parse the condition of a `${cond:?then:else}` expression, as make does
/// for the `:?` modifier.
///
/// make expands the condition (the variable name of the expression) before
/// parsing it, so the caller should pass the expanded text. In this context
/// make accepts unquoted text on the left-hand side of a comparison, since
/// it cannot tell anymore whether that text came from a variable reference.
/// Otherwise the syntax is the same as for [`parse_bsd_condition`] and a
/// [`BsdCondition`] evaluates as for `.if`.
///
/// # Example
/// ```
/// use makefile_lossless::{
///     parse_bsd_condition, parse_bsd_if_else_condition, BsdComparisonOp, BsdCondition,
///     BsdOperand,
/// };
/// // `${${ACTIVE_CC} == "clang":?a:b}` with ACTIVE_CC set to gcc.
/// assert_eq!(
///     parse_bsd_if_else_condition(r#"gcc == "clang""#).unwrap(),
///     BsdCondition::Compare {
///         lhs: BsdOperand::Word("gcc".to_string()),
///         op: BsdComparisonOp::Equal,
///         rhs: BsdOperand::String("clang".to_string()),
///     }
/// );
/// assert!(parse_bsd_condition(r#"gcc == "clang""#).is_err());
/// ```
pub fn parse_bsd_if_else_condition(text: &str) -> Result<BsdCondition, BsdConditionError> {
    parse(text, true)
}

impl FromStr for BsdCondition {
    type Err = BsdConditionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_bsd_condition(s)
    }
}

/// Whether `s` is a number as make's condition parser accepts it: a decimal
/// or hexadecimal integer, or a decimal floating point number.
fn is_number(s: &str) -> bool {
    if let Some(hex) = s.strip_prefix("0x") {
        return !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit());
    }
    let s = s.strip_prefix(['+', '-']).unwrap_or(s);
    let (mantissa, exponent) = match s.find(['e', 'E']) {
        Some(i) => (&s[..i], Some(&s[i + 1..])),
        None => (s, None),
    };
    let (int, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let all_digits = |t: &str| t.bytes().all(|b| b.is_ascii_digit());
    let mantissa_ok = !(int.is_empty() && frac.is_empty()) && all_digits(int) && all_digits(frac);
    let exponent_ok = exponent.is_none_or(|e| {
        let e = e.strip_prefix(['+', '-']).unwrap_or(e);
        !e.is_empty() && all_digits(e)
    });
    mantissa_ok && exponent_ok
}

struct Parser {
    /// The condition with `\#` replaced by `#`.
    text: Vec<u8>,
    /// The offset in the original text of each byte of `text`, plus the end.
    offsets: Vec<usize>,
    pos: usize,
    /// Whether plain characters are allowed in an unquoted left-hand side.
    left_unquoted_ok: bool,
}

impl Parser {
    fn new(original: &str, left_unquoted_ok: bool) -> Self {
        let bytes = original.as_bytes();
        let mut text = Vec::with_capacity(bytes.len());
        let mut offsets = Vec::with_capacity(bytes.len() + 1);
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                if bytes[i + 1] != b'#' {
                    text.push(b'\\');
                    offsets.push(i);
                }
                text.push(bytes[i + 1]);
                offsets.push(i + 1);
                i += 2;
            } else {
                text.push(bytes[i]);
                offsets.push(i);
                i += 1;
            }
        }
        offsets.push(bytes.len());
        Self {
            text,
            offsets,
            pos: 0,
            left_unquoted_ok,
        }
    }

    fn error(&self, kind: BsdConditionErrorKind, message: impl Into<String>) -> BsdConditionError {
        self.error_at(self.pos, kind, message)
    }

    fn error_at(
        &self,
        pos: usize,
        kind: BsdConditionErrorKind,
        message: impl Into<String>,
    ) -> BsdConditionError {
        BsdConditionError {
            message: message.into(),
            offset: self.offsets[pos],
            kind,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.text.get(self.pos).copied()
    }

    fn peek_at(&self, pos: usize) -> Option<u8> {
        self.text.get(pos).copied()
    }

    /// The text between `start` and `end`. Both must be at character
    /// boundaries, which holds for positions of ASCII delimiters.
    fn slice(&self, start: usize, end: usize) -> String {
        String::from_utf8(self.text[start..end].to_vec())
            .expect("split at a non-character boundary")
    }

    fn skip_whitespace(&mut self) {
        while self.peek().is_some_and(|b| b.is_ascii_whitespace()) {
            self.pos += 1;
        }
    }

    fn parse_or(&mut self) -> Result<BsdCondition, BsdConditionError> {
        let mut alternatives = vec![self.parse_and()?];
        while self.skip_logical_operator(b'|')? {
            alternatives.push(self.parse_and()?);
        }
        Ok(if alternatives.len() == 1 {
            alternatives.remove(0)
        } else {
            BsdCondition::Or(alternatives)
        })
    }

    fn parse_and(&mut self) -> Result<BsdCondition, BsdConditionError> {
        let mut operands = vec![self.parse_term()?];
        while self.skip_logical_operator(b'&')? {
            operands.push(self.parse_term()?);
        }
        Ok(if operands.len() == 1 {
            operands.remove(0)
        } else {
            BsdCondition::And(operands)
        })
    }

    /// Skip `&&` or `||` if it is next, where `c` is `&` or `|`.
    fn skip_logical_operator(&mut self, c: u8) -> Result<bool, BsdConditionError> {
        self.skip_whitespace();
        if self.peek() != Some(c) {
            return Ok(false);
        }
        if self.peek_at(self.pos + 1) != Some(c) {
            return Err(self.error(
                BsdConditionErrorKind::UnknownOperator,
                format!("unknown operator \"{}\"", c as char),
            ));
        }
        self.pos += 2;
        Ok(true)
    }

    fn parse_term(&mut self) -> Result<BsdCondition, BsdConditionError> {
        self.skip_whitespace();
        match self.peek() {
            None | Some(b'#') => {
                Err(self.error(BsdConditionErrorKind::MissingOperand, "missing operand"))
            }
            Some(b'!') => {
                self.pos += 1;
                Ok(BsdCondition::Not(Box::new(self.parse_term()?)))
            }
            Some(b'(') => {
                let open = self.pos;
                self.pos += 1;
                let inner = self.parse_or()?;
                self.skip_whitespace();
                if self.peek() != Some(b')') {
                    return Err(self.error_at(
                        open,
                        BsdConditionErrorKind::UnclosedParenthesis,
                        "unclosed \"(\"",
                    ));
                }
                self.pos += 1;
                Ok(inner)
            }
            Some(b')') => Err(self.error(
                BsdConditionErrorKind::UnexpectedParenthesis,
                "unexpected \")\"",
            )),
            Some(c @ (b'&' | b'|')) => Err(self.error(
                BsdConditionErrorKind::UnexpectedOperator,
                format!("unexpected operator \"{}\"", c as char),
            )),
            Some(b'"' | b'$' | b'0'..=b'9' | b'-' | b'+') => self.parse_comparison(),
            Some(_) => match self.parse_call()? {
                Some(call) => Ok(call),
                None => self.parse_bare_word(),
            },
        }
    }

    /// Parse a function call, if the text at the current position is a
    /// function name followed by `(`.
    fn parse_call(&mut self) -> Result<Option<BsdCondition>, BsdConditionError> {
        let rest = &self.text[self.pos..];
        let Some(function) = BsdFunction::ALL
            .into_iter()
            .find(|f| rest.starts_with(f.name().as_bytes()))
        else {
            return Ok(None);
        };
        let mut open = self.pos + function.name().len();
        while self.peek_at(open).is_some_and(|b| b.is_ascii_whitespace()) {
            open += 1;
        }
        if self.peek_at(open) != Some(b'(') {
            return Ok(None);
        }
        let start = self.pos;
        self.pos = open;
        let argument = if function == BsdFunction::Empty {
            // The argument is parsed like the inside of `$(...)`.
            let expr = format!("${}", self.slice(open, self.text.len()));
            let close = self.scan_expression(open - 1, &expr)? - 1;
            let argument = self.slice(open + 1, close);
            self.pos = close + 1;
            argument
        } else {
            self.pos += 1;
            self.skip_whitespace();
            let argument = self.scan_word()?;
            self.skip_whitespace();
            if self.peek() != Some(b')') {
                return Err(self.error_at(
                    start,
                    BsdConditionErrorKind::UnclosedFunctionCall,
                    format!("missing \")\" after argument of \"{}\"", function),
                ));
            }
            self.pos += 1;
            argument
        };
        Ok(Some(BsdCondition::Call { function, argument }))
    }

    /// Parse a word that is not a function call and does not start like a
    /// quoted string, variable reference or number.
    fn parse_bare_word(&mut self) -> Result<BsdCondition, BsdConditionError> {
        let start = self.pos;
        let word = self.scan_word()?;
        let end = self.pos;
        self.skip_whitespace();
        if matches!(self.peek(), Some(b'=' | b'!' | b'<' | b'>')) {
            // As in make, reparse it as the left-hand side of a comparison,
            // which is usually an error.
            self.pos = start;
            return self.parse_comparison();
        }
        self.pos = end;
        Ok(BsdCondition::Bare(word))
    }

    /// Scan a word as used for function arguments and bare words: up to
    /// whitespace, `&` or `|`, or an unbalanced `)`.
    fn scan_word(&mut self) -> Result<String, BsdConditionError> {
        let start = self.pos;
        let mut depth = 0usize;
        while let Some(c) = self.peek() {
            match c {
                b'$' => {
                    self.pos = self.scan_variable_reference(self.pos)?;
                    continue;
                }
                b'&' | b'|' if depth == 0 => break,
                b'(' => depth += 1,
                b')' if depth == 0 => break,
                b')' => depth -= 1,
                c if c.is_ascii_whitespace() => break,
                _ => {}
            }
            self.pos += 1;
        }
        Ok(self.slice(start, self.pos))
    }

    /// Return the end of the variable reference starting with the `$` at
    /// `start`.
    fn scan_variable_reference(&self, start: usize) -> Result<usize, BsdConditionError> {
        match self.peek_at(start + 1) {
            Some(b'(' | b'{') => {}
            Some(_) => {
                // A single-character variable name, such as `$@` or `$$`.
                let len = std::str::from_utf8(&self.text[start + 1..])
                    .expect("split at a non-character boundary")
                    .chars()
                    .next()
                    .map_or(1, char::len_utf8);
                return Ok(start + 1 + len);
            }
            None => {
                return Err(self.error_at(
                    start,
                    BsdConditionErrorKind::Reference(ReferenceSyntaxErrorKind::MissingVariableName),
                    "incomplete variable reference",
                ))
            }
        }
        let text =
            std::str::from_utf8(&self.text[start..]).expect("split at a non-character boundary");
        self.scan_expression(start, text)
    }

    /// Return the end of the expression `text`, which starts at `start` with
    /// `$(` or `${`. As in make, where the expression ends depends on its
    /// modifiers, so it is found by parsing them.
    fn scan_expression(&self, start: usize, text: &str) -> Result<usize, BsdConditionError> {
        match ParsedReference::parse_prefix(text, MakefileVariant::BSDMake) {
            Ok((_, len)) => Ok(start + len),
            Err(ReferenceError::Syntax {
                offset,
                kind,
                message,
            }) => Err(self.error_at(
                start + offset,
                BsdConditionErrorKind::Reference(kind),
                message,
            )),
            Err(ReferenceError::UnknownModifier { offset, modifier }) => Err(self.error_at(
                start + offset,
                BsdConditionErrorKind::UnknownModifier,
                format!("unknown modifier ':{}'", modifier),
            )),
            Err(e @ ReferenceError::FunctionCall { .. }) => {
                unreachable!("function call in BSD make expression: {}", e)
            }
        }
    }

    /// Parse a leaf, optionally followed by a comparison operator and
    /// another leaf.
    fn parse_comparison(&mut self) -> Result<BsdCondition, BsdConditionError> {
        let lhs = self.parse_leaf(true)?;
        self.skip_whitespace();
        let Some(op) = self.parse_comparison_op() else {
            return Ok(BsdCondition::Value(lhs));
        };
        self.skip_whitespace();
        // Only the end of the condition is an error; an empty leaf before
        // `)` or another operator compares against the empty string.
        if self.peek().is_none() {
            return Err(self.error(
                BsdConditionErrorKind::MissingRightHandSide,
                format!("missing right-hand side of operator \"{}\"", op),
            ));
        }
        let rhs = self.parse_leaf(false)?;
        Ok(BsdCondition::Compare { lhs, op, rhs })
    }

    fn parse_comparison_op(&mut self) -> Option<BsdComparisonOp> {
        let (op, len) = match (self.peek()?, self.peek_at(self.pos + 1)) {
            (b'<', Some(b'=')) => (BsdComparisonOp::LessOrEqual, 2),
            (b'<', _) => (BsdComparisonOp::Less, 1),
            (b'>', Some(b'=')) => (BsdComparisonOp::GreaterOrEqual, 2),
            (b'>', _) => (BsdComparisonOp::Greater, 1),
            (b'=', Some(b'=')) => (BsdComparisonOp::Equal, 2),
            (b'!', Some(b'=')) => (BsdComparisonOp::NotEqual, 2),
            _ => return None,
        };
        self.pos += len;
        Some(op)
    }

    /// Parse a quoted string, or unquoted text up to whitespace, `!`, `=`,
    /// `<`, `>` or `)`.
    ///
    /// As in make, plain characters in an unquoted left-hand side are only
    /// allowed if it starts with a variable reference or a digit, unless
    /// `left_unquoted_ok` is set.
    fn parse_leaf(&mut self, is_lhs: bool) -> Result<BsdOperand, BsdConditionError> {
        let start = self.pos;
        let quoted = self.peek() == Some(b'"');
        if quoted {
            self.pos += 1;
        }
        let unquoted_text_ok = quoted
            || !is_lhs
            || self.left_unquoted_ok
            || matches!(self.peek(), Some(b'$' | b'0'..=b'9'));
        let mut value = Vec::new();
        // The end of the first variable reference, if the leaf starts with one.
        let mut first_reference_end = None;
        loop {
            match self.peek() {
                None if quoted => {
                    return Err(self.error_at(
                        start,
                        BsdConditionErrorKind::UnfinishedStringLiteral,
                        "unterminated string literal",
                    ));
                }
                None => break,
                Some(b'"') if quoted => {
                    self.pos += 1;
                    break;
                }
                Some(b'\\') => {
                    let Some(escaped) = self.peek_at(self.pos + 1) else {
                        return Err(self.error(
                            BsdConditionErrorKind::UnfinishedEscape,
                            "unfinished backslash escape sequence",
                        ));
                    };
                    if escaped == b'$' {
                        value.push(b'$');
                    }
                    value.push(escaped);
                    self.pos += 2;
                }
                Some(b'$') => {
                    let end = self.scan_variable_reference(self.pos)?;
                    if self.pos == start {
                        first_reference_end = Some(end);
                    }
                    value.extend_from_slice(&self.text[self.pos..end]);
                    self.pos = end;
                }
                Some(c)
                    if !quoted
                        && (c.is_ascii_whitespace()
                            || matches!(c, b'!' | b'=' | b'<' | b'>' | b')')) =>
                {
                    break
                }
                Some(_) if !unquoted_text_ok => {
                    return Err(self.error_at(
                        start,
                        BsdConditionErrorKind::UnquotedLeftHandSide,
                        "left-hand side of comparison must be a quoted string, number or \
                         variable reference",
                    ));
                }
                Some(c) => {
                    value.push(c);
                    self.pos += 1;
                }
            }
        }
        let value = String::from_utf8(value).expect("split at a non-character boundary");
        Ok(if quoted {
            BsdOperand::String(value)
        } else if first_reference_end == Some(self.pos) {
            BsdOperand::VariableReference(value)
        } else if !value.contains('$') && is_number(&value) {
            BsdOperand::Number(value)
        } else {
            BsdOperand::Word(value)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use BsdComparisonOp::*;
    use BsdCondition::*;

    fn parse(text: &str) -> BsdCondition {
        parse_bsd_condition(text).unwrap()
    }

    fn error(text: &str) -> (String, usize) {
        let err = parse_bsd_condition(text).unwrap_err();
        (err.message, err.offset)
    }

    fn call(function: BsdFunction, argument: &str) -> BsdCondition {
        Call {
            function,
            argument: argument.to_string(),
        }
    }

    fn defined(argument: &str) -> BsdCondition {
        call(BsdFunction::Defined, argument)
    }

    fn var(text: &str) -> BsdOperand {
        BsdOperand::VariableReference(text.to_string())
    }

    fn string(text: &str) -> BsdOperand {
        BsdOperand::String(text.to_string())
    }

    fn word(text: &str) -> BsdOperand {
        BsdOperand::Word(text.to_string())
    }

    fn number(text: &str) -> BsdOperand {
        BsdOperand::Number(text.to_string())
    }

    fn compare(lhs: BsdOperand, op: BsdComparisonOp, rhs: BsdOperand) -> BsdCondition {
        Compare { lhs, op, rhs }
    }

    fn not(c: BsdCondition) -> BsdCondition {
        Not(Box::new(c))
    }

    fn bare(text: &str) -> BsdCondition {
        Bare(text.to_string())
    }

    #[test]
    fn test_functions() {
        assert_eq!(parse("defined(VAR)"), defined("VAR"));
        assert_eq!(parse("make(install)"), call(BsdFunction::Make, "install"));
        assert_eq!(parse("empty(VAR)"), call(BsdFunction::Empty, "VAR"));
        assert_eq!(
            parse("exists(${.CURDIR}/../Makefile.inc)"),
            call(BsdFunction::Exists, "${.CURDIR}/../Makefile.inc")
        );
        assert_eq!(parse("target(all)"), call(BsdFunction::Target, "all"));
        assert_eq!(
            parse("commands(install)"),
            call(BsdFunction::Commands, "install")
        );
    }

    #[test]
    fn test_function_whitespace() {
        assert_eq!(parse("defined ( VAR )"), defined("VAR"));
        assert_eq!(parse("defined()"), defined(""));
        assert_eq!(parse("make(foo(bar))"), call(BsdFunction::Make, "foo(bar)"));
    }

    #[test]
    fn test_empty_with_modifiers() {
        assert_eq!(
            parse("empty(MACHINE_ARCH:Mmips*)"),
            call(BsdFunction::Empty, "MACHINE_ARCH:Mmips*")
        );
        assert_eq!(
            parse("empty(VAR:M*(foo)*:S/a b/c/)"),
            call(BsdFunction::Empty, "VAR:M*(foo)*:S/a b/c/")
        );
        assert_eq!(
            parse("empty(${NAME}:M${PAT})"),
            call(BsdFunction::Empty, "${NAME}:M${PAT}")
        );
        assert_eq!(
            parse("!empty(.MAKE.MODE:Mmeta)"),
            not(call(BsdFunction::Empty, ".MAKE.MODE:Mmeta"))
        );
    }

    #[test]
    fn test_function_argument_with_reference() {
        assert_eq!(
            parse("defined(${VAR:S/a)b/c/})"),
            defined("${VAR:S/a)b/c/}")
        );
        assert_eq!(
            parse("target(${A:S/ /_/g})"),
            call(BsdFunction::Target, "${A:S/ /_/g}")
        );
    }

    #[test]
    fn test_function_name_without_parenthesis_is_bare_word() {
        assert_eq!(parse("defined"), bare("defined"));
        assert_eq!(parse("definedness"), bare("definedness"));
        assert_eq!(parse("makefoo(x)"), bare("makefoo(x)"));
    }

    #[test]
    fn test_comparisons() {
        assert_eq!(
            parse("${A} == ${B}"),
            compare(var("${A}"), Equal, var("${B}"))
        );
        assert_eq!(
            parse("$(A) != \"b\""),
            compare(var("$(A)"), NotEqual, string("b"))
        );
        assert_eq!(parse("${A} < 1"), compare(var("${A}"), Less, number("1")));
        assert_eq!(
            parse("${A} <= 1"),
            compare(var("${A}"), LessOrEqual, number("1"))
        );
        assert_eq!(
            parse("${A} > 1"),
            compare(var("${A}"), Greater, number("1"))
        );
        assert_eq!(
            parse("${A} >= 1"),
            compare(var("${A}"), GreaterOrEqual, number("1"))
        );
    }

    #[test]
    fn test_comparison_without_spaces() {
        assert_eq!(
            parse("${UNDEF:Uundefined}!=undefined"),
            compare(var("${UNDEF:Uundefined}"), NotEqual, word("undefined"))
        );
        assert_eq!(
            parse("${A:U12345}>12345"),
            compare(var("${A:U12345}"), Greater, number("12345"))
        );
        assert_eq!(parse("(${A}==1)"), compare(var("${A}"), Equal, number("1")));
    }

    #[test]
    fn test_comparison_empty_rhs() {
        // As in make, a right-hand side that ends before the end of the
        // condition is the empty string.
        assert_eq!(parse("(${A} ==)"), compare(var("${A}"), Equal, word("")));
        assert_eq!(
            parse("(${A} != ) || 1"),
            Or(vec![
                compare(var("${A}"), NotEqual, word("")),
                Value(number("1"))
            ])
        );
    }

    #[test]
    fn test_operands() {
        assert_eq!(parse("1 == ${A}"), compare(number("1"), Equal, var("${A}")));
        assert_eq!(
            parse("${A} == 0x1F"),
            compare(var("${A}"), Equal, number("0x1F"))
        );
        assert_eq!(
            parse("${A} == -1.5e3"),
            compare(var("${A}"), Equal, number("-1.5e3"))
        );
        assert_eq!(parse("${A} == 1x"), compare(var("${A}"), Equal, word("1x")));
        assert_eq!(
            parse("${A} == .5"),
            compare(var("${A}"), Equal, number(".5"))
        );
        assert_eq!(
            parse("0x${HEX} == 57005"),
            compare(word("0x${HEX}"), Equal, number("57005"))
        );
        assert_eq!(
            parse("${A}x == \"${B}x\""),
            compare(word("${A}x"), Equal, string("${B}x"))
        );
        assert_eq!(
            parse("${A} == x${B}y"),
            compare(var("${A}"), Equal, word("x${B}y"))
        );
    }

    #[test]
    fn test_quoted_strings() {
        assert_eq!(
            parse(r#""a b" == "c\"d\\e""#),
            compare(string("a b"), Equal, string("c\"d\\e"))
        );
        assert_eq!(
            parse(r#"${A} == "a&&b || !c)""#),
            compare(var("${A}"), Equal, string("a&&b || !c)"))
        );
        assert_eq!(
            parse(r#"${A} == "\$x""#),
            compare(var("${A}"), Equal, string("$$x"))
        );
        assert_eq!(
            parse(r#""unquoted\"quoted" != unquoted"quoted"#),
            compare(
                string("unquoted\"quoted"),
                NotEqual,
                word("unquoted\"quoted")
            )
        );
        assert_eq!(
            parse(r#"${A} == "${B:S/"/x/}""#),
            compare(var("${A}"), Equal, string("${B:S/\"/x/}"))
        );
    }

    #[test]
    fn test_variable_reference_with_special_characters() {
        assert_eq!(
            parse("${A:S/)/x/} == ${B:M*&&*}"),
            compare(var("${A:S/)/x/}"), Equal, var("${B:M*&&*}"))
        );
        assert_eq!(
            parse("${A:Ufoo bar!=baz} != ${B:N!}"),
            compare(var("${A:Ufoo bar!=baz}"), NotEqual, var("${B:N!}"))
        );
        assert_eq!(
            parse("${${NAME}_FLAGS:M-O*}"),
            Value(var("${${NAME}_FLAGS:M-O*}"))
        );
        assert_eq!(
            parse("$(A:S/(x)/y/) == $(B)"),
            compare(var("$(A:S/(x)/y/)"), Equal, var("$(B)"))
        );
        assert_eq!(parse("${A:S/\\}/x/}"), Value(var("${A:S/\\}/x/}")));
        assert_eq!(parse("$X == $@"), compare(var("$X"), Equal, var("$@")));
    }

    #[test]
    fn test_variable_reference_extent_follows_modifiers() {
        assert_eq!(
            parse("${A:S/{/x/} == x"),
            compare(var("${A:S/{/x/}"), Equal, word("x"))
        );
        assert_eq!(
            parse("${A:S,},x,} == x"),
            compare(var("${A:S,},x,}"), Equal, word("x"))
        );
        assert_eq!(
            parse("${A:C/[}]/x/} == x"),
            compare(var("${A:C/[}]/x/}"), Equal, word("x"))
        );
        assert_eq!(
            parse("$(A:S/(/x/) == x"),
            compare(var("$(A:S/(/x/)"), Equal, word("x"))
        );
        assert_eq!(
            parse("${A:S/${B}/{/} == x"),
            compare(var("${A:S/${B}/{/}"), Equal, word("x"))
        );
        assert_eq!(parse("${A:M*\\}*}"), Value(var("${A:M*\\}*}")));
        assert_eq!(parse("defined(${A:S/{/x/})"), defined("${A:S/{/x/}"));
        assert_eq!(
            parse("!empty(A:S/(/x/)"),
            not(call(BsdFunction::Empty, "A:S/(/x/"))
        );
        assert_eq!(
            error("!empty(A:M{*)"),
            ("unclosed expression, expecting ')'".to_string(), 13)
        );
        assert_eq!(
            error("${A:Z} == x"),
            ("unknown modifier ':Z'".to_string(), 4)
        );
    }

    #[test]
    fn test_bare_operand() {
        assert_eq!(parse("${FOO}"), Value(var("${FOO}")));
        assert_eq!(parse("0"), Value(number("0")));
        assert_eq!(parse("\"\""), Value(string("")));
        assert_eq!(parse("0${:Ux01}"), Value(word("0${:Ux01}")));
        assert_eq!(parse("${A}&&${B}"), Value(word("${A}&&${B}")));
    }

    #[test]
    fn test_bare_word() {
        assert_eq!(parse("foo"), bare("foo"));
        assert_eq!(parse("V${:UA}R"), bare("V${:UA}R"));
        assert_eq!(parse("foo.o"), bare("foo.o"));
        assert_eq!(parse("a==b"), bare("a==b"));
        assert_eq!(parse("\\\\"), bare("\\\\"));
    }

    #[test]
    fn test_ifdef_style_conditions() {
        assert_eq!(parse("A || B"), Or(vec![bare("A"), bare("B")]));
        assert_eq!(parse("!A && B"), And(vec![not(bare("A")), bare("B")]));
        assert_eq!(
            parse("install || make(all)"),
            Or(vec![bare("install"), call(BsdFunction::Make, "all")])
        );
    }

    #[test]
    fn test_logical_operators() {
        assert_eq!(
            parse("a && b && c"),
            And(vec![bare("a"), bare("b"), bare("c")])
        );
        assert_eq!(
            parse("a || b || c"),
            Or(vec![bare("a"), bare("b"), bare("c")])
        );
        assert_eq!(parse("!!a"), not(not(bare("a"))));
        assert_eq!(parse("a&&b||c"), parse("a && b || c"));
    }

    #[test]
    fn test_precedence() {
        assert_eq!(
            parse("a || b && c"),
            Or(vec![bare("a"), And(vec![bare("b"), bare("c")])])
        );
        assert_eq!(
            parse("a && b || c"),
            Or(vec![And(vec![bare("a"), bare("b")]), bare("c")])
        );
        assert_eq!(parse("!a && b"), And(vec![not(bare("a")), bare("b")]));
        assert_eq!(
            parse("!a || !b && c"),
            Or(vec![not(bare("a")), And(vec![not(bare("b")), bare("c")])])
        );
        assert_eq!(
            parse("!${A} == 1"),
            not(compare(var("${A}"), Equal, number("1")))
        );
    }

    #[test]
    fn test_parentheses() {
        assert_eq!(
            parse("(a || b) && c"),
            And(vec![Or(vec![bare("a"), bare("b")]), bare("c")])
        );
        assert_eq!(parse("!(a && b)"), not(And(vec![bare("a"), bare("b")])));
        assert_eq!(parse("((a))"), bare("a"));
        assert_eq!(
            parse("(a && b) && c"),
            And(vec![And(vec![bare("a"), bare("b")]), bare("c")])
        );
        assert_eq!(parse("( defined(A) )"), defined("A"));
    }

    #[test]
    fn test_netbsd_expressions() {
        assert_eq!(
            parse("defined(MKMAN) && ${MKMAN} != \"no\""),
            And(vec![
                defined("MKMAN"),
                compare(var("${MKMAN}"), NotEqual, string("no"))
            ])
        );
        assert_eq!(
            parse("!empty(MACHINE_ARCH:Mmips*) || ${MKPIC} == \"no\""),
            Or(vec![
                not(call(BsdFunction::Empty, "MACHINE_ARCH:Mmips*")),
                compare(var("${MKPIC}"), Equal, string("no"))
            ])
        );
        assert_eq!(
            parse("${USE_FORT:Uno} != \"no\""),
            compare(var("${USE_FORT:Uno}"), NotEqual, string("no"))
        );
        assert_eq!(parse("make(install)"), call(BsdFunction::Make, "install"));
        assert_eq!(
            parse("${MACHINE_ARCH} == \"x86_64\" || ${MACHINE_ARCH} == \"i386\""),
            Or(vec![
                compare(var("${MACHINE_ARCH}"), Equal, string("x86_64")),
                compare(var("${MACHINE_ARCH}"), Equal, string("i386")),
            ])
        );
        assert_eq!(
            parse("${HAVE_GCC:U0} >= 10 && !defined(NOGCCERROR)"),
            And(vec![
                compare(var("${HAVE_GCC:U0}"), GreaterOrEqual, number("10")),
                not(defined("NOGCCERROR")),
            ])
        );
        assert_eq!(
            parse("(${MKLIBCXX} == \"yes\" && ${MKGCC} != \"no\") || defined(HAVE_LLVM)"),
            Or(vec![
                And(vec![
                    compare(var("${MKLIBCXX}"), Equal, string("yes")),
                    compare(var("${MKGCC}"), NotEqual, string("no")),
                ]),
                defined("HAVE_LLVM"),
            ])
        );
        assert_eq!(
            parse("!target(__initialized__)"),
            not(call(BsdFunction::Target, "__initialized__"))
        );
        assert_eq!(
            parse("exists(${NETBSDSRCDIR}/sys/arch/${MACHINE}/include)"),
            call(
                BsdFunction::Exists,
                "${NETBSDSRCDIR}/sys/arch/${MACHINE}/include"
            )
        );
    }

    #[test]
    fn test_comment() {
        assert_eq!(parse("0 # comment"), Value(number("0")));
        assert_eq!(parse("0 \\# comment"), Value(number("0")));
        assert_eq!(
            parse("${A:M\\#*} == \\#x"),
            compare(var("${A:M#*}"), Equal, word("#x"))
        );
    }

    #[test]
    fn test_whitespace() {
        assert_eq!(parse("  a  "), bare("a"));
        assert_eq!(
            parse("\t${A}\t==\t1\t"),
            compare(var("${A}"), Equal, number("1"))
        );
    }

    #[test]
    fn test_errors() {
        assert_eq!(error(""), ("missing operand".to_string(), 0));
        assert_eq!(error("   "), ("missing operand".to_string(), 3));
        assert_eq!(error("a &&"), ("missing operand".to_string(), 4));
        assert_eq!(error("|| a"), ("unexpected operator \"|\"".to_string(), 0));
        assert_eq!(error("!"), ("missing operand".to_string(), 1));
        assert_eq!(error("a & b"), ("unknown operator \"&\"".to_string(), 2));
        assert_eq!(error("a | b"), ("unknown operator \"|\"".to_string(), 2));
        assert_eq!(error("(a"), ("unclosed \"(\"".to_string(), 0));
        assert_eq!(error("a)"), ("unbalanced \")\"".to_string(), 1));
        assert_eq!(error("()"), ("unexpected \")\"".to_string(), 1));
        assert_eq!(
            error("a b"),
            ("expected \"&&\", \"||\" or end of condition".to_string(), 2)
        );
        assert_eq!(
            error("${A} == "),
            ("missing right-hand side of operator \"==\"".to_string(), 8)
        );
        assert_eq!(
            error("${A} = b"),
            ("expected \"&&\", \"||\" or end of condition".to_string(), 5)
        );
        assert_eq!(
            error("${A"),
            ("unclosed expression, expecting '}'".to_string(), 3)
        );
        assert_eq!(
            error("defined(${A)"),
            ("unclosed expression, expecting '}'".to_string(), 12)
        );
        assert_eq!(
            error("${A} == \"b"),
            ("unterminated string literal".to_string(), 8)
        );
        assert_eq!(
            error("${A} == b\\"),
            ("unfinished backslash escape sequence".to_string(), 9)
        );
        assert_eq!(
            error("defined(A B)"),
            ("missing \")\" after argument of \"defined\"".to_string(), 0)
        );
        assert_eq!(
            error("empty(A"),
            ("unclosed expression, expecting ')'".to_string(), 7)
        );
        assert_eq!(
            error("${A} == $"),
            ("incomplete variable reference".to_string(), 8)
        );
    }

    #[test]
    fn test_error_kinds() {
        use BsdConditionErrorKind::*;
        let cases = [
            ("", MissingOperand),
            ("a &&", MissingOperand),
            ("()", UnexpectedParenthesis),
            ("a)", UnbalancedParenthesis),
            ("(a", UnclosedParenthesis),
            ("|| a", UnexpectedOperator),
            ("a b", UnexpectedText),
            ("a & b", UnknownOperator),
            ("${A} == ", MissingRightHandSide),
            ("defined(A B)", UnclosedFunctionCall),
            ("${A} == \"b", UnfinishedStringLiteral),
            ("${A} == b\\", UnfinishedEscape),
            ("left == right", UnquotedLeftHandSide),
            ("${A:Z} == x", UnknownModifier),
            (
                "${A",
                Reference(ReferenceSyntaxErrorKind::UnclosedExpression),
            ),
            (
                "${A} == $",
                Reference(ReferenceSyntaxErrorKind::MissingVariableName),
            ),
            (
                "empty(A:S/a/b)",
                Reference(ReferenceSyntaxErrorKind::UnfinishedModifier),
            ),
        ];
        for (text, expected) in cases {
            assert_eq!(
                parse_bsd_condition(text).unwrap_err().kind(),
                expected,
                "{}",
                text
            );
        }
    }

    #[test]
    fn test_unquoted_left_hand_side_is_error() {
        let message = "left-hand side of comparison must be a quoted string, number or \
                       variable reference"
            .to_string();
        assert_eq!(error("left == right"), (message.clone(), 0));
        assert_eq!(error("a || left != right"), (message.clone(), 5));
        assert_eq!(error("-1"), (message.clone(), 0));
        assert_eq!(error("!+1"), (message.clone(), 1));
        assert_eq!(error("x${:Uvalue} == \"\""), (message, 0));
    }

    fn parse_if_else(text: &str) -> BsdCondition {
        parse_bsd_if_else_condition(text).unwrap()
    }

    fn if_else_error(text: &str) -> (String, usize) {
        let err = parse_bsd_if_else_condition(text).unwrap_err();
        (err.message, err.offset)
    }

    #[test]
    fn test_if_else_unquoted_left_hand_side() {
        assert_eq!(
            parse_if_else("gcc == \"clang\""),
            compare(word("gcc"), Equal, string("clang"))
        );
        assert_eq!(
            parse_if_else("a || left != right"),
            Or(vec![
                bare("a"),
                compare(word("left"), NotEqual, word("right"))
            ])
        );
        assert_eq!(
            parse_if_else("x${:Uvalue} == \"\""),
            compare(word("x${:Uvalue}"), Equal, string(""))
        );
        // From varmod-ifelse.mk; "no >= 10" is only an error when evaluated.
        assert_eq!(
            parse_if_else("string == \"literal\" || no >= 10"),
            Or(vec![
                compare(word("string"), Equal, string("literal")),
                compare(word("no"), GreaterOrEqual, number("10")),
            ])
        );
        assert_eq!(parse_if_else("-1"), Value(number("-1")));
        assert_eq!(parse_if_else("!+1"), not(Value(number("+1"))));
        assert_eq!(parse_if_else("+\t\t"), Value(word("+")));
    }

    #[test]
    fn test_if_else_same_as_if() {
        // Bare words that are not compared are still passed to defined().
        assert_eq!(parse_if_else("*\t"), bare("*"));
        assert_eq!(parse_if_else("A"), bare("A"));
        assert_eq!(
            parse_if_else(" ${VAR} == value"),
            compare(var("${VAR}"), Equal, word("value"))
        );
        assert_eq!(
            parse_if_else(" (\"\" != \"\") "),
            compare(string(""), NotEqual, string(""))
        );
    }

    #[test]
    fn test_if_else_errors() {
        // All of these are a "Bad condition" in varmod-ifelse.mk.
        assert_eq!(
            if_else_error("bare words == \"literal\""),
            ("expected \"&&\", \"||\" or end of condition".to_string(), 5)
        );
        assert_eq!(
            if_else_error(" == \"\""),
            ("expected \"&&\", \"||\" or end of condition".to_string(), 4)
        );
        assert_eq!(
            if_else_error("1 == == 2"),
            ("expected \"&&\", \"||\" or end of condition".to_string(), 5)
        );
        assert_eq!(
            if_else_error("string == \"literal\" &&  >= 10"),
            (
                "expected \"&&\", \"||\" or end of condition".to_string(),
                27
            )
        );
        assert_eq!(if_else_error("\t"), ("missing operand".to_string(), 1));
        assert_eq!(
            if_else_error(" < 0 "),
            ("expected \"&&\", \"||\" or end of condition".to_string(), 3)
        );
    }

    #[test]
    fn test_escaped_left_hand_side() {
        // make only rejects plain characters in an unquoted left-hand side.
        assert_eq!(
            parse("\\x${:Uvalue} == \"xvalue\""),
            compare(word("x${:Uvalue}"), Equal, string("xvalue"))
        );
    }

    #[test]
    fn test_from_str() {
        assert_eq!("defined(A)".parse::<BsdCondition>(), Ok(defined("A")));
    }

    #[test]
    fn test_error_display() {
        assert_eq!(
            parse_bsd_condition("(a").unwrap_err().to_string(),
            "unclosed \"(\" at offset 0"
        );
    }

    #[test]
    fn test_operand_accessors() {
        assert_eq!(string("a").text(), "a");
        assert!(string("a").is_quoted());
        assert!(!var("${A}").is_quoted());
        assert!(!number("1").is_quoted());
        assert!(!word("a").is_quoted());
    }

    #[test]
    fn test_names() {
        assert_eq!(BsdFunction::Commands.to_string(), "commands");
        assert_eq!(GreaterOrEqual.to_string(), ">=");
    }

    #[test]
    fn test_is_number() {
        for s in [
            "0", "12", "-1", "+1", "0x1f", "1.5", ".5", "5.", "1e3", "1E-3",
        ] {
            assert!(is_number(s), "{s}");
        }
        for s in [
            "", "0x", "0xg", "1x", "e3", "1e", ".", "inf", "nan", "1.2.3", "-",
        ] {
            assert!(!is_number(s), "{s}");
        }
    }
}
