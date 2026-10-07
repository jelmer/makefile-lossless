//! Parser for the expressions in nmake's `!IF` and `!ELSEIF` directives.
//!
//! The grammar follows Microsoft's documentation of makefile preprocessing,
//! with these operators from the lowest to the highest precedence:
//!
//! ```text
//! ||
//! &&
//! &  ^  |
//! ==  !=
//! <=  >=  <  >
//! <<  >>
//! +  -
//! *  /  %
//! !  ~  -                   (unary)
//! DEFINED(macro)  EXIST(path)
//! ```

use crate::reference::MAX_DEPTH;
use std::fmt;
use std::str::FromStr;

/// A parsed nmake preprocessing expression, as in `!IF` and `!ELSEIF`.
///
/// Operands are kept as unexpanded text; expanding macros, running
/// commands and evaluating the result is up to the caller. nmake evaluates
/// expressions with 32-bit signed integer arithmetic, and compares strings
/// with `==` and `!=`.
///
/// # Example
/// ```
/// use makefile_lossless::{parse_nmake_condition, NmakeBinaryOp, NmakeCondition};
/// assert_eq!(
///     parse_nmake_condition(r#"DEFINED(CFG) && "$(CFG)" == "Release""#).unwrap(),
///     NmakeCondition::Binary {
///         lhs: Box::new(NmakeCondition::Defined("CFG".to_string())),
///         op: NmakeBinaryOp::And,
///         rhs: Box::new(NmakeCondition::Binary {
///             lhs: Box::new(NmakeCondition::String("$(CFG)".to_string())),
///             op: NmakeBinaryOp::Equal,
///             rhs: Box::new(NmakeCondition::String("Release".to_string())),
///         }),
///     }
/// );
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NmakeCondition {
    /// An integer constant, written in decimal, octal (with a leading `0`)
    /// or hexadecimal (with a leading `0x`).
    Integer(i64),
    /// The unexpanded text of a string constant, without the double quotes.
    String(String),
    /// Unquoted text with macro invocations in it, such as `$(VERSION)`.
    Macro(String),
    /// The unexpanded text of a command between `[` and `]`, which stands
    /// for its exit code.
    Command(String),
    /// `DEFINED(macro)`, with the name of the macro.
    Defined(String),
    /// `EXIST(path)`, with the path, without any double quotes around it.
    Exist(String),
    /// A unary operator applied to an operand, such as `!DEFINED(X)`.
    Unary {
        /// The operator.
        op: NmakeUnaryOp,
        /// The operand.
        operand: Box<NmakeCondition>,
    },
    /// A binary operator applied to two operands, such as `$(X) + 1`.
    Binary {
        /// The left-hand side.
        lhs: Box<NmakeCondition>,
        /// The operator.
        op: NmakeBinaryOp,
        /// The right-hand side.
        rhs: Box<NmakeCondition>,
    },
}

impl FromStr for NmakeCondition {
    type Err = NmakeConditionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_nmake_condition(s)
    }
}

/// A unary operator in an nmake preprocessing expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NmakeUnaryOp {
    /// `!`, logical NOT.
    Not,
    /// `~`, one's complement.
    Complement,
    /// `-`, negation.
    Negate,
}

impl NmakeUnaryOp {
    /// The operator as written in a makefile.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Not => "!",
            Self::Complement => "~",
            Self::Negate => "-",
        }
    }
}

impl fmt::Display for NmakeUnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A binary operator in an nmake preprocessing expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NmakeBinaryOp {
    /// `*`
    Multiply,
    /// `/`
    Divide,
    /// `%`
    Remainder,
    /// `+`
    Add,
    /// `-`
    Subtract,
    /// `<<`
    ShiftLeft,
    /// `>>`
    ShiftRight,
    /// `<=`
    LessOrEqual,
    /// `>=`
    GreaterOrEqual,
    /// `<`
    Less,
    /// `>`
    Greater,
    /// `==`, which also compares strings.
    Equal,
    /// `!=`, which also compares strings.
    NotEqual,
    /// `&`, bitwise AND.
    BitAnd,
    /// `^`, bitwise XOR, which is written `^^` in a makefile since `^` is
    /// the escape character.
    BitXor,
    /// `|`, bitwise OR.
    BitOr,
    /// `&&`, logical AND.
    And,
    /// `||`, logical OR.
    Or,
}

/// The binary operators, longest first so that `<<` is not read as `<`.
const BINARY_OPERATORS: [NmakeBinaryOp; 18] = [
    NmakeBinaryOp::ShiftLeft,
    NmakeBinaryOp::ShiftRight,
    NmakeBinaryOp::LessOrEqual,
    NmakeBinaryOp::GreaterOrEqual,
    NmakeBinaryOp::Equal,
    NmakeBinaryOp::NotEqual,
    NmakeBinaryOp::And,
    NmakeBinaryOp::Or,
    NmakeBinaryOp::Multiply,
    NmakeBinaryOp::Divide,
    NmakeBinaryOp::Remainder,
    NmakeBinaryOp::Add,
    NmakeBinaryOp::Subtract,
    NmakeBinaryOp::Less,
    NmakeBinaryOp::Greater,
    NmakeBinaryOp::BitAnd,
    NmakeBinaryOp::BitXor,
    NmakeBinaryOp::BitOr,
];

/// The number of precedence levels of the binary operators.
const PRECEDENCE_LEVELS: u8 = 8;

impl NmakeBinaryOp {
    /// The operator as nmake reads it, after escapes have been removed.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Multiply => "*",
            Self::Divide => "/",
            Self::Remainder => "%",
            Self::Add => "+",
            Self::Subtract => "-",
            Self::ShiftLeft => "<<",
            Self::ShiftRight => ">>",
            Self::LessOrEqual => "<=",
            Self::GreaterOrEqual => ">=",
            Self::Less => "<",
            Self::Greater => ">",
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::BitAnd => "&",
            Self::BitXor => "^",
            Self::BitOr => "|",
            Self::And => "&&",
            Self::Or => "||",
        }
    }

    /// How tightly the operator binds: operators with a higher precedence
    /// are applied first.
    fn precedence(&self) -> u8 {
        match self {
            Self::Or => 0,
            Self::And => 1,
            Self::BitAnd | Self::BitXor | Self::BitOr => 2,
            Self::Equal | Self::NotEqual => 3,
            Self::LessOrEqual | Self::GreaterOrEqual | Self::Less | Self::Greater => 4,
            Self::ShiftLeft | Self::ShiftRight => 5,
            Self::Add | Self::Subtract => 6,
            Self::Multiply | Self::Divide | Self::Remainder => 7,
        }
    }
}

impl fmt::Display for NmakeBinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The class of an [`NmakeConditionError`].
///
/// Use this rather than matching on error messages, which are meant for
/// humans and may change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum NmakeConditionErrorKind {
    /// The expression or an operand of an operator is missing.
    MissingOperand,
    /// A `(` without a matching `)`.
    UnclosedParenthesis,
    /// A string constant without its closing `"`.
    UnfinishedString,
    /// A command without its closing `]`.
    UnclosedCommand,
    /// A macro invocation without its closing `)`.
    UnclosedMacro,
    /// `DEFINED` or `EXIST` not followed by an argument in parentheses.
    InvalidFunctionCall,
    /// A number that is malformed or does not fit in 32 bits.
    InvalidNumber,
    /// Unquoted text that is not a number, a macro invocation or an
    /// operator.
    UnexpectedText,
    /// Parentheses or unary operators are nested more deeply than this
    /// crate supports.
    TooDeeplyNested,
}

/// A syntax error in an nmake preprocessing expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NmakeConditionError {
    /// A description of the problem.
    pub message: String,
    /// The byte offset in the expression at which the problem was found.
    pub offset: usize,
    kind: NmakeConditionErrorKind,
}

impl NmakeConditionError {
    /// The class of this error.
    pub fn kind(&self) -> NmakeConditionErrorKind {
        self.kind
    }
}

impl fmt::Display for NmakeConditionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} at offset {}", self.message, self.offset)
    }
}

impl std::error::Error for NmakeConditionError {}

/// Parse the expression of an nmake `!IF` or `!ELSEIF` directive.
///
/// The text should have line continuations collapsed, comments removed and
/// carets unescaped, as [`crate::ConditionalBranch::condition`] returns it,
/// so that the XOR operator written `^^` is a single `^`.
///
/// # Example
/// ```
/// use makefile_lossless::{parse_nmake_condition, NmakeCondition, NmakeUnaryOp};
/// assert_eq!(
///     parse_nmake_condition("!EXIST(\"out dir\")").unwrap(),
///     NmakeCondition::Unary {
///         op: NmakeUnaryOp::Not,
///         operand: Box::new(NmakeCondition::Exist("out dir".to_string())),
///     }
/// );
/// assert!(parse_nmake_condition("$(X) ==").is_err());
/// ```
pub fn parse_nmake_condition(text: &str) -> Result<NmakeCondition, NmakeConditionError> {
    let mut parser = Parser { text, pos: 0 };
    let condition = parser.parse_binary(0, 0)?;
    parser.skip_whitespace();
    if parser.pos < text.len() {
        return Err(parser.error(
            NmakeConditionErrorKind::UnexpectedText,
            format!("Unexpected {:?}", parser.rest()),
        ));
    }
    Ok(condition)
}

struct Parser<'a> {
    text: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn rest(&self) -> &'a str {
        &self.text[self.pos..]
    }

    fn skip_whitespace(&mut self) {
        let rest = self.rest();
        self.pos += rest.len() - rest.trim_start_matches([' ', '\t']).len();
    }

    fn error(&self, kind: NmakeConditionErrorKind, message: String) -> NmakeConditionError {
        NmakeConditionError {
            message,
            offset: self.pos,
            kind,
        }
    }

    fn check_depth(&self, depth: usize) -> Result<(), NmakeConditionError> {
        if depth > MAX_DEPTH {
            return Err(self.error(
                NmakeConditionErrorKind::TooDeeplyNested,
                "Expression nested too deeply".to_string(),
            ));
        }
        Ok(())
    }

    /// Parse operands joined by binary operators of precedence `level` or
    /// higher, which associate from left to right.
    fn parse_binary(
        &mut self,
        level: u8,
        depth: usize,
    ) -> Result<NmakeCondition, NmakeConditionError> {
        if level == PRECEDENCE_LEVELS {
            return self.parse_unary(depth);
        }
        let mut lhs = self.parse_binary(level + 1, depth)?;
        loop {
            self.skip_whitespace();
            let Some(op) = BINARY_OPERATORS
                .into_iter()
                .find(|op| self.rest().starts_with(op.as_str()))
                .filter(|op| op.precedence() == level)
            else {
                return Ok(lhs);
            };
            self.pos += op.as_str().len();
            let rhs = self.parse_binary(level + 1, depth)?;
            lhs = NmakeCondition::Binary {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            };
        }
    }

    fn parse_unary(&mut self, depth: usize) -> Result<NmakeCondition, NmakeConditionError> {
        self.check_depth(depth)?;
        self.skip_whitespace();
        let op = match self.rest().chars().next() {
            // `!=` is not an operand.
            Some('!') if !self.rest().starts_with("!=") => NmakeUnaryOp::Not,
            Some('~') => NmakeUnaryOp::Complement,
            Some('-') => NmakeUnaryOp::Negate,
            _ => return self.parse_primary(depth),
        };
        self.pos += 1;
        let operand = self.parse_unary(depth + 1)?;
        Ok(NmakeCondition::Unary {
            op,
            operand: Box::new(operand),
        })
    }

    fn parse_primary(&mut self, depth: usize) -> Result<NmakeCondition, NmakeConditionError> {
        self.skip_whitespace();
        let rest = self.rest();
        match rest.chars().next() {
            None => Err(self.error(
                NmakeConditionErrorKind::MissingOperand,
                "Missing operand".to_string(),
            )),
            Some('(') => {
                let start = self.pos;
                self.pos += 1;
                let condition = self.parse_binary(0, depth + 1)?;
                self.skip_whitespace();
                if !self.rest().starts_with(')') {
                    self.pos = start;
                    return Err(self.error(
                        NmakeConditionErrorKind::UnclosedParenthesis,
                        "Missing ')'".to_string(),
                    ));
                }
                self.pos += 1;
                Ok(condition)
            }
            Some('"') => {
                let end = rest[1..].find('"').ok_or_else(|| {
                    self.error(
                        NmakeConditionErrorKind::UnfinishedString,
                        "Missing closing '\"'".to_string(),
                    )
                })?;
                self.pos += end + 2;
                Ok(NmakeCondition::String(rest[1..end + 1].to_string()))
            }
            Some('[') => {
                let end = rest.find(']').ok_or_else(|| {
                    self.error(
                        NmakeConditionErrorKind::UnclosedCommand,
                        "Missing closing ']'".to_string(),
                    )
                })?;
                self.pos += end + 1;
                Ok(NmakeCondition::Command(rest[1..end].to_string()))
            }
            Some(_) => self.parse_word(),
        }
    }

    /// Parse a function call, number or text with macro invocations.
    fn parse_word(&mut self) -> Result<NmakeCondition, NmakeConditionError> {
        let start = self.pos;
        let text = self.text;
        let mut end = start;
        while let Some(c) = text[end..].chars().next() {
            match c {
                '$' => end = self.macro_end(end)?,
                ' ' | '\t' | '(' | ')' | '"' | '[' | ']' | '!' | '~' | '*' | '/' | '%' | '+'
                | '-' | '<' | '>' | '=' | '&' | '^' | '|' => break,
                c => end += c.len_utf8(),
            }
        }
        let word = &text[start..end];
        if word.is_empty() {
            return Err(self.error(
                NmakeConditionErrorKind::MissingOperand,
                format!("Expected an operand before {:?}", self.rest()),
            ));
        }
        // TODO: Check whether nmake takes `defined` and `exist` in any case,
        // like the directives.
        let function = match word.to_ascii_uppercase().as_str() {
            "DEFINED" => Some(NmakeCondition::Defined as fn(String) -> NmakeCondition),
            "EXIST" => Some(NmakeCondition::Exist as fn(String) -> NmakeCondition),
            _ => None,
        };
        if let Some(function) = function {
            self.pos = end;
            return self.parse_call(word, function);
        }
        if word.contains('$') {
            self.pos = end;
            return Ok(NmakeCondition::Macro(word.to_string()));
        }
        // TODO: Check how nmake handles other unquoted text.
        let value = parse_integer(word).ok_or_else(|| {
            self.error(
                if word.starts_with(|c: char| c.is_ascii_digit()) {
                    NmakeConditionErrorKind::InvalidNumber
                } else {
                    NmakeConditionErrorKind::UnexpectedText
                },
                format!("{word:?} is not a number, string or macro invocation"),
            )
        })?;
        self.pos = end;
        Ok(NmakeCondition::Integer(value))
    }

    /// The end of the macro invocation starting with the `$` at `start`.
    fn macro_end(&self, start: usize) -> Result<usize, NmakeConditionError> {
        let after = &self.text[start + 1..];
        let unclosed = || NmakeConditionError {
            message: "Missing ')' after macro invocation".to_string(),
            offset: start,
            kind: NmakeConditionErrorKind::UnclosedMacro,
        };
        match after.chars().next() {
            Some('(') => {
                let mut depth = 0usize;
                for (i, c) in after.char_indices() {
                    match c {
                        '(' => depth += 1,
                        ')' => {
                            depth -= 1;
                            if depth == 0 {
                                return Ok(start + 1 + i + 1);
                            }
                        }
                        _ => {}
                    }
                }
                Err(unclosed())
            }
            Some(c) => Ok(start + 1 + c.len_utf8()),
            None => Err(unclosed()),
        }
    }

    /// Parse the argument in parentheses of the function `name`.
    fn parse_call(
        &mut self,
        name: &str,
        function: fn(String) -> NmakeCondition,
    ) -> Result<NmakeCondition, NmakeConditionError> {
        self.skip_whitespace();
        let invalid = |parser: &Self| {
            parser.error(
                NmakeConditionErrorKind::InvalidFunctionCall,
                format!("Expected an argument in parentheses after {name}"),
            )
        };
        let rest = self.rest();
        if !rest.starts_with('(') {
            return Err(invalid(self));
        }
        let mut end = 1;
        while let Some(c) = rest[end..].chars().next() {
            match c {
                ')' => break,
                '$' => end = self.macro_end(self.pos + end)? - self.pos,
                '"' => {
                    end +=
                        1 + rest[end + 1..].find('"').ok_or_else(|| {
                            self.error(
                                NmakeConditionErrorKind::UnfinishedString,
                                "Missing closing '\"'".to_string(),
                            )
                        })? + 1
                }
                c => end += c.len_utf8(),
            }
        }
        if !rest[end..].starts_with(')') {
            return Err(invalid(self));
        }
        let argument = rest[1..end].trim_matches([' ', '\t']);
        let argument = argument
            .strip_prefix('"')
            .and_then(|a| a.strip_suffix('"'))
            .unwrap_or(argument);
        if argument.is_empty() {
            return Err(invalid(self));
        }
        let argument = argument.to_string();
        self.pos += end + 1;
        Ok(function(argument))
    }
}

/// Parse an integer constant in decimal or C notation, which nmake takes
/// as a 32-bit number.
fn parse_integer(word: &str) -> Option<i64> {
    let (digits, radix) =
        if let Some(hex) = word.strip_prefix("0x").or_else(|| word.strip_prefix("0X")) {
            (hex, 16)
        } else if word.len() > 1 && word.starts_with('0') {
            (&word[1..], 8)
        } else {
            (word, 10)
        };
    if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
        return None;
    }
    u32::from_str_radix(digits, radix).ok().map(i64::from)
}

#[cfg(test)]
mod tests {
    use super::*;
    use NmakeBinaryOp::*;
    use NmakeCondition::{Binary, Command, Defined, Exist, Integer, Macro, String as Str, Unary};

    fn binary(lhs: NmakeCondition, op: NmakeBinaryOp, rhs: NmakeCondition) -> NmakeCondition {
        Binary {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        }
    }

    fn unary(op: NmakeUnaryOp, operand: NmakeCondition) -> NmakeCondition {
        Unary {
            op,
            operand: Box::new(operand),
        }
    }

    fn parse(text: &str) -> NmakeCondition {
        parse_nmake_condition(text).unwrap()
    }

    fn error(text: &str) -> (NmakeConditionErrorKind, usize) {
        let error = parse_nmake_condition(text).unwrap_err();
        (error.kind(), error.offset)
    }

    #[test]
    fn test_operands() {
        assert_eq!(parse("1"), Integer(1));
        assert_eq!(parse("010"), Integer(8));
        assert_eq!(parse("0x1F"), Integer(31));
        assert_eq!(parse("0"), Integer(0));
        assert_eq!(parse("0xFFFFFFFF"), Integer(0xFFFF_FFFF));
        assert_eq!(parse(r#""a b""#), Str("a b".to_string()));
        assert_eq!(parse(r#""""#), Str(String::new()));
        assert_eq!(parse("$(X)"), Macro("$(X)".to_string()));
        assert_eq!(parse("$(X:a=b)$Y"), Macro("$(X:a=b)$Y".to_string()));
        assert_eq!(parse("$(A $(B))"), Macro("$(A $(B))".to_string()));
        assert_eq!(parse("[cl /? > nul]"), Command("cl /? > nul".to_string()));
        assert_eq!(parse("DEFINED(X)"), Defined("X".to_string()));
        assert_eq!(parse("defined ( X )"), Defined("X".to_string()));
        assert_eq!(parse("DEFINED($(N))"), Defined("$(N)".to_string()));
        assert_eq!(parse("EXIST(a.c)"), Exist("a.c".to_string()));
        assert_eq!(
            parse(r#"EXIST("C:\Program Files")"#),
            Exist(r"C:\Program Files".to_string())
        );
        assert_eq!(parse("( ( 1 ) )"), Integer(1));
    }

    #[test]
    fn test_precedence() {
        assert_eq!(
            parse("1 + 2 * 3"),
            binary(Integer(1), Add, binary(Integer(2), Multiply, Integer(3)))
        );
        assert_eq!(
            parse("1 - 2 - 3"),
            binary(
                binary(Integer(1), Subtract, Integer(2)),
                Subtract,
                Integer(3)
            )
        );
        assert_eq!(
            parse("(1 + 2) * 3"),
            binary(binary(Integer(1), Add, Integer(2)), Multiply, Integer(3))
        );
        assert_eq!(
            parse("1<<2<3==1"),
            binary(
                binary(binary(Integer(1), ShiftLeft, Integer(2)), Less, Integer(3)),
                Equal,
                Integer(1)
            )
        );
        // `&`, `^` and `|` have the same precedence.
        assert_eq!(
            parse("1 | 2 & 3 ^ 4"),
            binary(
                binary(binary(Integer(1), BitOr, Integer(2)), BitAnd, Integer(3)),
                BitXor,
                Integer(4)
            )
        );
        assert_eq!(
            parse("1 == 1 | 2"),
            binary(binary(Integer(1), Equal, Integer(1)), BitOr, Integer(2))
        );
        assert_eq!(
            parse("1 || 2 && 3 & 4"),
            binary(
                Integer(1),
                Or,
                binary(Integer(2), And, binary(Integer(3), BitAnd, Integer(4)))
            )
        );
        assert_eq!(
            parse("4 >= 3 != 2 <= 1"),
            binary(
                binary(Integer(4), GreaterOrEqual, Integer(3)),
                NotEqual,
                binary(Integer(2), LessOrEqual, Integer(1))
            )
        );
        assert_eq!(
            parse("8>>1%3/2"),
            binary(
                Integer(8),
                ShiftRight,
                binary(
                    binary(Integer(1), Remainder, Integer(3)),
                    Divide,
                    Integer(2)
                )
            )
        );
    }

    #[test]
    fn test_unary() {
        assert_eq!(
            parse("!DEFINED(X) && -1 < ~0"),
            binary(
                unary(NmakeUnaryOp::Not, Defined("X".to_string())),
                And,
                binary(
                    unary(NmakeUnaryOp::Negate, Integer(1)),
                    Less,
                    unary(NmakeUnaryOp::Complement, Integer(0))
                )
            )
        );
        assert_eq!(
            parse("1--1"),
            binary(
                Integer(1),
                Subtract,
                unary(NmakeUnaryOp::Negate, Integer(1))
            )
        );
        assert_eq!(
            parse("!!1"),
            unary(NmakeUnaryOp::Not, unary(NmakeUnaryOp::Not, Integer(1)))
        );
    }

    #[test]
    fn test_comparisons() {
        assert_eq!(
            parse(r#""$(CFG)" == "Debug""#),
            binary(Str("$(CFG)".to_string()), Equal, Str("Debug".to_string()))
        );
        assert_eq!(
            parse("[my_command.exe arg1 arg2] != 0"),
            binary(
                Command("my_command.exe arg1 arg2".to_string()),
                NotEqual,
                Integer(0)
            )
        );
        assert_eq!(
            parse("$(VER)>=5"),
            binary(Macro("$(VER)".to_string()), GreaterOrEqual, Integer(5))
        );
    }

    #[test]
    fn test_errors() {
        use NmakeConditionErrorKind::*;
        assert_eq!(error(""), (MissingOperand, 0));
        assert_eq!(error("1 +"), (MissingOperand, 3));
        assert_eq!(error("!"), (MissingOperand, 1));
        assert_eq!(error("== 1"), (MissingOperand, 0));
        assert_eq!(error("(1"), (UnclosedParenthesis, 0));
        assert_eq!(error("1)"), (UnexpectedText, 1));
        assert_eq!(error("1 2"), (UnexpectedText, 2));
        assert_eq!(error("\"a"), (UnfinishedString, 0));
        assert_eq!(error("[cmd"), (UnclosedCommand, 0));
        assert_eq!(error("$(X"), (UnclosedMacro, 0));
        assert_eq!(error("$"), (UnclosedMacro, 0));
        assert_eq!(error("DEFINED X"), (InvalidFunctionCall, 8));
        assert_eq!(error("DEFINED(X"), (InvalidFunctionCall, 7));
        assert_eq!(error("DEFINED()"), (InvalidFunctionCall, 7));
        assert_eq!(error("EXIST(\"a)"), (UnfinishedString, 5));
        assert_eq!(error("foo"), (UnexpectedText, 0));
        assert_eq!(error("09"), (InvalidNumber, 0));
        assert_eq!(error("1x"), (InvalidNumber, 0));
        assert_eq!(error("0x100000000"), (InvalidNumber, 0));
        assert_eq!(error("1 = 1"), (UnexpectedText, 2));
        assert_eq!(error(&"(".repeat(1000)).0, TooDeeplyNested);
        assert_eq!(error(&"!".repeat(1000)).0, TooDeeplyNested);
    }

    #[test]
    fn test_display() {
        assert_eq!(NmakeBinaryOp::BitXor.to_string(), "^");
        assert_eq!(NmakeUnaryOp::Complement.to_string(), "~");
        let error = parse_nmake_condition("1 +").unwrap_err();
        assert_eq!(error.to_string(), "Missing operand at offset 3");
    }
}
