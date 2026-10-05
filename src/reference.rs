//! Parsing of variable references and their modifier chains.
//!
//! BSD make (NetBSD make and bmake) supports a rich set of modifiers in
//! variable references, e.g. `${SRCS:M*.c:S/.c/.o/g:Q}`. GNU make, POSIX
//! make and nmake only support substitution references such as
//! `$(SRCS:.c=.o)`.

use crate::MakefileVariant;

/// A piece of a [`ModifierArg`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModifierArgPart {
    /// Literal text, with escapes removed.
    Literal(String),
    /// A nested expression such as `${FOO:Q}` or `$X`, as unexpanded text.
    /// It can be parsed with [`ParsedReference::parse`].
    Expr(String),
}

/// An argument of a modifier, made up of literal text and nested
/// expressions.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ModifierArg(Vec<ModifierArgPart>);

impl ModifierArg {
    /// Create an argument from its parts.
    ///
    /// Adjacent literal parts are merged and empty literals are dropped, so
    /// that equal arguments compare equal.
    pub fn new(parts: impl IntoIterator<Item = ModifierArgPart>) -> Self {
        let mut arg = Self::default();
        for part in parts {
            match part {
                ModifierArgPart::Literal(text) => arg.push_str(&text),
                ModifierArgPart::Expr(text) => arg.push_expr(&text),
            }
        }
        arg
    }

    /// Create an argument consisting of only literal text.
    pub fn literal(text: &str) -> Self {
        let mut arg = Self::default();
        arg.push_str(text);
        arg
    }

    /// The parts of this argument.
    pub fn parts(&self) -> &[ModifierArgPart] {
        &self.0
    }

    /// The text of this argument, if it contains no nested expressions.
    pub fn as_literal(&self) -> Option<String> {
        match self.0.as_slice() {
            [] => Some(String::new()),
            [ModifierArgPart::Literal(text)] => Some(text.clone()),
            _ => None,
        }
    }

    /// Whether this argument is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn push_str(&mut self, text: &str) {
        if text.is_empty() {
            return;
        }
        if let Some(ModifierArgPart::Literal(last)) = self.0.last_mut() {
            last.push_str(text);
        } else {
            self.0.push(ModifierArgPart::Literal(text.to_string()));
        }
    }

    fn push_char(&mut self, c: char) {
        self.push_str(c.encode_utf8(&mut [0; 4]));
    }

    fn push_expr(&mut self, text: &str) {
        self.0.push(ModifierArgPart::Expr(text.to_string()));
    }

    fn extend(&mut self, other: &ModifierArg) {
        for part in &other.0 {
            match part {
                ModifierArgPart::Literal(text) => self.push_str(text),
                ModifierArgPart::Expr(text) => self.push_expr(text),
            }
        }
    }
}

/// Flags of the `:S` and `:C` modifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SubstituteFlags {
    /// `g`: replace all occurrences in each word, not just the first.
    pub global: bool,
    /// `1`: only modify the first word that matches.
    pub once: bool,
    /// `W`: treat the whole value as a single word.
    pub one_word: bool,
}

/// The order requested by the `:O` modifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortOrder {
    /// `:O`: sort words lexicographically.
    Ascending,
    /// `:Or`: sort words lexicographically, in reverse.
    Descending,
    /// `:On`: sort words numerically.
    NumericAscending,
    /// `:Onr` or `:Orn`: sort words numerically, in reverse.
    NumericDescending,
    /// `:Ox`: shuffle the words.
    Shuffle,
}

/// The words selected by the `:[...]` modifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WordSelector {
    /// `:[#]`: the number of words.
    Count,
    /// `:[*]` or `:[0]`: treat the value as a single word.
    OneWord,
    /// `:[@]`: treat the value as a sequence of words.
    Split,
    /// `:[N]` or `:[N..M]`: words N through M, counting from 1. Negative
    /// numbers count from the end, with -1 being the last word. If `first`
    /// is greater than `last`, the words are selected in reverse order.
    Range {
        /// The first word to select.
        first: i64,
        /// The last word to select.
        last: i64,
    },
    /// The selector contains nested expressions, so it can only be
    /// interpreted after expanding them.
    Unexpanded(ModifierArg),
}

/// The operator of an assignment modifier such as `::=`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    /// `::=`: assign the value.
    Set,
    /// `::?=`: assign the value if the variable is not yet defined.
    SetIfUndefined,
    /// `::+=`: append the value.
    Append,
    /// `::!=`: assign the output of running the value as a shell command.
    ShellOutput,
}

/// A modifier in a variable reference, such as `:M*.c` in `${SRCS:M*.c}`.
///
/// See the "Variable modifiers" section of NetBSD make(1) for their meaning.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Modifier {
    /// `:E`: the suffix of each word.
    Suffix,
    /// `:H`: the directory part of each word.
    Head,
    /// `:R`: each word with its suffix removed.
    Root,
    /// `:T`: the last path component of each word.
    Tail,
    /// `:Mpattern`: the words that match the pattern. The pattern is raw
    /// text, see [`ParsedReference`].
    Match(String),
    /// `:Npattern`: the words that do not match the pattern. The pattern is
    /// raw text, see [`ParsedReference`].
    NoMatch(String),
    /// `:S/old/new/[1gW]`, with any delimiter instead of `/`.
    Substitute {
        /// The text to replace, without the anchors.
        from: ModifierArg,
        /// The replacement, with `&` already replaced by `from`.
        to: ModifierArg,
        /// `from` started with `^`: only match at the start of a word.
        anchor_start: bool,
        /// `from` ended with `$`: only match at the end of a word.
        anchor_end: bool,
        /// The flags after the last delimiter.
        flags: SubstituteFlags,
    },
    /// `:C/regex/replacement/[1gW]`, with any delimiter instead of `/`.
    RegexSubstitute {
        /// The extended regular expression.
        regex: ModifierArg,
        /// The replacement, in which `&` and `\1` to `\9` are still to be
        /// replaced with the match.
        replacement: ModifierArg,
        /// The flags after the last delimiter.
        flags: SubstituteFlags,
    },
    /// `:from=to`, or a GNU make substitution reference `$(VAR:from=to)`.
    ///
    /// If `from` contains a `%` it is a pattern, and a `%` in `to` is
    /// replaced with the text it matched. Otherwise `from` is replaced with
    /// `to` at the end of each word. This modifier always comes last, as it
    /// extends to the end of the reference, including any colons.
    ///
    /// nmake instead replaces every occurrence of `from` in the value.
    SysVSubstitute {
        /// The suffix or pattern to replace.
        from: ModifierArg,
        /// The replacement.
        to: ModifierArg,
    },
    /// `:@var@body@`: expand the body for each word, with the word assigned
    /// to `var`. The body is raw text, see [`ParsedReference`].
    Loop {
        /// The name of the loop variable.
        var: String,
        /// The text to expand for each word.
        body: String,
    },
    /// `:Uvalue`: the value if the variable is undefined.
    Default(ModifierArg),
    /// `:Dvalue`: the value if the variable is defined.
    Defined(ModifierArg),
    /// `:L`: the name of the variable instead of its value.
    Literal,
    /// `:P`: the path of the target with the name of the variable.
    Path,
    /// `:Q`: quote shell meta-characters.
    Quote,
    /// `:q`: quote shell meta-characters, and also `$`.
    QuoteDollar,
    /// `:u`: remove adjacent duplicate words.
    Unique,
    /// `:O`, `:Or`, `:On`, `:Onr`, `:Orn` or `:Ox`: sort the words.
    Order(SortOrder),
    /// `:tl`: convert to lower case.
    ToLower,
    /// `:tu`: convert to upper case.
    ToUpper,
    /// `:tA`: resolve each word with realpath(3).
    Realpath,
    /// `:tsc`: separate words with the character `c`.
    ///
    /// `:ts` and `:ts\0` give `None`, meaning that words are joined without
    /// a separator. `:ts\n`, `:ts\t`, octal `:ts\NNN` and hexadecimal
    /// `:ts\xNN` are decoded.
    Separator(Option<char>),
    /// `:tW`: treat the value as a single word.
    OneWord,
    /// `:tw`: treat the value as a sequence of words.
    SplitWords,
    /// `:[...]`: select words.
    Words(WordSelector),
    /// `:!cmd!`: the output of running the command.
    ShellCommand(ModifierArg),
    /// `:sh`: the output of running the value as a command.
    Shell,
    /// `:?then:else`: `then` if the variable name, evaluated as a condition,
    /// is true, otherwise `else`. This modifier always comes last.
    IfElse {
        /// The value if the condition is true.
        then_branch: ModifierArg,
        /// The value if the condition is false.
        else_branch: ModifierArg,
    },
    /// `::=value`, `::?=value`, `::+=value` or `::!=value`: assign to the
    /// variable, giving an empty value. This modifier always comes last.
    Assign {
        /// The kind of assignment.
        op: AssignOp,
        /// The value to assign.
        value: ModifierArg,
    },
    /// `:hash`: a 32-bit hash of the value, in hexadecimal.
    Hash,
    /// `:range` or `:range=N`: the numbers from 1 to the number of words, or
    /// to N.
    Range(Option<usize>),
    /// `:gmtime` or `:gmtime=T`: the value as a strftime(3) format for the
    /// current time or time T, in UTC.
    GmTime(Option<u64>),
    /// `:localtime` or `:localtime=T`: like [`Modifier::GmTime`] but in the
    /// local time zone.
    LocalTime(Option<u64>),
    /// `:mtime` or `:mtime=arg`: the modification time of each word, where
    /// `arg` is either a timestamp to use for missing files or `error`.
    Mtime(Option<String>),
    /// `:_` or `:_=var`: save the value in the given variable, `_` by
    /// default.
    Remember(String),
    /// A nested expression such as `${MODS}` in `${VAR:${MODS}}`, whose
    /// value is a list of modifiers to apply.
    Indirect(String),
}

/// A variable reference, split into the variable name and its modifiers.
///
/// Arguments of modifiers are not expanded. Depending on how BSD make treats
/// the argument, it is returned either as a [`ModifierArg`] or as a raw
/// [`String`]:
///
/// - A [`ModifierArg`] is used where make expands nested expressions while
///   parsing the modifier (`:S`, `:C`, `:U`, `:D`, `:?`, `:!cmd!`, the
///   assignment modifiers, `:[...]` and the SysV substitution). Escapes are
///   already removed from its literal parts, and nested expressions are kept
///   as separate parts so that escaped text is never expanded again.
/// - A raw [`String`] is used where make expands the argument as a whole
///   after parsing it (the pattern of `:M` and `:N` and the body of `:@`).
///   The evaluator should expand it like any other value, so `$$` stands for
///   a literal `$`.
///
/// The escapes that are removed follow NetBSD make:
///
/// - `:S`, `:C`, `:!cmd!`, `:?`, the assignment modifiers, `:[...]` and the
///   SysV substitution: `\` followed by the delimiter that ends the part, by
///   `\` or by `$` stands for that character. In the replacement of `:S`,
///   `\&` stands for `&` as well, and an unescaped `&` is replaced with the
///   (unescaped) text to match. Other backslashes, such as those in regular
///   expressions for `:C`, are kept.
/// - `:U` and `:D`: `\` followed by `:`, the closing brace, `$` or `\`.
/// - `:M` and `:N`: `\` followed by `:` or the closing brace. A backslash
///   before the opening brace is kept, as it is in make.
/// - `:@`: in the variable name and body, `\@`, `\\` and `\$`.
///
/// In parts that are parsed into a [`ModifierArg`], `$$` is returned as a
/// literal `$`. NetBSD make instead treats the first `$` as an undefined
/// expression, and complains about it in strict mode.
///
/// # Example
/// ```
/// use makefile_lossless::{MakefileVariant, Modifier, ParsedReference};
/// let parsed = ParsedReference::parse("${SRCS:M*.c:Q}", MakefileVariant::BSDMake).unwrap();
/// assert_eq!(parsed.name, "SRCS");
/// assert_eq!(
///     parsed.modifiers,
///     vec![Modifier::Match("*.c".to_string()), Modifier::Quote]
/// );
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedReference {
    /// The unexpanded name of the variable. It may contain nested
    /// expressions, as in `${VAR_${X}}`, and is empty in `${:Uvalue}`.
    pub name: String,
    /// The modifiers, in the order in which they are applied.
    pub modifiers: Vec<Modifier>,
}

/// An error parsing a variable reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReferenceError {
    /// The reference is malformed.
    Syntax {
        /// The byte offset of the error in the text.
        offset: usize,
        /// A description of the error.
        message: String,
    },
    /// The reference contains a modifier that make does not know.
    UnknownModifier {
        /// The byte offset of the modifier in the text.
        offset: usize,
        /// The text of the modifier, as far as it could be determined.
        modifier: String,
    },
    /// The reference is a GNU make function call such as
    /// `$(patsubst %.c,%.o,$(SRCS))`, rather than a variable reference.
    FunctionCall {
        /// The name of the function.
        name: String,
    },
}

impl std::fmt::Display for ReferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReferenceError::Syntax { offset, message } => {
                write!(f, "{} at offset {}", message, offset)
            }
            ReferenceError::UnknownModifier { offset, modifier } => {
                write!(f, "unknown modifier ':{}' at offset {}", modifier, offset)
            }
            ReferenceError::FunctionCall { name } => {
                write!(f, "call of function '{}' is not a variable reference", name)
            }
        }
    }
}

impl std::error::Error for ReferenceError {}

/// The built-in functions of GNU make.
const GNU_FUNCTIONS: &[&str] = &[
    "abspath",
    "addprefix",
    "addsuffix",
    "and",
    "basename",
    "call",
    "dir",
    "error",
    "eval",
    "file",
    "filter",
    "filter-out",
    "findstring",
    "firstword",
    "flavor",
    "foreach",
    "guile",
    "if",
    "info",
    "intcmp",
    "join",
    "lastword",
    "let",
    "notdir",
    "or",
    "origin",
    "patsubst",
    "realpath",
    "shell",
    "sort",
    "strip",
    "subst",
    "suffix",
    "value",
    "warning",
    "wildcard",
    "word",
    "wordlist",
    "words",
];

impl ParsedReference {
    /// Parse a complete variable reference such as `${FOO:Q}`, `$(FOO)` or
    /// `$X`.
    ///
    /// For [`MakefileVariant::BSDMake`] all modifiers are recognized. For the
    /// other variants the only modifier is the substitution reference
    /// `$(VAR:from=to)`, and a reference without `=` after the colon refers to
    /// a variable whose name contains the colon. For
    /// [`MakefileVariant::GNUMake`] a function call such as `$(wildcard *.c)`
    /// gives [`ReferenceError::FunctionCall`].
    pub fn parse(text: &str, variant: MakefileVariant) -> Result<Self, ReferenceError> {
        let (parsed, end) = Self::parse_prefix(text, variant)?;
        if end != text.len() {
            return Err(syntax_error(end, "unexpected text after reference"));
        }
        Ok(parsed)
    }

    /// Parse the variable reference at the start of `text`, returning it and
    /// the length of its text.
    ///
    /// This is useful for expanding a value: find the next `$`, parse the
    /// reference there and continue after it. Note that `$$` is not a
    /// reference.
    pub fn parse_prefix(
        text: &str,
        variant: MakefileVariant,
    ) -> Result<(Self, usize), ReferenceError> {
        let mut parser = Parser { text, pos: 0 };
        let parsed = if variant == MakefileVariant::BSDMake {
            parser.parse_expr()?
        } else {
            parser.parse_simple_expr(variant)?
        };
        Ok((parsed, parser.pos))
    }

    /// Parse the text between the braces of a variable reference, such as
    /// `SRCS:M*.c` for `${SRCS:M*.c}`.
    ///
    /// The body extends to the end of `text`; there is no closing brace that
    /// ends it, so a `}` or `)` is treated like any other character where
    /// make would accept it.
    pub fn parse_body(body: &str, variant: MakefileVariant) -> Result<Self, ReferenceError> {
        let mut parser = Parser { text: body, pos: 0 };
        if variant == MakefileVariant::BSDMake {
            let delims = Delims {
                startc: None,
                endc: None,
            };
            let parsed = parser.parse_braced(delims)?;
            if parser.pos != body.len() {
                return Err(syntax_error(parser.pos, "unexpected text after reference"));
            }
            Ok(parsed)
        } else {
            parse_simple_body(body, 0, variant)
        }
    }
}

fn syntax_error(offset: usize, message: impl Into<String>) -> ReferenceError {
    ReferenceError::Syntax {
        offset,
        message: message.into(),
    }
}

/// The braces of the expression being parsed. Both are `None` when parsing
/// just the body of an expression.
#[derive(Debug, Clone, Copy)]
struct Delims {
    startc: Option<char>,
    endc: Option<char>,
}

impl Delims {
    /// Whether `c` ends a modifier; `None` stands for the end of the text.
    fn is_delimiter(&self, c: Option<char>) -> bool {
        match c {
            None | Some(':') => true,
            Some(c) => Some(c) == self.endc,
        }
    }
}

struct Parser<'a> {
    text: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn rest(&self) -> &'a str {
        &self.text[self.pos..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn peek_nth(&self, n: usize) -> Option<char> {
        self.rest().chars().nth(n)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn bump_n(&mut self, n: usize) {
        for _ in 0..n {
            self.bump();
        }
    }

    /// Parse a BSD make expression starting at `$`.
    fn parse_expr(&mut self) -> Result<ParsedReference, ReferenceError> {
        let start = self.pos;
        if self.bump() != Some('$') {
            return Err(syntax_error(start, "expected '$'"));
        }
        let endc = match self.peek() {
            Some('(') => ')',
            Some('{') => '}',
            Some('$') => {
                return Err(syntax_error(
                    start,
                    "'$$' is an escaped dollar, not a reference",
                ))
            }
            None | Some(':' | ')' | '}') => {
                return Err(syntax_error(start, "missing variable name after '$'"))
            }
            Some(c) => {
                self.bump();
                return Ok(ParsedReference {
                    name: c.to_string(),
                    modifiers: vec![],
                });
            }
        };
        let startc = self.bump();
        self.parse_braced(Delims {
            startc,
            endc: Some(endc),
        })
    }

    /// Parse the name and modifiers of an expression, after the opening
    /// brace. Consumes the closing brace.
    fn parse_braced(&mut self, delims: Delims) -> Result<ParsedReference, ReferenceError> {
        let name = self.parse_name(delims)?;
        let modifiers = match self.peek() {
            Some(':') => {
                self.bump();
                self.parse_modifiers(delims)?
            }
            None if delims.endc.is_none() => vec![],
            None => return Err(self.unclosed_error(delims)),
            Some(_) => {
                // The closing brace
                self.bump();
                vec![]
            }
        };
        Ok(ParsedReference { name, modifiers })
    }

    fn unclosed_error(&self, delims: Delims) -> ReferenceError {
        syntax_error(
            self.pos,
            format!("unclosed expression, expecting '{}'", delims.endc.unwrap()),
        )
    }

    /// Parse a variable name, up to the first `:` or closing brace that is
    /// not nested.
    fn parse_name(&mut self, delims: Delims) -> Result<String, ReferenceError> {
        let start = self.pos;
        let mut depth = 0;
        while let Some(c) = self.peek() {
            if (Some(c) == delims.endc || c == ':') && depth == 0 {
                break;
            }
            if Some(c) == delims.startc {
                depth += 1;
            }
            if Some(c) == delims.endc {
                depth -= 1;
            }
            if c != '$' {
                self.bump();
                continue;
            }
            match self.peek_nth(1) {
                Some('(' | '{') => {
                    self.parse_expr()?;
                }
                None => return Err(syntax_error(self.pos, "missing variable name after '$'")),
                // Like make, only skip the '$' since the next character
                // cannot be a variable name.
                Some(':' | ')' | '}') => {
                    self.bump();
                }
                Some(_) => self.bump_n(2),
            }
        }
        Ok(self.text[start..self.pos].to_string())
    }

    /// Parse the modifiers of an expression, after the first `:`. Consumes
    /// the closing brace.
    fn parse_modifiers(&mut self, delims: Delims) -> Result<Vec<Modifier>, ReferenceError> {
        let mut modifiers = vec![];
        loop {
            match self.peek() {
                None if delims.endc.is_none() => break,
                None => return Err(self.unclosed_error(delims)),
                Some(c) if Some(c) == delims.endc => {
                    self.bump();
                    break;
                }
                Some(_) => {}
            }
            let start = self.pos;
            modifiers.push(self.parse_modifier(delims)?);
            match self.peek() {
                Some(':') => {
                    self.bump();
                }
                c if delims.is_delimiter(c) => {}
                _ => {
                    return Err(syntax_error(
                        self.pos,
                        format!(
                            "missing delimiter ':' after modifier ':{}'",
                            &self.text[start..self.pos]
                        ),
                    ))
                }
            }
        }
        Ok(modifiers)
    }

    /// Whether the text at the current position is `name` followed by a
    /// delimiter.
    fn at_word(&self, name: &str, delims: Delims) -> bool {
        self.rest()
            .strip_prefix(name)
            .is_some_and(|rest| delims.is_delimiter(rest.chars().next()))
    }

    /// Whether the text at the current position is `name` followed by `=` or
    /// a delimiter.
    fn at_word_or_eq(&self, name: &str, delims: Delims) -> bool {
        self.rest().strip_prefix(name).is_some_and(|rest| {
            let next = rest.chars().next();
            next == Some('=') || delims.is_delimiter(next)
        })
    }

    fn parse_modifier(&mut self, delims: Delims) -> Result<Modifier, ReferenceError> {
        let start = self.pos;
        let first = self.peek().expect("caller checked for end of text");
        let simple = |parser: &mut Self, modifier: Modifier| {
            if delims.is_delimiter(parser.peek_nth(1)) {
                parser.bump();
                Some(modifier)
            } else {
                None
            }
        };
        let modifier = match first {
            '$' => self.parse_indirect(delims)?,
            '!' => {
                self.bump();
                Some(Modifier::ShellCommand(self.parse_part(
                    Some('!'),
                    None,
                    None,
                )?))
            }
            ':' => self.parse_assign(delims)?,
            '?' => {
                self.bump();
                let then_branch = self.parse_part(Some(':'), None, None)?;
                let else_branch = self.parse_part_to_end(delims)?;
                Some(Modifier::IfElse {
                    then_branch,
                    else_branch,
                })
            }
            '@' => Some(self.parse_loop()?),
            '[' => Some(self.parse_words(delims)?),
            '_' => self.parse_remember(delims),
            'C' => Some(self.parse_regex()?),
            'D' | 'U' => {
                self.bump();
                let value = self.parse_default_value(delims)?;
                Some(if first == 'D' {
                    Modifier::Defined(value)
                } else {
                    Modifier::Default(value)
                })
            }
            'E' => simple(self, Modifier::Suffix),
            'H' => simple(self, Modifier::Head),
            'R' => simple(self, Modifier::Root),
            'T' => simple(self, Modifier::Tail),
            'Q' => simple(self, Modifier::Quote),
            'q' => simple(self, Modifier::QuoteDollar),
            'u' => simple(self, Modifier::Unique),
            'g' if self.at_word_or_eq("gmtime", delims) => {
                self.bump_n("gmtime".len());
                Some(Modifier::GmTime(self.parse_time_arg()?))
            }
            'l' if self.at_word_or_eq("localtime", delims) => {
                self.bump_n("localtime".len());
                Some(Modifier::LocalTime(self.parse_time_arg()?))
            }
            'h' if self.at_word("hash", delims) => {
                self.bump_n("hash".len());
                Some(Modifier::Hash)
            }
            'L' => {
                self.bump();
                Some(Modifier::Literal)
            }
            'M' | 'N' => {
                self.bump();
                let pattern = self.parse_match_pattern(delims);
                Some(if first == 'M' {
                    Modifier::Match(pattern)
                } else {
                    Modifier::NoMatch(pattern)
                })
            }
            'm' if self.at_word_or_eq("mtime", delims) => {
                self.bump_n("mtime".len());
                Some(Modifier::Mtime(self.parse_mtime_arg(delims)?))
            }
            'O' => Some(self.parse_order(delims)?),
            'P' => {
                self.bump();
                Some(Modifier::Path)
            }
            'r' if self.at_word_or_eq("range", delims) => {
                self.bump_n("range".len());
                Some(Modifier::Range(self.parse_range_arg()?))
            }
            'S' => Some(self.parse_substitute()?),
            's' if self.at_word("sh", delims) => {
                self.bump_n("sh".len());
                Some(Modifier::Shell)
            }
            't' => Some(self.parse_to(delims)?),
            _ => None,
        };
        if let Some(modifier) = modifier {
            return Ok(modifier);
        }
        self.pos = start;
        if let Some(modifier) = self.parse_sysv(delims)? {
            return Ok(modifier);
        }
        // Guess the end of the modifier, like make does.
        self.bump();
        while !delims.is_delimiter(self.peek()) {
            self.bump();
        }
        Err(ReferenceError::UnknownModifier {
            offset: start,
            modifier: self.text[start..self.pos].to_string(),
        })
    }

    fn bad_modifier(&self, start: usize, delims: Delims) -> ReferenceError {
        let mut chars = self.text[start..].char_indices();
        chars.next();
        let len = chars
            .find(|&(_, c)| delims.is_delimiter(Some(c)))
            .map_or(self.text.len() - start, |(i, _)| i);
        syntax_error(
            start,
            format!("bad modifier ':{}'", &self.text[start..start + len]),
        )
    }

    /// Parse a nested expression used as a list of modifiers. Returns `None`
    /// and restores the position if it is not followed by a delimiter.
    fn parse_indirect(&mut self, delims: Delims) -> Result<Option<Modifier>, ReferenceError> {
        let start = self.pos;
        let mut arg = ModifierArg::default();
        self.parse_nested_expr(&mut arg)?;
        if !delims.is_delimiter(self.peek()) {
            self.pos = start;
            return Ok(None);
        }
        Ok(Some(Modifier::Indirect(
            self.text[start..self.pos].to_string(),
        )))
    }

    fn parse_assign(&mut self, delims: Delims) -> Result<Option<Modifier>, ReferenceError> {
        let (op, len) = match (self.peek_nth(1), self.peek_nth(2)) {
            (Some('='), _) => (AssignOp::Set, 2),
            (Some('?'), Some('=')) => (AssignOp::SetIfUndefined, 3),
            (Some('+'), Some('=')) => (AssignOp::Append, 3),
            (Some('!'), Some('=')) => (AssignOp::ShellOutput, 3),
            _ => return Ok(None),
        };
        self.bump_n(len);
        let value = self.parse_part_to_end(delims)?;
        Ok(Some(Modifier::Assign { op, value }))
    }

    fn parse_loop(&mut self) -> Result<Modifier, ReferenceError> {
        let start = self.pos;
        self.bump();
        let var = self
            .parse_part(Some('@'), None, None)?
            .as_literal()
            .filter(|var| !var.contains('$'))
            .ok_or_else(|| {
                syntax_error(
                    start,
                    "in the :@ modifier, the variable name must not contain a dollar",
                )
            })?;
        let body = self.parse_balanced_part('@')?;
        Ok(Modifier::Loop { var, body })
    }

    fn parse_words(&mut self, delims: Delims) -> Result<Modifier, ReferenceError> {
        let start = self.pos;
        self.bump();
        let arg = self.parse_part(Some(']'), None, None)?;
        if !delims.is_delimiter(self.peek()) {
            return Err(self.bad_modifier(start, delims));
        }
        let Some(text) = arg.as_literal() else {
            return Ok(Modifier::Words(WordSelector::Unexpanded(arg)));
        };
        let selector = match text.as_str() {
            "#" => WordSelector::Count,
            "*" => WordSelector::OneWord,
            "@" => WordSelector::Split,
            _ => {
                let (first, last) = match text.split_once("..") {
                    Some((first, last)) => (parse_int_base0(first), parse_int_base0(last)),
                    None => {
                        let n = parse_int_base0(&text);
                        (n, n)
                    }
                };
                match (first, last) {
                    (Some(0), Some(0)) => WordSelector::OneWord,
                    (Some(first), Some(last)) if first != 0 && last != 0 => {
                        WordSelector::Range { first, last }
                    }
                    _ => return Err(self.bad_modifier(start, delims)),
                }
            }
        };
        Ok(Modifier::Words(selector))
    }

    fn parse_remember(&mut self, delims: Delims) -> Option<Modifier> {
        if self.peek_nth(1) == Some('=') {
            self.bump_n(2);
            let len = self
                .rest()
                .find([':', ')', '}'])
                .unwrap_or(self.rest().len());
            let name = self.rest()[..len].to_string();
            self.pos += len;
            Some(Modifier::Remember(name))
        } else if delims.is_delimiter(self.peek_nth(1)) {
            self.bump();
            Some(Modifier::Remember("_".to_string()))
        } else {
            None
        }
    }

    /// Parse the delimiter after `:S` or `:C`.
    fn parse_pattern_delimiter(&mut self, name: char) -> Result<char, ReferenceError> {
        let start = self.pos;
        self.bump();
        self.bump().ok_or_else(|| {
            syntax_error(start, format!("missing delimiter for modifier ':{}'", name))
        })
    }

    fn parse_pattern_flags(&mut self) -> SubstituteFlags {
        let mut flags = SubstituteFlags::default();
        loop {
            match self.peek() {
                Some('g') => flags.global = true,
                Some('1') => flags.once = true,
                Some('W') => flags.one_word = true,
                _ => return flags,
            }
            self.bump();
        }
    }

    fn parse_substitute(&mut self) -> Result<Modifier, ReferenceError> {
        let delim = self.parse_pattern_delimiter('S')?;
        let anchor_start = self.peek() == Some('^');
        if anchor_start {
            self.bump();
        }
        let mut anchor_end = false;
        let from = self.parse_part(Some(delim), Some(&mut anchor_end), None)?;
        let to = self.parse_part(Some(delim), None, Some(&from))?;
        let flags = self.parse_pattern_flags();
        Ok(Modifier::Substitute {
            from,
            to,
            anchor_start,
            anchor_end,
            flags,
        })
    }

    fn parse_regex(&mut self) -> Result<Modifier, ReferenceError> {
        let delim = self.parse_pattern_delimiter('C')?;
        let regex = self.parse_part(Some(delim), None, None)?;
        let replacement = self.parse_part(Some(delim), None, None)?;
        let flags = self.parse_pattern_flags();
        Ok(Modifier::RegexSubstitute {
            regex,
            replacement,
            flags,
        })
    }

    fn parse_order(&mut self, delims: Delims) -> Result<Modifier, ReferenceError> {
        let start = self.pos;
        let c1 = self.peek_nth(1);
        let c2 = self.peek_nth(2);
        let (order, len) = if delims.is_delimiter(c1) {
            (SortOrder::Ascending, 1)
        } else if delims.is_delimiter(c2) {
            match c1 {
                Some('n') => (SortOrder::NumericAscending, 2),
                Some('r') => (SortOrder::Descending, 2),
                Some('x') => (SortOrder::Shuffle, 2),
                _ => return Err(self.bad_modifier(start, delims)),
            }
        } else if delims.is_delimiter(self.peek_nth(3))
            && matches!((c1, c2), (Some('n'), Some('r')) | (Some('r'), Some('n')))
        {
            (SortOrder::NumericDescending, 3)
        } else {
            return Err(self.bad_modifier(start, delims));
        };
        self.bump_n(len);
        Ok(Modifier::Order(order))
    }

    fn parse_to(&mut self, delims: Delims) -> Result<Modifier, ReferenceError> {
        let start = self.pos;
        let c1 = self.peek_nth(1);
        if delims.is_delimiter(c1) {
            return Err(self.bad_modifier(start, delims));
        }
        if c1 == Some('s') {
            return self.parse_separator(delims);
        }
        if !delims.is_delimiter(self.peek_nth(2)) {
            return Err(self.bad_modifier(start, delims));
        }
        let modifier = match c1 {
            Some('A') => Modifier::Realpath,
            Some('u') => Modifier::ToUpper,
            Some('l') => Modifier::ToLower,
            Some('W') => Modifier::OneWord,
            Some('w') => Modifier::SplitWords,
            _ => return Err(self.bad_modifier(start, delims)),
        };
        self.bump_n(2);
        Ok(modifier)
    }

    fn parse_separator(&mut self, delims: Delims) -> Result<Modifier, ReferenceError> {
        let start = self.pos;
        self.bump_n(2);
        let sep0 = self.peek();
        let sep1 = self.peek_nth(1);
        if let Some(c) = sep0 {
            if Some(c) != delims.endc && delims.is_delimiter(sep1) {
                self.bump();
                return Ok(Modifier::Separator(Some(c)));
            }
        }
        if delims.is_delimiter(sep0) {
            return Ok(Modifier::Separator(None));
        }
        if sep0 != Some('\\') {
            return Err(self.bad_modifier(start, delims));
        }
        match sep1 {
            Some('n') => {
                self.bump_n(2);
                return Ok(Modifier::Separator(Some('\n')));
            }
            Some('t') => {
                self.bump_n(2);
                return Ok(Modifier::Separator(Some('\t')));
            }
            _ => {}
        }
        let radix = match sep1 {
            Some('x') => {
                self.bump_n(2);
                16
            }
            Some(c) if c.is_ascii_digit() => {
                self.bump();
                8
            }
            _ => return Err(self.bad_modifier(start, delims)),
        };
        let digits_len = self
            .rest()
            .find(|c: char| !c.is_digit(radix))
            .unwrap_or(self.rest().len());
        let value = u8::from_str_radix(&self.rest()[..digits_len], radix).map_err(|_| {
            syntax_error(
                self.pos,
                format!("invalid character number at '{}'", self.rest()),
            )
        })?;
        self.pos += digits_len;
        if !delims.is_delimiter(self.peek()) {
            return Err(self.bad_modifier(start, delims));
        }
        Ok(Modifier::Separator(if value == 0 {
            None
        } else {
            Some(char::from(value))
        }))
    }

    /// Parse the digits of the argument of `:gmtime=` or `:localtime=`, if
    /// any.
    fn parse_time_arg(&mut self) -> Result<Option<u64>, ReferenceError> {
        if self.peek() != Some('=') {
            return Ok(None);
        }
        self.bump();
        let digits = self.take_digits();
        digits
            .parse()
            .map(Some)
            .map_err(|_| syntax_error(self.pos, format!("invalid time value '{}'", digits)))
    }

    fn parse_range_arg(&mut self) -> Result<Option<usize>, ReferenceError> {
        if self.peek() != Some('=') {
            return Ok(None);
        }
        self.bump();
        let digits = self.take_digits();
        digits.parse().map(Some).map_err(|_| {
            syntax_error(
                self.pos,
                format!("invalid number '{}' for ':range' modifier", digits),
            )
        })
    }

    fn parse_mtime_arg(&mut self, delims: Delims) -> Result<Option<String>, ReferenceError> {
        if self.peek() != Some('=') {
            return Ok(None);
        }
        self.bump();
        let start = self.pos;
        let digits = self.take_digits();
        if !digits.is_empty() {
            return Ok(Some(digits.to_string()));
        }
        if self.at_word("error", delims) {
            self.bump_n("error".len());
            return Ok(Some("error".to_string()));
        }
        Err(syntax_error(
            start,
            format!("invalid argument '{}' for modifier ':mtime'", self.rest()),
        ))
    }

    fn take_digits(&mut self) -> &'a str {
        let rest = self.rest();
        let len = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        self.pos += len;
        &rest[..len]
    }

    /// Try to parse a SysV substitution `from=to`, which extends to the
    /// closing brace.
    fn parse_sysv(&mut self, delims: Delims) -> Result<Option<Modifier>, ReferenceError> {
        let mut depth = 1;
        let mut eq_found = false;
        let mut end = None;
        for c in self.rest().chars() {
            if c == '=' {
                eq_found = true;
            } else if Some(c) == delims.endc {
                depth -= 1;
            } else if Some(c) == delims.startc {
                depth += 1;
            }
            if depth == 0 {
                end = Some(c);
                break;
            }
        }
        if end != delims.endc || !eq_found {
            return Ok(None);
        }
        let from = self.parse_part(Some('='), None, None)?;
        let to = self.parse_part_to_end(delims)?;
        Ok(Some(Modifier::SysVSubstitute { from, to }))
    }

    /// Parse the pattern of `:M` or `:N`.
    fn parse_match_pattern(&mut self, delims: Delims) -> String {
        let mut pattern = String::new();
        let mut nest = 0;
        while let Some(c) = self.peek() {
            if c == ':' && nest == 0 {
                break;
            }
            if c == '\\' {
                if let Some(next) = self.peek_nth(1) {
                    let escapes_delimiter = delims.is_delimiter(Some(next));
                    if escapes_delimiter || Some(next) == delims.startc {
                        if !escapes_delimiter {
                            pattern.push('\\');
                        }
                        pattern.push(next);
                        self.bump_n(2);
                        continue;
                    }
                }
            }
            if c == '(' || c == '{' {
                nest += 1;
            }
            if c == ')' || c == '}' {
                nest -= 1;
                if nest < 0 {
                    break;
                }
            }
            pattern.push(c);
            self.bump();
        }
        pattern
    }

    /// Parse the value of `:U` or `:D`, up to the next delimiter.
    fn parse_default_value(&mut self, delims: Delims) -> Result<ModifierArg, ReferenceError> {
        let mut arg = ModifierArg::default();
        while !delims.is_delimiter(self.peek()) {
            let c = self.peek().expect("end of text is a delimiter");
            if c == '\\' {
                if let Some(next) = self.peek_nth(1) {
                    if delims.is_delimiter(Some(next)) || next == '$' || next == '\\' {
                        arg.push_char(next);
                        self.bump_n(2);
                        continue;
                    }
                }
            }
            if c == '$' {
                self.parse_nested_expr(&mut arg)?;
                continue;
            }
            arg.push_char(c);
            self.bump();
        }
        Ok(arg)
    }

    /// Parse a nested expression starting at `$`, adding it to `arg`.
    fn parse_nested_expr(&mut self, arg: &mut ModifierArg) -> Result<(), ReferenceError> {
        let start = self.pos;
        match self.peek_nth(1) {
            Some('(' | '{') => {
                self.parse_expr()?;
                arg.push_expr(&self.text[start..self.pos]);
            }
            Some('$') => {
                self.bump_n(2);
                arg.push_char('$');
            }
            None | Some(':' | ')' | '}') => {
                return Err(syntax_error(start, "missing variable name after '$'"));
            }
            Some(_) => {
                self.bump_n(2);
                arg.push_expr(&self.text[start..self.pos]);
            }
        }
        Ok(())
    }

    /// Parse a part of a modifier up to and including `delim`, where `None`
    /// stands for the end of the text.
    ///
    /// If `anchor_end` is given, a `$` just before the delimiter sets it
    /// rather than being added to the part. If `subst_from` is given, `&`
    /// is replaced with it.
    fn parse_part(
        &mut self,
        delim: Option<char>,
        mut anchor_end: Option<&mut bool>,
        subst_from: Option<&ModifierArg>,
    ) -> Result<ModifierArg, ReferenceError> {
        let mut arg = ModifierArg::default();
        loop {
            let c = self.peek();
            if c == delim {
                self.bump();
                return Ok(arg);
            }
            let Some(c) = c else {
                return Err(syntax_error(
                    self.pos,
                    format!("unfinished modifier ('{}' missing)", delim.unwrap()),
                ));
            };
            let next = self.peek_nth(1);
            if c == '\\' {
                if let Some(next) = next {
                    if Some(next) == delim
                        || next == '\\'
                        || next == '$'
                        || (next == '&' && subst_from.is_some())
                    {
                        arg.push_char(next);
                        self.bump_n(2);
                        continue;
                    }
                }
            }
            if c != '$' {
                match subst_from {
                    Some(from) if c == '&' => arg.extend(from),
                    _ => arg.push_char(c),
                }
                self.bump();
                continue;
            }
            if next == delim {
                match anchor_end.as_mut() {
                    Some(anchor_end) => **anchor_end = true,
                    None => arg.push_char('$'),
                }
                self.bump();
                continue;
            }
            self.parse_nested_expr(&mut arg)?;
        }
    }

    /// Parse a part that extends to the closing brace, without consuming the
    /// brace.
    fn parse_part_to_end(&mut self, delims: Delims) -> Result<ModifierArg, ReferenceError> {
        let arg = self.parse_part(delims.endc, None, None)?;
        if let Some(endc) = delims.endc {
            self.pos -= endc.len_utf8();
        }
        Ok(arg)
    }

    /// Parse a part up to and including `delim`, keeping nested expressions
    /// as unexpanded text, as make does for the body of `:@`.
    fn parse_balanced_part(&mut self, delim: char) -> Result<String, ReferenceError> {
        let mut text = String::new();
        loop {
            let Some(c) = self.peek() else {
                return Err(syntax_error(
                    self.pos,
                    format!("unfinished modifier ('{}' missing)", delim),
                ));
            };
            if c == delim {
                self.bump();
                return Ok(text);
            }
            let next = self.peek_nth(1);
            if c == '\\' {
                if let Some(next) = next.filter(|&n| n == delim || n == '\\' || n == '$') {
                    text.push(next);
                    self.bump_n(2);
                    continue;
                }
            }
            let (startc, endc) = match (c, next) {
                ('$', Some('(')) => ('(', ')'),
                ('$', Some('{')) => ('{', '}'),
                _ => {
                    text.push(c);
                    self.bump();
                    continue;
                }
            };
            let start = self.pos;
            self.bump_n(2);
            let mut depth = 1;
            let mut prev = startc;
            while depth > 0 {
                let Some(c) = self.bump() else {
                    break;
                };
                if prev != '\\' {
                    if c == startc {
                        depth += 1;
                    }
                    if c == endc {
                        depth -= 1;
                    }
                }
                prev = c;
            }
            text.push_str(&self.text[start..self.pos]);
        }
    }

    /// Parse a reference for make variants other than BSD make, which only
    /// support substitution references.
    fn parse_simple_expr(
        &mut self,
        variant: MakefileVariant,
    ) -> Result<ParsedReference, ReferenceError> {
        let start = self.pos;
        if self.bump() != Some('$') {
            return Err(syntax_error(start, "expected '$'"));
        }
        let endc = match self.peek() {
            Some('(') => ')',
            Some('{') => '}',
            Some('$') => {
                return Err(syntax_error(
                    start,
                    "'$$' is an escaped dollar, not a reference",
                ))
            }
            None => return Err(syntax_error(start, "missing variable name after '$'")),
            Some(c) => {
                self.bump();
                return Ok(ParsedReference {
                    name: c.to_string(),
                    modifiers: vec![],
                });
            }
        };
        let body_start = self.pos + 1;
        let body_end = self.text.len()
            - skip_balanced(&self.text[self.pos..])
                .ok_or_else(|| {
                    syntax_error(
                        self.text.len(),
                        format!("unclosed reference, expecting '{}'", endc),
                    )
                })?
                .len();
        self.pos = body_end;
        parse_simple_body(&self.text[body_start..body_end - 1], body_start, variant)
    }
}

/// Skip the parenthesized or braced text at the start of `text`, counting
/// only the kind of brace it starts with as GNU make does. Returns the rest
/// of the text, or `None` if the brace is not closed.
fn skip_balanced(text: &str) -> Option<&str> {
    let open = text.chars().next()?;
    let close = if open == '(' { ')' } else { '}' };
    let mut depth = 0;
    for (i, c) in text.char_indices() {
        if c == open {
            depth += 1;
        } else if c == close {
            depth -= 1;
            if depth == 0 {
                return Some(&text[i + 1..]);
            }
        }
    }
    None
}

/// Find the first occurrence of `needle` in `text` that is not inside a
/// nested reference.
fn find_unnested(text: &str, needle: char) -> Option<usize> {
    let mut i = 0;
    while let Some(c) = text[i..].chars().next() {
        if c == needle {
            return Some(i);
        }
        if c == '$' {
            let rest = &text[i + 1..];
            match rest.chars().next() {
                Some('(' | '{') => {
                    i = text.len() - skip_balanced(rest).map_or(0, str::len);
                    continue;
                }
                Some(next) => i += next.len_utf8(),
                None => {}
            }
        }
        i += c.len_utf8();
    }
    None
}

/// Parse the body of a reference for make variants other than BSD make.
/// `offset` is the position of the body in the original text.
fn parse_simple_body(
    body: &str,
    offset: usize,
    variant: MakefileVariant,
) -> Result<ParsedReference, ReferenceError> {
    if variant == MakefileVariant::GNUMake {
        if let Some((name, _)) = body.split_once([' ', '\t']) {
            if GNU_FUNCTIONS.contains(&name) {
                return Err(ReferenceError::FunctionCall {
                    name: name.to_string(),
                });
            }
        }
    }
    let substitution = find_unnested(body, ':').and_then(|colon| {
        let eq = colon + 1 + find_unnested(&body[colon + 1..], '=')?;
        Some((colon, eq))
    });
    let Some((colon, eq)) = substitution else {
        return Ok(ParsedReference {
            name: body.to_string(),
            modifiers: vec![],
        });
    };
    let from = parse_simple_arg(&body[colon + 1..eq], offset + colon + 1)?;
    let to = parse_simple_arg(&body[eq + 1..], offset + eq + 1)?;
    Ok(ParsedReference {
        name: body[..colon].to_string(),
        modifiers: vec![Modifier::SysVSubstitute { from, to }],
    })
}

/// Split an argument of a substitution reference into literal text and
/// nested references. There are no escapes other than `$$`.
fn parse_simple_arg(text: &str, offset: usize) -> Result<ModifierArg, ReferenceError> {
    let mut arg = ModifierArg::default();
    let mut rest = text;
    while let Some(i) = rest.find('$') {
        arg.push_str(&rest[..i]);
        let after = &rest[i + 1..];
        let end = match after.chars().next() {
            Some('$') => {
                arg.push_char('$');
                rest = &after[1..];
                continue;
            }
            Some('(' | '{') => {
                after.len()
                    - skip_balanced(after)
                        .ok_or_else(|| {
                            syntax_error(
                                offset + text.len() - rest.len() + i,
                                "unclosed nested reference",
                            )
                        })?
                        .len()
            }
            Some(c) => c.len_utf8(),
            None => {
                return Err(syntax_error(
                    offset + text.len() - rest.len() + i,
                    "missing variable name after '$'",
                ))
            }
        };
        arg.push_expr(&rest[i..i + 1 + end]);
        rest = &after[end..];
    }
    arg.push_str(rest);
    Ok(arg)
}

/// Parse an integer like strtol(3) with base 0, requiring that the whole
/// text is consumed.
fn parse_int_base0(text: &str) -> Option<i64> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text.strip_prefix('+').unwrap_or(text)),
    };
    let (radix, digits) = if let Some(hex) = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        (16, hex)
    } else if digits.len() > 1 && digits.starts_with('0') {
        (8, &digits[1..])
    } else {
        (10, digits)
    };
    if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
        return None;
    }
    let value = i64::from_str_radix(digits, radix).ok()?;
    Some(if negative { -value } else { value })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MakefileVariant::{BSDMake, GNUMake, NMake, POSIXMake};

    fn lit(text: &str) -> ModifierArg {
        ModifierArg::literal(text)
    }

    fn expr(text: &str) -> ModifierArgPart {
        ModifierArgPart::Expr(text.to_string())
    }

    fn text(text: &str) -> ModifierArgPart {
        ModifierArgPart::Literal(text.to_string())
    }

    fn bsd(text: &str) -> ParsedReference {
        ParsedReference::parse(text, BSDMake).unwrap()
    }

    fn mods(text: &str) -> Vec<Modifier> {
        bsd(text).modifiers
    }

    fn one(text: &str) -> Modifier {
        let mut modifiers = mods(text);
        assert_eq!(modifiers.len(), 1, "{:?}", modifiers);
        modifiers.remove(0)
    }

    fn reference(name: &str, modifiers: Vec<Modifier>) -> ParsedReference {
        ParsedReference {
            name: name.to_string(),
            modifiers,
        }
    }

    fn subst(from: &str, to: &str, flags: SubstituteFlags) -> Modifier {
        Modifier::Substitute {
            from: lit(from),
            to: lit(to),
            anchor_start: false,
            anchor_end: false,
            flags,
        }
    }

    fn global() -> SubstituteFlags {
        SubstituteFlags {
            global: true,
            ..Default::default()
        }
    }

    fn sysv(from: &str, to: &str) -> Modifier {
        Modifier::SysVSubstitute {
            from: lit(from),
            to: lit(to),
        }
    }

    fn syntax(text: &str) -> (usize, String) {
        match ParsedReference::parse(text, BSDMake) {
            Err(ReferenceError::Syntax { offset, message }) => (offset, message),
            other => panic!("expected syntax error, got {:?}", other),
        }
    }

    #[test]
    fn test_plain() {
        assert_eq!(bsd("${FOO}"), reference("FOO", vec![]));
        assert_eq!(bsd("$(FOO)"), reference("FOO", vec![]));
        assert_eq!(bsd("$X"), reference("X", vec![]));
        assert_eq!(bsd("$@"), reference("@", vec![]));
        assert_eq!(bsd("${.CURDIR}"), reference(".CURDIR", vec![]));
        assert_eq!(bsd("${FOO:}"), reference("FOO", vec![]));
        assert_eq!(bsd("${}"), reference("", vec![]));
    }

    #[test]
    fn test_nested_name() {
        assert_eq!(bsd("${VAR_${X}}"), reference("VAR_${X}", vec![]));
        assert_eq!(bsd("${VAR_$X}"), reference("VAR_$X", vec![]));
        assert_eq!(
            bsd("${LIBDO.${lib}:U}"),
            reference("LIBDO.${lib}", vec![Modifier::Default(lit(""))])
        );
        // A colon inside the nested reference does not end the name.
        assert_eq!(
            bsd("${A.${B:S/:/_/g}:Q}"),
            reference("A.${B:S/:/_/g}", vec![Modifier::Quote])
        );
        assert_eq!(bsd("$(A(B))"), reference("A(B)", vec![]));
    }

    #[test]
    fn test_word_modifiers() {
        assert_eq!(
            mods("${X:E:H:R:T}"),
            vec![
                Modifier::Suffix,
                Modifier::Head,
                Modifier::Root,
                Modifier::Tail
            ]
        );
        assert_eq!(
            bsd("${.CURDIR:H}"),
            reference(".CURDIR", vec![Modifier::Head])
        );
        assert_eq!(
            mods("$(X:Q:q:u:L:P)"),
            vec![
                Modifier::Quote,
                Modifier::QuoteDollar,
                Modifier::Unique,
                Modifier::Literal,
                Modifier::Path
            ]
        );
    }

    #[test]
    fn test_order() {
        assert_eq!(
            mods("${X:O:Or:On:Onr:Orn:Ox}"),
            vec![
                Modifier::Order(SortOrder::Ascending),
                Modifier::Order(SortOrder::Descending),
                Modifier::Order(SortOrder::NumericAscending),
                Modifier::Order(SortOrder::NumericDescending),
                Modifier::Order(SortOrder::NumericDescending),
                Modifier::Order(SortOrder::Shuffle),
            ]
        );
        assert_eq!(syntax("${X:Oq}"), (4, "bad modifier ':Oq'".to_string()));
    }

    #[test]
    fn test_to() {
        assert_eq!(
            mods("${X:tl:tu:tA:tW:tw}"),
            vec![
                Modifier::ToLower,
                Modifier::ToUpper,
                Modifier::Realpath,
                Modifier::OneWord,
                Modifier::SplitWords,
            ]
        );
        assert_eq!(syntax("${X:tx}"), (4, "bad modifier ':tx'".to_string()));
        assert_eq!(syntax("${X:t}"), (4, "bad modifier ':t'".to_string()));
        assert_eq!(syntax("${X:tlx}"), (4, "bad modifier ':tlx'".to_string()));
    }

    #[test]
    fn test_separator() {
        assert_eq!(one("${X:ts,}"), Modifier::Separator(Some(',')));
        assert_eq!(one("${X:ts}"), Modifier::Separator(None));
        assert_eq!(
            mods("${X:ts:Q}"),
            vec![Modifier::Separator(None), Modifier::Quote]
        );
        // A colon directly before the closing brace is the separator.
        assert_eq!(one("${X:ts:}"), Modifier::Separator(Some(':')));
        assert_eq!(
            mods("${X:ts::Q}"),
            vec![Modifier::Separator(Some(':')), Modifier::Quote]
        );
        assert_eq!(one("${X:ts\\n}"), Modifier::Separator(Some('\n')));
        assert_eq!(one("${X:ts\\t}"), Modifier::Separator(Some('\t')));
        assert_eq!(one("${X:ts\\072}"), Modifier::Separator(Some(':')));
        assert_eq!(one("${X:ts\\x2c}"), Modifier::Separator(Some(',')));
        assert_eq!(one("${X:ts\\0}"), Modifier::Separator(None));
        assert_eq!(syntax("${X:tsab}"), (4, "bad modifier ':tsab'".to_string()));
        assert_eq!(
            syntax("${X:ts\\q}"),
            (4, "bad modifier ':ts\\q'".to_string())
        );
        assert_eq!(
            syntax("${X:ts\\x}"),
            (8, "invalid character number at '}'".to_string())
        );
        assert_eq!(
            syntax("${X:ts\\400}"),
            (7, "invalid character number at '400}'".to_string())
        );
    }

    #[test]
    fn test_match() {
        assert_eq!(one("${SRCS:M*.c}"), Modifier::Match("*.c".to_string()));
        assert_eq!(one("${SRCS:N*.c}"), Modifier::NoMatch("*.c".to_string()));
        assert_eq!(
            bsd("${CPPFLAGS:M-[ID]*}"),
            reference("CPPFLAGS", vec![Modifier::Match("-[ID]*".to_string())])
        );
        // Braces are balanced, so a nested reference may contain colons.
        assert_eq!(
            mods("${X:M${PAT:Q}:Q}"),
            vec![Modifier::Match("${PAT:Q}".to_string()), Modifier::Quote]
        );
        assert_eq!(one("${X:M{a,b}*}"), Modifier::Match("{a,b}*".to_string()));
        // An escaped delimiter loses its backslash, an escaped opening
        // brace does not.
        assert_eq!(one("${X:Ma\\:b}"), Modifier::Match("a:b".to_string()));
        assert_eq!(one("${X:Ma\\}b}"), Modifier::Match("a}b".to_string()));
        assert_eq!(one("${X:Ma\\{b}"), Modifier::Match("a\\{b".to_string()));
        assert_eq!(one("${X:M\\*}"), Modifier::Match("\\*".to_string()));
        assert_eq!(one("${X:M}"), Modifier::Match("".to_string()));
        // `=` does not make this a SysV substitution.
        assert_eq!(one("${X:Ma=b}"), Modifier::Match("a=b".to_string()));
    }

    #[test]
    fn test_substitute() {
        assert_eq!(
            one("${X:S/.c/.o/}"),
            subst(".c", ".o", SubstituteFlags::default())
        );
        assert_eq!(one("${X:S/.c/.o/g}"), subst(".c", ".o", global()));
        assert_eq!(
            one("${X:S/a/b/1gW}"),
            subst(
                "a",
                "b",
                SubstituteFlags {
                    global: true,
                    once: true,
                    one_word: true
                }
            )
        );
        assert_eq!(one("${X:S,a/b,c,}"), subst("a/b", "c", Default::default()));
        assert_eq!(one("${X:S|a|}|}"), subst("a", "}", Default::default()));
        assert_eq!(
            one("${X:S\u{a7}a\u{a7}b\u{a7}}"),
            subst("a", "b", Default::default())
        );
        assert_eq!(
            one("${X:S/^lib//}"),
            Modifier::Substitute {
                from: lit("lib"),
                to: lit(""),
                anchor_start: true,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:S/.c$/.o/}"),
            Modifier::Substitute {
                from: lit(".c"),
                to: lit(".o"),
                anchor_start: false,
                anchor_end: true,
                flags: Default::default(),
            }
        );
        // `$` before the delimiter in the replacement is literal.
        assert_eq!(one("${X:S/a/b$/}"), subst("a", "b$", Default::default()));
    }

    #[test]
    fn test_substitute_escapes() {
        assert_eq!(one("${X:S/\\//_/g}"), subst("/", "_", global()));
        assert_eq!(one("${X:S/a/\\\\/}"), subst("a", "\\", Default::default()));
        assert_eq!(one("${X:S/a/\\$/}"), subst("a", "$", Default::default()));
        // An escaped `$` before the delimiter is not an anchor.
        assert_eq!(one("${X:S/a\\$/b/}"), subst("a$", "b", Default::default()));
        // `&` stands for the text to match, `\&` for itself.
        assert_eq!(
            one("${X:S/^a/&&\\&/}"),
            Modifier::Substitute {
                from: lit("a"),
                to: lit("aa&"),
                anchor_start: true,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:S/${A}/[&]/}"),
            Modifier::Substitute {
                from: ModifierArg::new([expr("${A}")]),
                to: ModifierArg::new([text("["), expr("${A}"), text("]")]),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        // Other backslashes are kept.
        assert_eq!(
            one("${X:S/a\\b/c/}"),
            subst("a\\b", "c", Default::default())
        );
        assert_eq!(one("${X:S/a/$$/}"), subst("a", "$", Default::default()));
    }

    #[test]
    fn test_substitute_nested() {
        assert_eq!(
            one("${X:S/${A:S,/,x,}/$B/}"),
            Modifier::Substitute {
                from: ModifierArg::new([expr("${A:S,/,x,}")]),
                to: ModifierArg::new([expr("$B")]),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
    }

    #[test]
    fn test_regex_substitute() {
        assert_eq!(
            bsd("${MACHINE_ARCH:C/e[lb]$//}"),
            reference(
                "MACHINE_ARCH",
                vec![Modifier::RegexSubstitute {
                    regex: lit("e[lb]$"),
                    replacement: lit(""),
                    flags: Default::default(),
                }]
            )
        );
        assert_eq!(
            one("${X:C,([^/]*)/(.*),\\2 & \\1,g}"),
            Modifier::RegexSubstitute {
                regex: lit("([^/]*)/(.*)"),
                replacement: lit("\\2 & \\1"),
                flags: global(),
            }
        );
        assert_eq!(
            one("${X:C/\\./\\//W}"),
            Modifier::RegexSubstitute {
                regex: lit("\\."),
                replacement: lit("/"),
                flags: SubstituteFlags {
                    one_word: true,
                    ..Default::default()
                },
            }
        );
        assert_eq!(
            syntax("${X:C/a/b}"),
            (10, "unfinished modifier ('/' missing)".to_string())
        );
        assert_eq!(
            syntax("$(X:S"),
            (4, "missing delimiter for modifier ':S'".to_string())
        );
    }

    #[test]
    fn test_sysv() {
        assert_eq!(
            bsd("${SRCS:.c=.o}"),
            reference("SRCS", vec![sysv(".c", ".o")])
        );
        assert_eq!(one("${X:%.c=%.o}"), sysv("%.c", "%.o"));
        assert_eq!(one("${X:=.o}"), sysv("", ".o"));
        assert_eq!(one("${X:.c=}"), sysv(".c", ""));
        // The replacement extends to the closing brace, colons included.
        assert_eq!(one("${X:a=b:c:Q}"), sysv("a", "b:c:Q"));
        assert_eq!(
            bsd("${SRCS:M*.c:.c=.o}"),
            reference(
                "SRCS",
                vec![Modifier::Match("*.c".to_string()), sysv(".c", ".o")]
            )
        );
        assert_eq!(
            one("${X:${A}=${B:Q}}"),
            Modifier::SysVSubstitute {
                from: ModifierArg::new([expr("${A}")]),
                to: ModifierArg::new([expr("${B:Q}")]),
            }
        );
        assert_eq!(one("${X:a\\=b=c}"), sysv("a=b", "c"));
        assert_eq!(one("${X:a=\\}}"), sysv("a", "}"));
        // Modifiers that require a delimiter after them fall back to SysV.
        assert_eq!(one("${X:E=x}"), sysv("E", "x"));
        assert_eq!(one("${X:Q=x}"), sysv("Q", "x"));
        assert_eq!(one("$(X:.c=.o)"), sysv(".c", ".o"));
    }

    #[test]
    fn test_loop() {
        assert_eq!(
            one("${X:@f@${f}.o@}"),
            Modifier::Loop {
                var: "f".to_string(),
                body: "${f}.o".to_string()
            }
        );
        assert_eq!(
            one("${X:@f@-I${f:H} $$f \\@ \\$f$@}"),
            Modifier::Loop {
                var: "f".to_string(),
                body: "-I${f:H} $$f @ $f$".to_string()
            }
        );
        // The body may contain colons and braces in nested references.
        assert_eq!(
            mods("${X:@f@${f:S/@/at/}@:Q}"),
            vec![
                Modifier::Loop {
                    var: "f".to_string(),
                    body: "${f:S/@/at/}".to_string()
                },
                Modifier::Quote
            ]
        );
        assert_eq!(
            syntax("${X:@${v}@x@}"),
            (
                4,
                "in the :@ modifier, the variable name must not contain a dollar".to_string()
            )
        );
        assert_eq!(
            syntax("${X:@v@x}"),
            (9, "unfinished modifier ('@' missing)".to_string())
        );
    }

    #[test]
    fn test_default_defined() {
        assert_eq!(one("${X:Ufoo}"), Modifier::Default(lit("foo")));
        assert_eq!(one("${X:Dfoo}"), Modifier::Defined(lit("foo")));
        assert_eq!(
            bsd("${:Ua b c:[2]}"),
            reference(
                "",
                vec![
                    Modifier::Default(lit("a b c")),
                    Modifier::Words(WordSelector::Range { first: 2, last: 2 })
                ]
            )
        );
        assert_eq!(
            one("${X:U${Y:S/a/b/}/x}"),
            Modifier::Default(ModifierArg::new([expr("${Y:S/a/b/}"), text("/x")]))
        );
        assert_eq!(
            one("${X:Ua\\:b\\}\\$c\\\\\\d}"),
            Modifier::Default(lit("a:b}$c\\\\d"))
        );
        // Unlike in the name, braces are not balanced in the value.
        assert_eq!(
            ParsedReference::parse_prefix("${X:U{a}:Q}", BSDMake),
            Ok((reference("X", vec![Modifier::Default(lit("{a"))]), 8))
        );
    }

    #[test]
    fn test_shell() {
        assert_eq!(
            one("${X:!echo a:b!}"),
            Modifier::ShellCommand(lit("echo a:b"))
        );
        assert_eq!(
            one("${X:!echo \\! ${Y}!}"),
            Modifier::ShellCommand(ModifierArg::new([text("echo ! "), expr("${Y}")]))
        );
        assert_eq!(mods("${X:sh:Q}"), vec![Modifier::Shell, Modifier::Quote]);
    }

    #[test]
    fn test_if_else() {
        assert_eq!(
            bsd("${MKPIC:Mno:?yes:no}"),
            reference(
                "MKPIC",
                vec![
                    Modifier::Match("no".to_string()),
                    Modifier::IfElse {
                        then_branch: lit("yes"),
                        else_branch: lit("no"),
                    }
                ]
            )
        );
        // The else branch extends to the closing brace.
        assert_eq!(
            one("${X:?${A:Q}:b:c}"),
            Modifier::IfElse {
                then_branch: ModifierArg::new([expr("${A:Q}")]),
                else_branch: lit("b:c"),
            }
        );
        assert_eq!(
            one("${X:?a\\:b:}"),
            Modifier::IfElse {
                then_branch: lit("a:b"),
                else_branch: lit(""),
            }
        );
    }

    #[test]
    fn test_assign() {
        assert_eq!(
            one("${X::=a:b}"),
            Modifier::Assign {
                op: AssignOp::Set,
                value: lit("a:b")
            }
        );
        assert_eq!(
            one("${X::?=a}"),
            Modifier::Assign {
                op: AssignOp::SetIfUndefined,
                value: lit("a")
            }
        );
        assert_eq!(
            one("${X::+=${Y}}"),
            Modifier::Assign {
                op: AssignOp::Append,
                value: ModifierArg::new([expr("${Y}")])
            }
        );
        assert_eq!(
            one("${X::!=echo}"),
            Modifier::Assign {
                op: AssignOp::ShellOutput,
                value: lit("echo")
            }
        );
    }

    #[test]
    fn test_words() {
        let words = |text| match one(text) {
            Modifier::Words(selector) => selector,
            other => panic!("unexpected {:?}", other),
        };
        assert_eq!(words("${X:[1]}"), WordSelector::Range { first: 1, last: 1 });
        assert_eq!(
            words("${X:[-1]}"),
            WordSelector::Range {
                first: -1,
                last: -1
            }
        );
        assert_eq!(
            words("${X:[1..2]}"),
            WordSelector::Range { first: 1, last: 2 }
        );
        assert_eq!(
            words("${X:[-1..1]}"),
            WordSelector::Range { first: -1, last: 1 }
        );
        assert_eq!(
            words("${X:[0x10]}"),
            WordSelector::Range {
                first: 16,
                last: 16
            }
        );
        assert_eq!(words("${X:[#]}"), WordSelector::Count);
        assert_eq!(words("${X:[*]}"), WordSelector::OneWord);
        assert_eq!(words("${X:[0]}"), WordSelector::OneWord);
        assert_eq!(words("${X:[@]}"), WordSelector::Split);
        assert_eq!(
            words("${X:[${N}]}"),
            WordSelector::Unexpanded(ModifierArg::new([expr("${N}")]))
        );
        assert_eq!(syntax("${X:[]}"), (4, "bad modifier ':[]'".to_string()));
        assert_eq!(
            syntax("${X:[0..1]}"),
            (4, "bad modifier ':[0..1]'".to_string())
        );
        assert_eq!(
            syntax("${X:[1..]}"),
            (4, "bad modifier ':[1..]'".to_string())
        );
        assert_eq!(syntax("${X:[a]}"), (4, "bad modifier ':[a]'".to_string()));
        assert_eq!(syntax("${X:[1]x}"), (4, "bad modifier ':[1]x'".to_string()));
    }

    #[test]
    fn test_misc() {
        assert_eq!(
            mods("${X:hash:range:range=3:gmtime:gmtime=1:localtime:localtime=2}"),
            vec![
                Modifier::Hash,
                Modifier::Range(None),
                Modifier::Range(Some(3)),
                Modifier::GmTime(None),
                Modifier::GmTime(Some(1)),
                Modifier::LocalTime(None),
                Modifier::LocalTime(Some(2)),
            ]
        );
        assert_eq!(
            mods("${X:mtime:mtime=5:mtime=error}"),
            vec![
                Modifier::Mtime(None),
                Modifier::Mtime(Some("5".to_string())),
                Modifier::Mtime(Some("error".to_string())),
            ]
        );
        assert_eq!(
            mods("${X:_:_=save:Q}"),
            vec![
                Modifier::Remember("_".to_string()),
                Modifier::Remember("save".to_string()),
                Modifier::Quote,
            ]
        );
        assert_eq!(
            syntax("${X:range=x}"),
            (10, "invalid number '' for ':range' modifier".to_string())
        );
        assert_eq!(
            syntax("${X:gmtime=x}"),
            (11, "invalid time value ''".to_string())
        );
    }

    #[test]
    fn test_indirect() {
        assert_eq!(
            mods("${X:${MODS}:Q}"),
            vec![Modifier::Indirect("${MODS}".to_string()), Modifier::Quote]
        );
        assert_eq!(one("${X:$M}"), Modifier::Indirect("$M".to_string()));
        // Not followed by a delimiter, so it is a SysV substitution.
        assert_eq!(
            one("${X:${A}x=y}"),
            Modifier::SysVSubstitute {
                from: ModifierArg::new([expr("${A}"), text("x")]),
                to: lit("y"),
            }
        );
    }

    #[test]
    fn test_chain() {
        assert_eq!(
            bsd("${SRCS:M*.c:S/.c/.o/g:Q}"),
            reference(
                "SRCS",
                vec![
                    Modifier::Match("*.c".to_string()),
                    subst(".c", ".o", global()),
                    Modifier::Quote,
                ]
            )
        );
        assert_eq!(
            bsd("$(SRCS:T:R:S/$/.o/:O:u)"),
            reference(
                "SRCS",
                vec![
                    Modifier::Tail,
                    Modifier::Root,
                    Modifier::Substitute {
                        from: lit(""),
                        to: lit(".o"),
                        anchor_start: false,
                        anchor_end: true,
                        flags: Default::default(),
                    },
                    Modifier::Order(SortOrder::Ascending),
                    Modifier::Unique,
                ]
            )
        );
    }

    #[test]
    fn test_unknown_modifier() {
        assert_eq!(
            ParsedReference::parse("${X:Z:Q}", BSDMake),
            Err(ReferenceError::UnknownModifier {
                offset: 4,
                modifier: "Z".to_string()
            })
        );
        assert_eq!(
            ParsedReference::parse("${X:Ex}", BSDMake),
            Err(ReferenceError::UnknownModifier {
                offset: 4,
                modifier: "Ex".to_string()
            })
        );
        assert_eq!(
            ParsedReference::parse("${X::}", BSDMake),
            Err(ReferenceError::UnknownModifier {
                offset: 4,
                modifier: ":".to_string()
            })
        );
    }

    #[test]
    fn test_syntax_errors() {
        assert_eq!(
            syntax("${X"),
            (3, "unclosed expression, expecting '}'".to_string())
        );
        assert_eq!(
            syntax("${X:Q"),
            (5, "unclosed expression, expecting '}'".to_string())
        );
        assert_eq!(
            syntax("$(X:Lx)"),
            (5, "missing delimiter ':' after modifier ':L'".to_string())
        );
        assert_eq!(
            syntax("$$"),
            (0, "'$$' is an escaped dollar, not a reference".to_string())
        );
        assert_eq!(
            syntax("$"),
            (0, "missing variable name after '$'".to_string())
        );
        assert_eq!(
            syntax("${X}y"),
            (4, "unexpected text after reference".to_string())
        );
        assert_eq!(
            syntax("${X:U$}"),
            (5, "missing variable name after '$'".to_string())
        );
    }

    #[test]
    fn test_parse_prefix() {
        assert_eq!(
            ParsedReference::parse_prefix("${X:S/}/)/} rest", BSDMake),
            Ok((
                reference("X", vec![subst("}", ")", Default::default())]),
                11
            ))
        );
        assert_eq!(
            ParsedReference::parse_prefix("$X rest", BSDMake),
            Ok((reference("X", vec![]), 2))
        );
        assert_eq!(
            ParsedReference::parse_prefix("$(X:a=b) rest", GNUMake),
            Ok((reference("X", vec![sysv("a", "b")]), 8))
        );
    }

    #[test]
    fn test_parse_body() {
        assert_eq!(
            ParsedReference::parse_body("SRCS:M*.c:.c=.o", BSDMake),
            Ok(reference(
                "SRCS",
                vec![Modifier::Match("*.c".to_string()), sysv(".c", ".o")]
            ))
        );
        assert_eq!(
            ParsedReference::parse_body("X:ts:", BSDMake),
            Ok(reference("X", vec![Modifier::Separator(Some(':'))]))
        );
        assert_eq!(
            ParsedReference::parse_body("X:?a:b}", BSDMake),
            Ok(reference(
                "X",
                vec![Modifier::IfElse {
                    then_branch: lit("a"),
                    else_branch: lit("b}"),
                }]
            ))
        );
        assert_eq!(
            ParsedReference::parse_body("X:%.c=%.o", GNUMake),
            Ok(reference("X", vec![sysv("%.c", "%.o")]))
        );
    }

    #[test]
    fn test_gnu() {
        let gnu = |text| ParsedReference::parse(text, GNUMake).unwrap();
        assert_eq!(
            gnu("$(SRCS:.c=.o)"),
            reference("SRCS", vec![sysv(".c", ".o")])
        );
        assert_eq!(
            gnu("${SRCS:%.c=%.o}"),
            reference("SRCS", vec![sysv("%.c", "%.o")])
        );
        assert_eq!(gnu("$(FOO)"), reference("FOO", vec![]));
        assert_eq!(gnu("$@"), reference("@", vec![]));
        // Without `=` the colon is part of the variable name.
        assert_eq!(gnu("$(X:Q)"), reference("X:Q", vec![]));
        assert_eq!(
            gnu("$(X:a=b:c=d)"),
            reference("X", vec![sysv("a", "b:c=d")])
        );
        assert_eq!(
            gnu("$(X:$(A)=$(B:x=y)$$)"),
            reference(
                "X",
                vec![Modifier::SysVSubstitute {
                    from: ModifierArg::new([expr("$(A)")]),
                    to: ModifierArg::new([expr("$(B:x=y)"), text("$")]),
                }]
            )
        );
        assert_eq!(gnu("$($(V):a=b)"), reference("$(V)", vec![sysv("a", "b")]));
        // GNU make only counts the kind of parenthesis that opened the
        // reference.
        assert_eq!(gnu("$(X:{=})"), reference("X", vec![sysv("{", "}")]));
        assert_eq!(
            ParsedReference::parse("$(patsubst %.c,%.o,$(SRCS))", GNUMake),
            Err(ReferenceError::FunctionCall {
                name: "patsubst".to_string()
            })
        );
        // Not a known function, so a variable with a space in its name.
        assert_eq!(gnu("$(foo bar)"), reference("foo bar", vec![]));
        assert_eq!(
            ParsedReference::parse("$(X", GNUMake),
            Err(ReferenceError::Syntax {
                offset: 3,
                message: "unclosed reference, expecting ')'".to_string()
            })
        );
    }

    #[test]
    fn test_other_variants() {
        for variant in [POSIXMake, NMake] {
            assert_eq!(
                ParsedReference::parse("$(SRCS:.c=.o)", variant),
                Ok(reference("SRCS", vec![sysv(".c", ".o")]))
            );
            // These variants have no functions.
            assert_eq!(
                ParsedReference::parse("$(shell ls)", variant),
                Ok(reference("shell ls", vec![]))
            );
        }
    }

    #[test]
    fn test_netbsd_examples() {
        assert_eq!(
            bsd("${LIBDO.${lib}:U${.CURDIR}/../lib${lib}}"),
            reference(
                "LIBDO.${lib}",
                vec![Modifier::Default(ModifierArg::new([
                    expr("${.CURDIR}"),
                    text("/../lib"),
                    expr("${lib}"),
                ]))]
            )
        );
        assert_eq!(
            bsd("${SRCS:M*.[cly]:T:R:S/$/.o/g}"),
            reference(
                "SRCS",
                vec![
                    Modifier::Match("*.[cly]".to_string()),
                    Modifier::Tail,
                    Modifier::Root,
                    Modifier::Substitute {
                        from: lit(""),
                        to: lit(".o"),
                        anchor_start: false,
                        anchor_end: true,
                        flags: global(),
                    },
                ]
            )
        );
        assert_eq!(
            bsd("${MACHINE_CPU:S/^arm$/arm32/:tu}"),
            reference(
                "MACHINE_CPU",
                vec![
                    Modifier::Substitute {
                        from: lit("arm"),
                        to: lit("arm32"),
                        anchor_start: true,
                        anchor_end: true,
                        flags: Default::default(),
                    },
                    Modifier::ToUpper,
                ]
            )
        );
        assert_eq!(
            bsd("${.ALLSRC:O:u:@f@${f:T}@:ts\\n}"),
            reference(
                ".ALLSRC",
                vec![
                    Modifier::Order(SortOrder::Ascending),
                    Modifier::Unique,
                    Modifier::Loop {
                        var: "f".to_string(),
                        body: "${f:T}".to_string(),
                    },
                    Modifier::Separator(Some('\n')),
                ]
            )
        );
        assert_eq!(
            bsd("${MKDEBUG:Uno:tl:Mno:?:-g}"),
            reference(
                "MKDEBUG",
                vec![
                    Modifier::Default(lit("no")),
                    Modifier::ToLower,
                    Modifier::Match("no".to_string()),
                    Modifier::IfElse {
                        then_branch: lit(""),
                        else_branch: lit("-g"),
                    },
                ]
            )
        );
    }

    #[test]
    fn test_modifier_arg() {
        let arg = ModifierArg::new([text("a"), text(""), text("b"), expr("$X"), text("c")]);
        assert_eq!(arg.parts(), &[text("ab"), expr("$X"), text("c")]);
        assert_eq!(arg.as_literal(), None);
        assert_eq!(lit("ab").as_literal(), Some("ab".to_string()));
        assert_eq!(lit("").as_literal(), Some("".to_string()));
        assert!(lit("").is_empty());
        assert!(!arg.is_empty());
    }

    #[test]
    fn test_error_display() {
        assert_eq!(
            ReferenceError::UnknownModifier {
                offset: 4,
                modifier: "Z".to_string()
            }
            .to_string(),
            "unknown modifier ':Z' at offset 4"
        );
    }
}
