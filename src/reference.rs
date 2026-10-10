//! Parsing of variable references and their modifier chains.
//!
//! BSD make (NetBSD make and bmake) supports a rich set of modifiers in
//! variable references, e.g. `${SRCS:M*.c:S/.c/.o/g:Q}`. GNU make, POSIX
//! make and nmake only support substitution references such as
//! `$(SRCS:.c=.o)`.

use crate::MakefileVariant;
use std::collections::HashMap;
use std::ops::Range;

/// A piece of a [`ModifierArg`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ModifierArgPart {
    /// Literal text, with escapes removed.
    Literal(String),
    /// A nested expression such as `${FOO:Q}` or `$X`, as unexpanded text.
    /// It can be parsed with [`ParsedReference::parse`].
    ///
    /// In BSD make modifiers, it can also be `$` on its own, for a `$`
    /// followed by `:`, `)`, `}` or the end of the text where that does not
    /// end the argument, such as in `${:Ua$}`. make skips such a `$`, so it
    /// expands to nothing (in lint mode, it is an error).
    Expr(String),
    /// `$$` in an argument of a BSD make modifier.
    ///
    /// Its meaning depends on the modifier, so it is up to the caller.
    ///
    /// In the pattern of `:M` and `:N`, make expands the pattern as a whole,
    /// so this stands for `$`, except when expanding the value of a `:=`
    /// assignment with `.MAKE.SAVE_DOLLARS` enabled (the NetBSD default),
    /// where it stays `$$`.
    ///
    /// In all other arguments, make does not take `$$` as an escape. The
    /// first `$` is an expression without a valid name, which expands to
    /// nothing (in lint mode with `.MAKE.SAVE_DOLLARS` enabled, it is an
    /// error). The second `$` starts an expression with the text after it,
    /// so `$$x` and `$${x}` both give the value of `x`. The parser ends that
    /// expression where make does, and its text after the `$` is kept
    /// unchanged at the start of the next part, so `$${x}` gives this
    /// followed by the literal text `{x}`.
    ///
    /// If `$$` ends the argument, the second `$` is a literal `$`, or for the
    /// text to replace of `:S` it anchors the match at the end of the word,
    /// as a single `$` would. This does not apply to `:U` and `:D`, nor to
    /// a `:` that ends the argument of `:gmtime=` or `:localtime=`. Apart
    /// from that, a second `$` followed by `$`, `:`, `)` or `}` expands to
    /// nothing.
    ///
    /// Substitution references of other make variants have no such parts,
    /// as `$$` always stands for `$` there.
    EscapedDollar,
    /// An unescaped `&` in the replacement of `:S`, which stands for the
    /// text to replace.
    ///
    /// make replaces it with the expanded text to replace, the same text
    /// that it matches, so nested expressions in that text are not expanded
    /// again.
    Matched,
}

/// An argument of a modifier, made up of literal text and nested
/// expressions.
#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
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
                part => arg.0.push(part),
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

    /// The text of this argument, if it is only literal text, without
    /// nested expressions or other parts.
    pub fn as_literal_str(&self) -> Option<&str> {
        match self.0.as_slice() {
            [] => Some(""),
            [ModifierArgPart::Literal(text)] => Some(text),
            _ => None,
        }
    }

    /// The text of this argument, if it is only literal text.
    #[deprecated(since = "0.4.2", note = "use `as_literal_str` instead")]
    pub fn as_literal(&self) -> Option<String> {
        self.as_literal_str().map(str::to_string)
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
}

/// Flags of the `:S` and `:C` modifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct SubstituteFlags {
    /// `g`: replace all occurrences in each word, not just the first.
    pub global: bool,
    /// `1`: only modify the first word that matches.
    pub once: bool,
    /// `W`: treat the whole value as a single word.
    pub one_word: bool,
}

/// The order requested by the `:O` modifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    /// `:Mpattern`: the words that match the pattern, see
    /// [`ParsedReference`].
    Match(ModifierArg),
    /// `:Npattern`: the words that do not match the pattern, see
    /// [`ParsedReference`].
    NoMatch(ModifierArg),
    /// `:S/old/new/[1gW]`, with any delimiter instead of `/`.
    Substitute {
        /// The text to replace, without the anchors.
        from: ModifierArg,
        /// The replacement, in which an unescaped `&` is
        /// [`ModifierArgPart::Matched`].
        to: ModifierArg,
        /// `from` started with `^`: only match at the start of a word.
        anchor_start: bool,
        /// `from` ended with a single `$`: only match at the end of a word.
        /// make anchors the match for `$$` at the end as well, see
        /// [`ModifierArgPart::EscapedDollar`].
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
        /// The replacement. BSD make expands it again for each word that
        /// matches.
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
    ///
    /// make expands T before checking that it is a number of seconds, and
    /// only does so when the expression is evaluated, so T is not checked
    /// here.
    GmTime(Option<ModifierArg>),
    /// `:localtime` or `:localtime=T`: like [`Modifier::GmTime`] but in the
    /// local time zone.
    LocalTime(Option<ModifierArg>),
    /// `:mtime` or `:mtime=arg`: the modification time of each word, where
    /// `arg` is either a timestamp to use for missing files or `error`.
    Mtime(Option<String>),
    /// `:_` or `:_=var`: save the value in the given variable, `_` by
    /// default.
    Remember(String),
    /// A nested expression such as `${MODS}` in `${VAR:${MODS}}`, whose
    /// value is a list of modifiers to apply.
    ///
    /// The value is parsed as a list of modifiers on its own, as by
    /// [`ParsedReference::parse_body`] with a leading `:`. It may end in a
    /// `:`, so `tl:` has the same effect as `tl`.
    Indirect(String),
    /// A nested expression used as a list of modifiers like
    /// [`Modifier::Indirect`], that is directly followed by the next
    /// modifier instead of by `:` or the closing brace, such as `${M}` in
    /// `${VAR:${M}S,a,b,}`.
    ///
    /// make only accepts this if the expression expands to an empty string.
    /// Otherwise it reports an unknown modifier `:${`.
    UnseparatedIndirect(String),
}

/// A variable reference, split into the variable name and its modifiers.
///
/// Arguments of modifiers are not expanded. Depending on how BSD make treats
/// the argument, it is returned either as a [`ModifierArg`] or as a raw
/// [`String`]:
///
/// - A [`ModifierArg`] is used for most arguments (`:M`, `:N`, `:S`, `:C`,
///   `:U`, `:D`, `:?`, `:!cmd!`, the assignment modifiers, `:[...]`,
///   `:gmtime=`, `:localtime=` and the SysV substitution). Escapes are
///   already removed from its literal parts, and nested expressions are kept
///   as separate parts so that escaped text is never expanded again. The
///   pattern of `:M` and `:N` keeps the backslashes that make interprets
///   when matching, such as in `\*`.
/// - A raw [`String`] is used for the body of `:@`, which make expands as a
///   whole for each word. The evaluator should expand it like any other
///   value, so `$$` stands for a literal `$`.
///
/// The escapes that are removed follow NetBSD make:
///
/// - `:S`, `:C`, `:!cmd!`, `:?`, the assignment modifiers, `:[...]` and the
///   SysV substitution: `\` followed by the delimiter that ends the part, by
///   `\` or by `$` stands for that character. In the replacement of `:S`,
///   `\&` stands for `&` as well, and an unescaped `&` is returned as
///   [`ModifierArgPart::Matched`]. Other backslashes, such as those in
///   regular expressions for `:C`, are kept.
/// - `:U`, `:D`, `:gmtime=` and `:localtime=`: `\` followed by `:`, the
///   closing brace, `$` or `\`.
/// - `:M` and `:N`: `\` followed by `:` or the closing brace, but only if
///   an escaped `:`, closing brace or opening brace comes before the first
///   `$`. These escapes are then removed from the whole pattern, including
///   from nested expressions, so `${X:M\:${:U\:}}` gives `:${:U:}` while
///   `${X:M${:U\:}}` gives `${:U\:}`. A backslash before the opening brace
///   is kept, as it is in make.
/// - `:@`: in the variable name and body, `\@`, `\\` and `\$`.
///
/// `$$` in a [`ModifierArg`] is returned as
/// [`ModifierArgPart::EscapedDollar`]. It only stands for `$` in the pattern
/// of `:M` and `:N`; in other arguments, NetBSD make takes the second `$` as
/// the start of an expression, as described there.
///
/// # Example
/// ```
/// use makefile_lossless::{MakefileVariant, Modifier, ModifierArg, ParsedReference};
/// let parsed = ParsedReference::parse("${SRCS:M*.c:Q}", MakefileVariant::BSDMake).unwrap();
/// assert_eq!(parsed.name, "SRCS");
/// assert_eq!(
///     parsed.modifiers,
///     vec![Modifier::Match(ModifierArg::literal("*.c")), Modifier::Quote]
/// );
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParsedReference {
    /// The unexpanded name of the variable. It may contain nested
    /// expressions, as in `${VAR_${X}}`, and is empty in `${:Uvalue}`.
    pub name: String,
    /// The modifiers, in the order in which they are applied.
    pub modifiers: Vec<Modifier>,
}

/// The class of a [`ReferenceError::Syntax`] error.
///
/// Use this rather than matching on error messages, which are meant for
/// humans and may change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ReferenceSyntaxErrorKind {
    /// Text follows the reference where the end of the text was expected.
    TrailingText,
    /// The text does not start with `$`.
    ExpectedDollar,
    /// The text starts with `$$`, which stands for a literal `$`.
    EscapedDollar,
    /// A `$` is followed by nothing, or by a character that cannot be a
    /// variable name (make: "Dollar followed by nothing").
    MissingVariableName,
    /// An expression such as `${FOO` has no closing brace (make: "Unclosed
    /// expression" or "Unclosed variable").
    UnclosedExpression,
    /// A modifier is followed by something other than `:` or the closing
    /// brace (make: "Missing delimiter ':' after modifier").
    MissingModifierSeparator,
    /// `:S` or `:C` is not followed by a delimiter (make: "Missing
    /// delimiter for modifier").
    MissingModifierDelimiter,
    /// A modifier that make recognizes by its first characters is malformed,
    /// such as `:[]` or `:tx` (make: "Bad modifier").
    BadModifier,
    /// The variable name of `:@` contains a `$`.
    DollarInLoopVariable,
    /// The character number in `:ts\NNN` or `:ts\xNN` is out of range.
    InvalidCharacterNumber,
    /// The argument of `:range=` is not a number.
    InvalidRangeNumber,
    /// The argument of `:mtime=` is neither a number nor `error`.
    InvalidMtimeArgument,
    /// A part of a modifier such as `:S/from/to/` is not terminated by its
    /// delimiter (make: "Unfinished modifier").
    UnfinishedModifier,
    /// Expressions are nested more deeply than this crate supports.
    TooDeeplyNested,
}

/// An error parsing a variable reference.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ReferenceError {
    /// The reference is malformed.
    #[non_exhaustive]
    Syntax {
        /// The byte offset of the error in the text.
        offset: usize,
        /// The class of the error.
        kind: ReferenceSyntaxErrorKind,
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
    /// [`FunctionCall::parse_prefix`] parses it.
    FunctionCall {
        /// The name of the function.
        name: String,
    },
}

impl ReferenceError {
    /// The class of the error, if it is a [`ReferenceError::Syntax`] error.
    pub fn syntax_kind(&self) -> Option<ReferenceSyntaxErrorKind> {
        match self {
            ReferenceError::Syntax { kind, .. } => Some(*kind),
            _ => None,
        }
    }
}

impl std::fmt::Display for ReferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReferenceError::Syntax {
                offset, message, ..
            } => {
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

/// The built-in functions of GNU make, with the maximum number of arguments
/// they take. Any commas after the last argument are part of it.
const GNU_FUNCTIONS: &[(&str, usize)] = &[
    ("abspath", 1),
    ("addprefix", 2),
    ("addsuffix", 2),
    ("and", usize::MAX),
    ("basename", 1),
    ("call", usize::MAX),
    ("dir", 1),
    ("error", 1),
    ("eval", 1),
    ("file", 2),
    ("filter", 2),
    ("filter-out", 2),
    ("findstring", 2),
    ("firstword", 1),
    ("flavor", 1),
    ("foreach", 3),
    ("guile", 1),
    ("if", 3),
    ("info", 1),
    ("intcmp", 5),
    ("join", 2),
    ("lastword", 1),
    ("let", 3),
    ("notdir", 1),
    ("or", usize::MAX),
    ("origin", 1),
    ("patsubst", 3),
    ("realpath", 1),
    ("shell", 1),
    ("sort", 1),
    ("strip", 1),
    ("subst", 3),
    ("suffix", 1),
    ("value", 1),
    ("warning", 1),
    ("wildcard", 1),
    ("word", 2),
    ("wordlist", 3),
    ("words", 1),
];

/// A call of a GNU make built-in function, such as
/// `$(patsubst %.c,%.o,$(SRCS))`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct FunctionCall {
    /// The name of the function.
    pub name: String,
    /// The byte ranges of the arguments in the text the call was parsed
    /// from.
    ///
    /// They are split as GNU make does: at commas outside parentheses
    /// nested in `$(...)`, or braces nested in `${...}`, but no further
    /// than the number of arguments the function takes, so any further
    /// commas are part of the last argument. Blanks before the first
    /// argument are skipped; nothing else is trimmed.
    pub arguments: Vec<Range<usize>>,
}

impl FunctionCall {
    /// Parse the GNU make function call at the start of `text`, returning
    /// it and the length of its text.
    ///
    /// Returns `Ok(None)` if `text` does not start with a reference whose
    /// name is that of a built-in function followed by a blank, as
    /// [`ParsedReference::parse_prefix`] then returns something other than
    /// [`ReferenceError::FunctionCall`]. Returns an error if the reference
    /// is not closed.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::FunctionCall;
    ///
    /// let text = "$(if $(X),a,b,c) rest";
    /// let (call, len) = FunctionCall::parse_prefix(text).unwrap().unwrap();
    /// assert_eq!(call.name, "if");
    /// assert_eq!(len, 16);
    /// let args: Vec<_> = call.arguments.iter().map(|r| &text[r.clone()]).collect();
    /// assert_eq!(args, vec!["$(X)", "a", "b,c"]);
    /// ```
    pub fn parse_prefix(text: &str) -> Result<Option<(Self, usize)>, ReferenceError> {
        match Self::parse_partial_prefix(text)? {
            None => Ok(None),
            Some((call, Some(len))) => Ok(Some((call, len))),
            Some((_, None)) => {
                let close = if text.starts_with("${") { '}' } else { ')' };
                Err(unclosed_reference(text.len(), close))
            }
        }
    }

    /// Like [`Self::parse_prefix`], but for a call that is not closed,
    /// return the arguments so far, the last running to the end of `text`,
    /// and no length.
    ///
    /// This is meant for text that is still being typed, such as when
    /// showing which argument the cursor is in. Returns an error if `text`
    /// ends within the name of the function, as it is not known yet whether
    /// it is a call.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::FunctionCall;
    ///
    /// let text = "$(subst a,$(X)";
    /// let (call, len) = FunctionCall::parse_partial_prefix(text).unwrap().unwrap();
    /// assert_eq!(call.name, "subst");
    /// assert_eq!(len, None);
    /// let args: Vec<_> = call.arguments.iter().map(|r| &text[r.clone()]).collect();
    /// assert_eq!(args, vec!["a", "$(X)"]);
    ///
    /// let (_, len) = FunctionCall::parse_partial_prefix("$(info a) b").unwrap().unwrap();
    /// assert_eq!(len, Some(9));
    /// ```
    pub fn parse_partial_prefix(
        text: &str,
    ) -> Result<Option<(Self, Option<usize>)>, ReferenceError> {
        let (open, close) = match text.strip_prefix('$').and_then(|t| t.chars().next()) {
            Some('(') => ('(', ')'),
            Some('{') => ('{', '}'),
            _ => return Ok(None),
        };
        let body_start = 2;
        let Some(name_end) = text[body_start..]
            .find([' ', '\t', open, close])
            .map(|i| body_start + i)
        else {
            return Err(unclosed_reference(text.len(), close));
        };
        let name = &text[body_start..name_end];
        let Some(&(_, max_args)) = GNU_FUNCTIONS.iter().find(|(n, _)| *n == name) else {
            return Ok(None);
        };
        if !text[name_end..].starts_with([' ', '\t']) {
            return Ok(None);
        }
        let mut start = text.len() - text[name_end..].trim_start_matches([' ', '\t']).len();
        let mut arguments = Vec::new();
        let mut depth = 0usize;
        // The delimiters are ASCII, so they can't be part of another character.
        for (i, c) in text
            .bytes()
            .enumerate()
            .skip(start)
            .map(|(i, b)| (i, char::from(b)))
        {
            if c == open {
                depth += 1;
            } else if c == close {
                if depth == 0 {
                    arguments.push(start..i);
                    let call = FunctionCall {
                        name: name.to_string(),
                        arguments,
                    };
                    return Ok(Some((call, Some(i + 1))));
                }
                depth -= 1;
            } else if c == ',' && depth == 0 && arguments.len() + 1 < max_args {
                arguments.push(start..i);
                start = i + 1;
            }
        }
        arguments.push(start..text.len());
        let call = FunctionCall {
            name: name.to_string(),
            arguments,
        };
        Ok(Some((call, None)))
    }
}

fn unclosed_reference(offset: usize, close: char) -> ReferenceError {
    syntax_error(
        offset,
        ReferenceSyntaxErrorKind::UnclosedExpression,
        format!("unclosed reference, expecting '{}'", close),
    )
}

impl ParsedReference {
    /// Parse a complete variable reference such as `${FOO:Q}`, `$(FOO)` or
    /// `$X`.
    ///
    /// For [`MakefileVariant::BSDMake`] all modifiers are recognized. For the
    /// other variants the only modifier is the substitution reference
    /// `$(VAR:from=to)`, and a reference without `=` after the colon refers to
    /// a variable whose name contains the colon. For
    /// [`MakefileVariant::GNUMake`] a function call such as `$(wildcard *.c)`
    /// gives [`ReferenceError::FunctionCall`]. For [`MakefileVariant::NMake`]
    /// `$**`, all dependents of the target, refers to `**`; a filename part
    /// such as `$(@D)` or `$(**F)` is part of the name, as in GNU make. The
    /// strings of an nmake substitution can't invoke macros, so it ends at
    /// the first `)`, and `$` is literal in them.
    pub fn parse(text: &str, variant: MakefileVariant) -> Result<Self, ReferenceError> {
        let (parsed, end) = Self::parse_prefix(text, variant)?;
        if end != text.len() {
            return Err(syntax_error(
                end,
                ReferenceSyntaxErrorKind::TrailingText,
                "unexpected text after reference",
            ));
        }
        Ok(parsed)
    }

    /// Parse the variable reference at the start of `text`, returning it and
    /// the length of its text.
    ///
    /// This is useful for expanding a value: find the next `$`, parse the
    /// reference there and continue after it. Note that `$$` is not a
    /// reference, not even in nmake's `$$@`, the current target on a
    /// dependency line: the makefile parser reads that as a `$` followed by
    /// the reference `$@`, and likewise for `$$(@F)`.
    ///
    /// For [`MakefileVariant::BSDMake`], `\#` stands for `#`, as make
    /// replaces it before parsing any line other than a recipe line.
    pub fn parse_prefix(
        text: &str,
        variant: MakefileVariant,
    ) -> Result<(Self, usize), ReferenceError> {
        if variant != MakefileVariant::BSDMake {
            let mut parser = Parser::new(text);
            let parsed = parser.parse_simple_expr(variant)?;
            return Ok((parsed, parser.pos));
        }
        // Unescaping all of `text` would make parsing each reference in a
        // long value take time proportional to the rest of the value, so
        // parse a growing prefix until that succeeds. A prefix not ending in
        // a backslash unescapes to a prefix of the unescaped text. Within the
        // braces, the end of the text is never where an expression can end:
        // a modifier that reaches it is followed by a missing closing brace,
        // and the fallback to `from=to` after an unrecognized modifier needs
        // a closing brace before the end. So parsing a prefix either fails
        // or gives the same result as parsing all of `text`.
        let mut len = 64;
        loop {
            let mut end = len.min(text.len());
            while end < text.len() && (!text.is_char_boundary(end) || text[..end].ends_with('\\')) {
                end += 1;
            }
            let unescaped = UnescapedHash::new(&text[..end]);
            let mut parser = Parser::new(&unescaped.text);
            let result = parser.parse_expr();
            if end < text.len() && result.is_err() {
                len = end * 2;
                continue;
            }
            let parsed = result.map_err(|e| unescaped.map_error(e))?;
            return Ok((parsed, unescaped.original_offset(parser.pos)));
        }
    }

    /// Parse the text between the braces of a variable reference, such as
    /// `SRCS:M*.c` for `${SRCS:M*.c}`.
    ///
    /// The body extends to the end of `text`; there is no closing brace that
    /// ends it, so a `}` or `)` is treated like any other character where
    /// make would accept it.
    ///
    /// As in [`Self::parse_prefix`], `\#` stands for `#` for
    /// [`MakefileVariant::BSDMake`].
    pub fn parse_body(body: &str, variant: MakefileVariant) -> Result<Self, ReferenceError> {
        if variant != MakefileVariant::BSDMake {
            return parse_simple_body(body, 0, variant);
        }
        let unescaped = UnescapedHash::new(body);
        let mut parser = Parser::new(&unescaped.text);
        let delims = Delims {
            startc: None,
            endc: None,
        };
        let parsed = parser
            .parse_braced(delims)
            .map_err(|e| unescaped.map_error(e))?;
        if parser.pos != unescaped.text.len() {
            return Err(syntax_error(
                unescaped.original_offset(parser.pos),
                ReferenceSyntaxErrorKind::TrailingText,
                "unexpected text after reference",
            ));
        }
        Ok(parsed)
    }
}

/// A part of make text, as returned by [`split_references`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TextPart {
    /// Text without any `$`, as written.
    Literal(Range<usize>),
    /// `$$`, which stands for a literal `$`.
    EscapedDollar(Range<usize>),
    /// A variable reference or function call starting with `$`.
    Reference {
        /// The byte range of the reference, from the `$` up to and including
        /// the closing brace. If the reference is not closed, the range
        /// extends to the end of the text.
        range: Range<usize>,
        /// The result of [`ParsedReference::parse_prefix`] on the text from
        /// the start of `range`. Error offsets are relative to the start of
        /// `range`.
        ///
        /// This is usually the same as [`ParsedReference::parse`] on the
        /// text in `range`, but not always for
        /// [`MakefileVariant::BSDMake`]: make only treats a modifier as a
        /// SysV substitution if a closing brace follows, and looks for it
        /// past the end of the reference, so `${S:a=b{}}` is the reference
        /// `${S:a=b{}` followed by `}`.
        parsed: Result<ParsedReference, ReferenceError>,
    },
}

impl TextPart {
    /// The byte range of this part.
    pub fn range(&self) -> Range<usize> {
        match self {
            TextPart::Literal(range)
            | TextPart::EscapedDollar(range)
            | TextPart::Reference { range, .. } => range.clone(),
        }
    }
}

/// Split make text into literal text, `$$` escapes and references, with
/// byte ranges into `text`.
///
/// This is meant for text that does not come straight from the source,
/// such as [`Recipe::shell_text`](crate::Recipe::shell_text) or an include
/// path after expansion; for the source itself, use the
/// [`VariableReference`](crate::VariableReference) API. References are
/// recognized as [`ParsedReference::parse_prefix`] does: for
/// [`MakefileVariant::GNUMake`] a function call such as `$(wildcard *.c)`
/// is a [`TextPart::Reference`] whose `parsed` is a
/// [`ReferenceError::FunctionCall`], and for [`MakefileVariant::BSDMake`]
/// `\#` stands for `#`. A malformed reference is still a
/// [`TextPart::Reference`], with the error in `parsed`.
///
/// The parts are in order and together cover all of `text`.
///
/// # Example
/// ```
/// use makefile_lossless::{split_references, MakefileVariant, TextPart};
///
/// let parts = split_references("cp $(SRC) $$HOME/$@", MakefileVariant::GNUMake);
/// assert_eq!(
///     parts.iter().map(TextPart::range).collect::<Vec<_>>(),
///     vec![0..3, 3..9, 9..10, 10..12, 12..17, 17..19]
/// );
/// assert!(matches!(&parts[1], TextPart::Reference { parsed: Ok(r), .. } if r.name == "SRC"));
/// assert!(matches!(&parts[3], TextPart::EscapedDollar(_)));
/// ```
pub fn split_references(text: &str, variant: MakefileVariant) -> Vec<TextPart> {
    let mut parts = vec![];
    let mut pos = 0;
    while pos < text.len() {
        let Some(dollar) = text[pos..].find('$').map(|i| pos + i) else {
            parts.push(TextPart::Literal(pos..text.len()));
            break;
        };
        if dollar > pos {
            parts.push(TextPart::Literal(pos..dollar));
        }
        if text[dollar + 1..].starts_with('$') {
            parts.push(TextPart::EscapedDollar(dollar..dollar + 2));
            pos = dollar + 2;
            continue;
        }
        let (len, parsed) = reference_prefix(&text[dollar..], variant);
        pos = dollar + len;
        parts.push(TextPart::Reference {
            range: dollar..pos,
            parsed,
        });
    }
    parts
}

/// Parse the reference at the start of `text`, which starts with a `$`
/// that is not followed by another one, and return the length of its text
/// along with the result.
fn reference_prefix(
    text: &str,
    variant: MakefileVariant,
) -> (usize, Result<ParsedReference, ReferenceError>) {
    if variant == MakefileVariant::BSDMake {
        return match ParsedReference::parse_prefix(text, variant) {
            Ok((parsed, len)) => (len, Ok(parsed)),
            // The extent of a malformed BSD make expression is not known;
            // make itself gives up on the rest of the line.
            Err(e) => (text.len(), Err(e)),
        };
    }
    let mut parser = Parser::new(text);
    let result = parser.parse_simple_expr(variant);
    // The parser stops after the closing brace even if the body is not a
    // variable reference, and right after the `$` if there is no name or
    // closing brace.
    let unclosed = result.as_ref().err().and_then(ReferenceError::syntax_kind)
        == Some(ReferenceSyntaxErrorKind::UnclosedExpression);
    let len = if parser.pos <= 1 && unclosed {
        text.len()
    } else {
        parser.pos.max(1)
    };
    (len, result)
}

/// Find the extent of the BSD make expression at the start of `text`, as
/// [`ParsedReference::parse_prefix`] does, along with the byte ranges of the
/// expressions nested directly in it. `$$` counts as a nested expression,
/// but a `$` that make takes literally, such as the anchor in `:S/$/x/`,
/// does not.
///
/// Returns `None` if the expression is malformed.
#[cfg(test)]
pub(crate) fn bsd_expr_extent(text: &str) -> Option<(usize, Vec<Range<usize>>)> {
    BsdExprLine::new(UnescapedHash::new(text)).extent_at(0)
}

/// A line of BSD make text to find expressions in, along with the
/// expressions parsed in it so far, so that finding the expressions nested
/// in one another does not parse the inner ones again.
#[derive(Default)]
pub(crate) struct BsdExprLine {
    line: UnescapedHash,
    parsed: ParsedExprs,
}

impl BsdExprLine {
    pub(crate) fn new(line: UnescapedHash) -> Self {
        BsdExprLine {
            line,
            parsed: ParsedExprs::default(),
        }
    }

    /// Like [`bsd_expr_extent`], for the expression at offset `start` of
    /// the original text of the line. The offsets returned are relative to
    /// `start`.
    pub(crate) fn extent_at(&mut self, start: usize) -> Option<(usize, Vec<Range<usize>>)> {
        let line = &self.line;
        let unescaped_start = line.unescaped_offset(start);
        let mut parser = Parser::new(&line.text);
        parser.pos = unescaped_start;
        parser.parsed = std::mem::take(&mut self.parsed);
        let result = parser.skip_expr();
        self.parsed = std::mem::take(&mut parser.parsed);
        result.ok()?;
        let mut spans = parser.spans;
        spans.sort_by_key(|span| (span.start, std::cmp::Reverse(span.end)));
        let mut nested: Vec<Range<usize>> = vec![];
        for span in spans {
            // Skip the expression itself and the expressions nested further.
            if span.start == unescaped_start
                || nested.last().is_some_and(|last| span.start < last.end)
            {
                continue;
            }
            nested.push(span);
        }
        let original = |offset: usize| line.original_offset(offset) - start;
        let nested = nested
            .into_iter()
            .map(|span| original(span.start)..original(span.end))
            .collect();
        Some((original(parser.pos), nested))
    }
}

/// Text with `\#` replaced by `#`, as BSD make does before parsing a line
/// other than a recipe line. A backslash escaped by another backslash is
/// kept along with it.
#[derive(Default)]
pub(crate) struct UnescapedHash {
    text: String,
    /// The offsets in `text` of each `#` whose backslash was removed.
    removed: Vec<usize>,
    /// The offsets in the original text of the removed backslashes.
    escapes: Vec<usize>,
}

#[cfg(test)]
thread_local! {
    /// The number of bytes unescaped by [`UnescapedHash::new`] on this thread.
    static UNESCAPED_BYTES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// The number of braced BSD make expressions parsed on this thread.
    static PARSED_EXPRS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl UnescapedHash {
    /// `text` as is, for a recipe line, where BSD make does not unescape
    /// `\#`.
    pub(crate) fn verbatim(text: &str) -> Self {
        Self {
            text: text.to_string(),
            ..Default::default()
        }
    }

    pub(crate) fn new(original: &str) -> Self {
        #[cfg(test)]
        UNESCAPED_BYTES.with(|n| n.set(n.get() + original.len()));
        let mut text = String::with_capacity(original.len());
        let mut removed = vec![];
        let mut escapes = vec![];
        let mut chars = original.char_indices();
        while let Some((i, c)) = chars.next() {
            if c != '\\' {
                text.push(c);
                continue;
            }
            match chars.next().map(|(_, next)| next) {
                Some('#') => {
                    removed.push(text.len());
                    escapes.push(i);
                    text.push('#');
                }
                Some(next) => {
                    text.push('\\');
                    text.push(next);
                }
                None => text.push('\\'),
            }
        }
        UnescapedHash {
            text,
            removed,
            escapes,
        }
    }

    /// The offset in the unescaped text corresponding to `offset` in the
    /// original text.
    fn unescaped_offset(&self, offset: usize) -> usize {
        offset - self.escapes.partition_point(|&e| e < offset)
    }

    /// The offset in the original text corresponding to `offset` in the
    /// unescaped text. An offset at an unescaped `#` maps to its backslash.
    fn original_offset(&self, offset: usize) -> usize {
        offset + self.removed.partition_point(|&r| r < offset)
    }

    fn map_error(&self, error: ReferenceError) -> ReferenceError {
        error.map_offset(|offset| self.original_offset(offset))
    }
}

impl ReferenceError {
    /// Replace the offset of the error, if it has one, with `f(offset)`.
    pub(crate) fn map_offset(self, f: impl FnOnce(usize) -> usize) -> Self {
        match self {
            ReferenceError::Syntax {
                offset,
                kind,
                message,
            } => ReferenceError::Syntax {
                offset: f(offset),
                kind,
                message,
            },
            ReferenceError::UnknownModifier { offset, modifier } => {
                ReferenceError::UnknownModifier {
                    offset: f(offset),
                    modifier,
                }
            }
            ReferenceError::FunctionCall { name } => ReferenceError::FunctionCall { name },
        }
    }
}

pub(crate) fn syntax_error(
    offset: usize,
    kind: ReferenceSyntaxErrorKind,
    message: impl Into<String>,
) -> ReferenceError {
    ReferenceError::Syntax {
        offset,
        kind,
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

/// How deeply references are nested at most, so that parsing them and
/// building and dropping the tree does not run out of stack.
pub(crate) const MAX_DEPTH: usize = 128;

/// The outcome of parsing the expression at some position.
struct ParsedExpr {
    result: Result<(), ReferenceError>,
    /// The position after the expression.
    end: usize,
    /// The spans found in it.
    spans: Vec<Range<usize>>,
    /// Whether parsing it reached [`MAX_DEPTH`], so that the outcome
    /// depends on the depth.
    limited: bool,
}

/// The braced expressions parsed so far, by their start, the length of the
/// text and the depth, since a modifier may be parsed in more than one way
/// and the expressions in a pattern are parsed again on their own. Without
/// this, parsing nested expressions takes time exponential in their depth.
#[derive(Default)]
struct ParsedExprs {
    by_depth: HashMap<(usize, usize, usize), ParsedExpr>,
    /// By start and length of the text, the greatest depth at which the
    /// expression was parsed without reaching [`MAX_DEPTH`]. The outcome is
    /// the same at any lesser depth, such as when the expressions nested
    /// in an expression are looked at on their own.
    unlimited: HashMap<(usize, usize), usize>,
}

impl ParsedExprs {
    fn get(&self, pos: usize, len: usize, depth: usize) -> Option<&ParsedExpr> {
        self.by_depth.get(&(pos, len, depth)).or_else(|| {
            let max_depth = *self.unlimited.get(&(pos, len))?;
            (max_depth >= depth).then(|| &self.by_depth[&(pos, len, max_depth)])
        })
    }

    fn insert(&mut self, pos: usize, len: usize, depth: usize, parsed: ParsedExpr) {
        if !parsed.limited {
            let max_depth = self.unlimited.entry((pos, len)).or_insert(depth);
            *max_depth = (*max_depth).max(depth);
        }
        self.by_depth.insert((pos, len, depth), parsed);
    }
}

struct Parser<'a> {
    text: &'a str,
    pos: usize,
    /// The byte ranges of the expressions found so far, including `$$`.
    spans: Vec<Range<usize>>,
    /// The number of expressions being parsed that enclose the position.
    depth: usize,
    parsed: ParsedExprs,
    /// The number of times [`MAX_DEPTH`] was reached, including where the
    /// error was not reported.
    depth_limit_reached: usize,
    /// Whether only the extent of the expression being parsed is needed.
    skipping: bool,
}

impl<'a> Parser<'a> {
    fn new(text: &'a str) -> Self {
        Parser {
            text,
            pos: 0,
            spans: vec![],
            depth: 0,
            parsed: ParsedExprs::default(),
            depth_limit_reached: 0,
            skipping: false,
        }
    }

    /// A parser for `text`, a prefix of the text of this one, at the same
    /// depth, sharing the expressions parsed so far. Hand them back with
    /// [`Self::join`].
    fn fork(&mut self, text: &'a str, pos: usize) -> Parser<'a> {
        Parser {
            text,
            pos,
            spans: vec![],
            depth: self.depth,
            parsed: std::mem::take(&mut self.parsed),
            depth_limit_reached: self.depth_limit_reached,
            skipping: self.skipping,
        }
    }

    fn join(&mut self, other: &mut Parser<'a>) {
        self.parsed = std::mem::take(&mut other.parsed);
        self.depth_limit_reached = other.depth_limit_reached;
    }

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
        if self.depth >= MAX_DEPTH {
            self.depth_limit_reached += 1;
            return Err(syntax_error(
                self.pos,
                ReferenceSyntaxErrorKind::TooDeeplyNested,
                "expressions nested too deeply",
            ));
        }
        self.depth += 1;
        let result = self.parse_expr_inner();
        self.depth -= 1;
        result
    }

    /// Parse a nested expression starting at `$`, like
    /// [`Self::parse_expr`], without the result.
    fn skip_expr(&mut self) -> Result<(), ReferenceError> {
        let (pos, len, depth) = (self.pos, self.text.len(), self.depth);
        if let Some(parsed) = self.parsed.get(pos, len, depth) {
            self.pos = parsed.end;
            self.spans.extend(parsed.spans.iter().cloned());
            if parsed.limited {
                self.depth_limit_reached += 1;
            }
            return parsed.result.clone();
        }
        let spans = self.spans.len();
        let reached = self.depth_limit_reached;
        let skipping = std::mem::replace(&mut self.skipping, true);
        let result = self.parse_expr().map(|_| ());
        self.skipping = skipping;
        let parsed = ParsedExpr {
            result: result.clone(),
            end: self.pos,
            spans: self.spans[spans..].to_vec(),
            limited: self.depth_limit_reached != reached,
        };
        self.parsed.insert(pos, len, depth, parsed);
        result
    }

    fn parse_expr_inner(&mut self) -> Result<ParsedReference, ReferenceError> {
        let start = self.pos;
        if self.bump() != Some('$') {
            return Err(syntax_error(
                start,
                ReferenceSyntaxErrorKind::ExpectedDollar,
                "expected '$'",
            ));
        }
        let endc = match self.peek() {
            Some('(') => ')',
            Some('{') => '}',
            Some('$') => {
                return Err(syntax_error(
                    start,
                    ReferenceSyntaxErrorKind::EscapedDollar,
                    "'$$' is an escaped dollar, not a reference",
                ))
            }
            None | Some(':' | ')' | '}') => {
                return Err(syntax_error(
                    start,
                    ReferenceSyntaxErrorKind::MissingVariableName,
                    "missing variable name after '$'",
                ))
            }
            Some(c) => {
                self.bump();
                self.spans.push(start..self.pos);
                return Ok(ParsedReference {
                    name: c.to_string(),
                    modifiers: vec![],
                });
            }
        };
        #[cfg(test)]
        PARSED_EXPRS.with(|n| n.set(n.get() + 1));
        let startc = self.bump();
        let parsed = self.parse_braced(Delims {
            startc,
            endc: Some(endc),
        })?;
        self.spans.push(start..self.pos);
        Ok(parsed)
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
            ReferenceSyntaxErrorKind::UnclosedExpression,
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
                    self.skip_expr()?;
                }
                None => {
                    return Err(syntax_error(
                        self.pos,
                        ReferenceSyntaxErrorKind::MissingVariableName,
                        "missing variable name after '$'",
                    ))
                }
                // Like make, only skip the '$' since the next character
                // cannot be a variable name.
                Some(':' | ')' | '}') => {
                    self.bump();
                }
                Some(_) => {
                    let start = self.pos;
                    self.bump_n(2);
                    self.spans.push(start..self.pos);
                }
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
            let modifier = self.parse_modifier(delims)?;
            let unseparated = matches!(modifier, Modifier::UnseparatedIndirect(_));
            modifiers.push(modifier);
            match self.peek() {
                Some(':') => {
                    self.bump();
                }
                c if unseparated || delims.is_delimiter(c) => {}
                _ => {
                    return Err(syntax_error(
                        self.pos,
                        ReferenceSyntaxErrorKind::MissingModifierSeparator,
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
        let spans = self.spans.len();
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
                    false,
                )?))
            }
            ':' => self.parse_assign(delims)?,
            '?' => {
                self.bump();
                let then_branch = self.parse_part(Some(':'), None, false)?;
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
                Some(Modifier::GmTime(self.parse_time_arg(delims)?))
            }
            'l' if self.at_word_or_eq("localtime", delims) => {
                self.bump_n("localtime".len());
                Some(Modifier::LocalTime(self.parse_time_arg(delims)?))
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
                let pattern_start = self.pos;
                let unescaped = self.parse_match_pattern(delims);
                let mut pattern = self.record_raw_spans(pattern_start..self.pos);
                // Parsing the unescaped pattern again when only skipping
                // would make nested patterns take exponential time.
                if let Some(unescaped) = unescaped.filter(|_| !self.skipping) {
                    let mut parser = Parser::new(&unescaped);
                    parser.depth = self.depth;
                    pattern = parser.split_raw();
                }
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
        self.spans.truncate(spans);
        if let Some(modifier) = self.parse_sysv(delims)? {
            return Ok(modifier);
        }
        // An indirect modifier that expands to an empty string may be
        // followed directly by the next modifier.
        if first == '$' {
            let mut arg = ModifierArg::default();
            self.parse_nested_expr(&mut arg)?;
            return Ok(Modifier::UnseparatedIndirect(
                self.text[start..self.pos].to_string(),
            ));
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
            ReferenceSyntaxErrorKind::BadModifier,
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
            .parse_part(Some('@'), None, false)?
            .as_literal_str()
            .filter(|var| !var.contains('$'))
            .map(str::to_string)
            .ok_or_else(|| {
                syntax_error(
                    start,
                    ReferenceSyntaxErrorKind::DollarInLoopVariable,
                    "in the :@ modifier, the variable name must not contain a dollar",
                )
            })?;
        let body_start = self.pos;
        let body = self.parse_balanced_part('@')?;
        self.record_raw_spans(body_start..self.pos - 1);
        Ok(Modifier::Loop { var, body })
    }

    fn parse_words(&mut self, delims: Delims) -> Result<Modifier, ReferenceError> {
        let start = self.pos;
        self.bump();
        let arg = self.parse_part(Some(']'), None, false)?;
        if !delims.is_delimiter(self.peek()) {
            return Err(self.bad_modifier(start, delims));
        }
        let Some(text) = arg.as_literal_str() else {
            return Ok(Modifier::Words(WordSelector::Unexpanded(arg)));
        };
        let selector = match text {
            "#" => WordSelector::Count,
            "*" => WordSelector::OneWord,
            "@" => WordSelector::Split,
            _ => {
                let (first, last) = match text.split_once("..") {
                    Some((first, last)) => (parse_int_base0(first), parse_int_base0(last)),
                    None => {
                        let n = parse_int_base0(text);
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
            syntax_error(
                start,
                ReferenceSyntaxErrorKind::MissingModifierDelimiter,
                format!("missing delimiter for modifier ':{}'", name),
            )
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
        let from = self.parse_part(Some(delim), Some(&mut anchor_end), false)?;
        let to = self.parse_part(Some(delim), None, true)?;
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
        let regex = self.parse_part(Some(delim), None, false)?;
        let replacement = self.parse_part(Some(delim), None, false)?;
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
                ReferenceSyntaxErrorKind::InvalidCharacterNumber,
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

    /// Parse the argument of `:gmtime=` or `:localtime=`, if any, up to the
    /// next delimiter.
    fn parse_time_arg(&mut self, delims: Delims) -> Result<Option<ModifierArg>, ReferenceError> {
        if self.peek() != Some('=') {
            return Ok(None);
        }
        self.bump();
        let mut arg = ModifierArg::default();
        while !delims.is_delimiter(self.peek()) {
            let c = self.peek().expect("end of text is a delimiter");
            let next = self.peek_nth(1);
            if c == '\\' {
                if let Some(next) =
                    next.filter(|&n| delims.is_delimiter(Some(n)) || n == '$' || n == '\\')
                {
                    arg.push_char(next);
                    self.bump_n(2);
                    continue;
                }
            }
            if c == '$' && next == Some('$') {
                self.parse_escaped_dollar(&mut arg, delims.endc)?;
                continue;
            }
            // As in make, a `$` just before the closing brace is literal.
            if c == '$' && next != delims.endc {
                self.parse_nested_expr(&mut arg)?;
                continue;
            }
            arg.push_char(c);
            self.bump();
        }
        Ok(Some(arg))
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
                ReferenceSyntaxErrorKind::InvalidRangeNumber,
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
            ReferenceSyntaxErrorKind::InvalidMtimeArgument,
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
        let from = self.parse_part(Some('='), None, false)?;
        let to = self.parse_part_to_end(delims)?;
        Ok(Some(Modifier::SysVSubstitute { from, to }))
    }

    /// Parse the pattern of `:M` or `:N`.
    ///
    /// As in make, escaped delimiters are only unescaped if an escape comes
    /// before the first `$`, and then throughout the pattern, including in
    /// nested expressions. Returns the unescaped pattern if that happened.
    fn parse_match_pattern(&mut self, delims: Delims) -> Option<String> {
        let start = self.pos;
        let mut unescape = false;
        let mut has_expr = false;
        let mut nest = 0;
        while let Some(c) = self.peek() {
            if c == ':' && nest == 0 {
                break;
            }
            if c == '\\' {
                if let Some(next) = self.peek_nth(1) {
                    if delims.is_delimiter(Some(next)) || Some(next) == delims.startc {
                        unescape |= !has_expr;
                        self.bump_n(2);
                        continue;
                    }
                }
            }
            if c == '$' {
                has_expr = true;
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
            self.bump();
        }
        if !unescape {
            return None;
        }
        let raw = &self.text[start..self.pos];
        let mut pattern = String::with_capacity(raw.len());
        let mut chars = raw.chars().peekable();
        while let Some(c) = chars.next() {
            if c == '\\' {
                if let Some(&next) = chars.peek() {
                    if delims.is_delimiter(Some(next)) {
                        continue;
                    }
                }
            }
            pattern.push(c);
        }
        Some(pattern)
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
            if c == '$' && self.peek_nth(1) == Some('$') {
                self.parse_escaped_dollar(&mut arg, delims.endc)?;
                continue;
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

    /// Parse `$$` in an argument other than the pattern of `:M` or `:N`,
    /// where `end` is the delimiter that ends the argument.
    ///
    /// make does not take `$$` as an escape there: the first `$` expands to
    /// nothing, and the second one starts an expression unless it is followed
    /// by `end`. That expression is skipped as make does, and the text after
    /// the second `$` is added as literal text, so that `$${x}` gives
    /// `EscapedDollar` and `{x}`.
    fn parse_escaped_dollar(
        &mut self,
        arg: &mut ModifierArg,
        end: Option<char>,
    ) -> Result<(), ReferenceError> {
        let start = self.pos;
        self.bump_n(2);
        self.spans.push(start..self.pos);
        arg.0.push(ModifierArgPart::EscapedDollar);
        let next = self.peek();
        if next == end {
            return Ok(());
        }
        match next {
            None | Some('$' | ':' | ')' | '}') => {}
            Some('(' | '{') => {
                let spans = self.spans.len();
                self.pos -= 1;
                self.skip_expr()?;
                self.spans.truncate(spans);
                arg.push_str(&self.text[start + 2..self.pos]);
            }
            Some(c) => {
                self.bump();
                arg.push_char(c);
            }
        }
        Ok(())
    }

    /// Parse a nested expression starting at `$`, adding it to `arg`.
    fn parse_nested_expr(&mut self, arg: &mut ModifierArg) -> Result<(), ReferenceError> {
        let start = self.pos;
        match self.peek_nth(1) {
            Some('(' | '{') => {
                self.skip_expr()?;
                arg.push_expr(&self.text[start..self.pos]);
            }
            Some('$') => {
                self.bump_n(2);
                self.spans.push(start..self.pos);
                arg.0.push(ModifierArgPart::EscapedDollar);
            }
            // Like make, only skip the '$' since the next character cannot
            // be a variable name.
            None | Some(':' | ')' | '}') => {
                self.bump();
                arg.push_expr("$");
            }
            Some(_) => {
                self.bump_n(2);
                self.spans.push(start..self.pos);
                arg.push_expr(&self.text[start..self.pos]);
            }
        }
        Ok(())
    }

    /// Record the expressions in the raw text at `raw`, which make expands
    /// only after parsing the modifier, and split the text into literal
    /// text and those expressions.
    fn record_raw_spans(&mut self, raw: Range<usize>) -> ModifierArg {
        let mut parser = self.fork(&self.text[..raw.end], raw.start);
        let arg = parser.split_raw();
        self.join(&mut parser);
        self.spans.extend(parser.spans);
        arg
    }

    /// Split the rest of the text into literal text, the expressions in it
    /// and `$$`.
    ///
    /// Make reports an error for an invalid expression only when expanding
    /// the text, so the text from there on is kept as one expression. A `$`
    /// at the end of the text is kept as an expression as well; make
    /// expands it to nothing.
    fn split_raw(&mut self) -> ModifierArg {
        let mut arg = ModifierArg::default();
        let mut unclosed = None;
        while let Some(offset) = self.rest().find('$') {
            if unclosed.is_none() {
                arg.push_str(&self.rest()[..offset]);
            }
            self.pos += offset;
            let dollar = self.pos;
            match self.peek_nth(1) {
                None => {
                    self.bump();
                    unclosed.get_or_insert(dollar);
                }
                Some('(' | '{') => {
                    let mut nested = self.fork(self.text, dollar);
                    let ok = nested.skip_expr().is_ok();
                    self.join(&mut nested);
                    if ok {
                        self.spans.extend(nested.spans);
                        self.pos = nested.pos;
                    } else {
                        self.bump();
                        unclosed.get_or_insert(dollar);
                    }
                }
                Some(_) => {
                    self.bump_n(2);
                    self.spans.push(dollar..self.pos);
                }
            }
            if unclosed.is_none() {
                match &self.text[dollar..self.pos] {
                    "$$" => arg.0.push(ModifierArgPart::EscapedDollar),
                    expr => arg.push_expr(expr),
                }
            }
        }
        match unclosed {
            Some(start) => arg.push_expr(&self.text[start..]),
            None => arg.push_str(self.rest()),
        }
        arg
    }

    /// Parse a part of a modifier up to and including `delim`, where `None`
    /// stands for the end of the text.
    ///
    /// If `anchor_end` is given, a `$` just before the delimiter sets it
    /// rather than being added to the part. If `matched` is set, as for the
    /// replacement of `:S`, `&` gives [`ModifierArgPart::Matched`].
    fn parse_part(
        &mut self,
        delim: Option<char>,
        mut anchor_end: Option<&mut bool>,
        matched: bool,
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
                    ReferenceSyntaxErrorKind::UnfinishedModifier,
                    format!("unfinished modifier ('{}' missing)", delim.unwrap()),
                ));
            };
            let next = self.peek_nth(1);
            if c == '\\' {
                if let Some(next) = next {
                    if Some(next) == delim
                        || next == '\\'
                        || next == '$'
                        || (next == '&' && matched)
                    {
                        arg.push_char(next);
                        self.bump_n(2);
                        continue;
                    }
                }
            }
            if c != '$' {
                if matched && c == '&' {
                    arg.0.push(ModifierArgPart::Matched);
                } else {
                    arg.push_char(c);
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
            if next == Some('$') {
                self.parse_escaped_dollar(&mut arg, delim)?;
                continue;
            }
            self.parse_nested_expr(&mut arg)?;
        }
    }

    /// Parse a part that extends to the closing brace, without consuming the
    /// brace.
    fn parse_part_to_end(&mut self, delims: Delims) -> Result<ModifierArg, ReferenceError> {
        let arg = self.parse_part(delims.endc, None, false)?;
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
                    ReferenceSyntaxErrorKind::UnfinishedModifier,
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
            return Err(syntax_error(
                start,
                ReferenceSyntaxErrorKind::ExpectedDollar,
                "expected '$'",
            ));
        }
        let endc = match self.peek() {
            Some('(') => ')',
            Some('{') => '}',
            Some('$') => {
                return Err(syntax_error(
                    start,
                    ReferenceSyntaxErrorKind::EscapedDollar,
                    "'$$' is an escaped dollar, not a reference",
                ))
            }
            None => {
                return Err(syntax_error(
                    start,
                    ReferenceSyntaxErrorKind::MissingVariableName,
                    "missing variable name after '$'",
                ))
            }
            Some(c) => {
                self.bump();
                let mut name = c.to_string();
                // nmake's `$**` is all dependents of the target.
                if variant == MakefileVariant::NMake && c == '*' && self.peek() == Some('*') {
                    self.bump();
                    name.push('*');
                }
                return Ok(ParsedReference {
                    name,
                    modifiers: vec![],
                });
            }
        };
        let body_start = self.pos + 1;
        if variant == MakefileVariant::NMake && endc == ')' {
            if let Some(parsed) = self.parse_nmake_substitution(body_start)? {
                return Ok(parsed);
            }
        }
        let body_end = self.text.len()
            - skip_balanced(&self.text[self.pos..])
                .ok_or_else(|| {
                    syntax_error(
                        self.text.len(),
                        ReferenceSyntaxErrorKind::UnclosedExpression,
                        format!("unclosed reference, expecting '{}'", endc),
                    )
                })?
                .len();
        self.pos = body_end;
        parse_simple_body(&self.text[body_start..body_end - 1], body_start, variant)
    }

    /// Parse nmake's `$(name:string1=string2)` with its body at
    /// `body_start`, or return `None` if the reference is not one.
    ///
    /// The strings "can't invoke macros", so the reference ends at the first
    /// `)` and `$` is literal in them.
    fn parse_nmake_substitution(
        &mut self,
        body_start: usize,
    ) -> Result<Option<ParsedReference>, ReferenceError> {
        let rest = &self.text[body_start..];
        let name_len = nmake_macro_name_len(rest);
        if name_len == 0 || !rest[name_len..].starts_with(':') {
            return Ok(None);
        }
        let Some(len) = rest.find(')') else {
            return Err(syntax_error(
                self.text.len(),
                ReferenceSyntaxErrorKind::UnclosedExpression,
                "unclosed reference, expecting ')'",
            ));
        };
        let body = &rest[..len];
        self.pos = body_start + len + 1;
        let Some((from, to)) = body[name_len + 1..].split_once('=') else {
            return Ok(Some(ParsedReference {
                name: body.to_string(),
                modifiers: vec![],
            }));
        };
        Ok(Some(ParsedReference {
            name: body[..name_len].to_string(),
            modifiers: vec![Modifier::SysVSubstitute {
                from: ModifierArg::literal(from),
                to: ModifierArg::literal(to),
            }],
        }))
    }
}

/// The length of the macro name at the start of `text` that the parser
/// takes as the name of an nmake substitution: a run of identifier
/// characters, `**`, or another single character that does not end a name.
fn nmake_macro_name_len(text: &str) -> usize {
    let identifier = text
        .find(|c: char| !(c.is_ascii_alphanumeric() || "_/.-%".contains(c)))
        .unwrap_or(text.len());
    if identifier > 0 {
        return identifier;
    }
    if text.starts_with("**") {
        return 2;
    }
    match text.chars().next() {
        Some(c) if !c.is_whitespace() && !"$(){}:=#\\^\"'".contains(c) => c.len_utf8(),
        _ => 0,
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
            if GNU_FUNCTIONS.iter().any(|(n, _)| *n == name) {
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
                                ReferenceSyntaxErrorKind::UnclosedExpression,
                                "unclosed nested reference",
                            )
                        })?
                        .len()
            }
            Some(c) => c.len_utf8(),
            None => {
                return Err(syntax_error(
                    offset + text.len() - rest.len() + i,
                    ReferenceSyntaxErrorKind::MissingVariableName,
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

    /// The parts of `text`, as `(kind, text)` where kind is `L` for a
    /// literal, `$` for `$$`, `R` for a reference and `E` for a malformed
    /// reference.
    fn split(text: &str, variant: MakefileVariant) -> Vec<(char, &str)> {
        let parts = split_references(text, variant);
        assert_eq!(
            parts.iter().map(TextPart::range).fold(0, |end, range| {
                assert_eq!(range.start, end);
                range.end
            }),
            text.len()
        );
        parts
            .into_iter()
            .map(|part| {
                let kind = match &part {
                    TextPart::Literal(_) => 'L',
                    TextPart::EscapedDollar(_) => '$',
                    TextPart::Reference { parsed: Ok(_), .. } => 'R',
                    TextPart::Reference { parsed: Err(_), .. } => 'E',
                };
                (kind, &text[part.range()])
            })
            .collect()
    }

    #[test]
    fn test_split_references() {
        assert_eq!(
            split("a $(B) ${C}d$E$$f", GNUMake),
            vec![
                ('L', "a "),
                ('R', "$(B)"),
                ('L', " "),
                ('R', "${C}"),
                ('L', "d"),
                ('R', "$E"),
                ('$', "$$"),
                ('L', "f"),
            ]
        );
        assert_eq!(split("", GNUMake), vec![]);
        assert_eq!(split("plain", GNUMake), vec![('L', "plain")]);
        assert_eq!(split("$$$$", GNUMake), vec![('$', "$$"), ('$', "$$")]);
        assert_eq!(split("$$$X", GNUMake), vec![('$', "$$"), ('R', "$X")]);
    }

    #[test]
    fn test_split_references_parsed() {
        let parts = split_references("$(SRCS:.c=.o)$@", GNUMake);
        assert_eq!(
            parts,
            vec![
                TextPart::Reference {
                    range: 0..13,
                    parsed: ParsedReference::parse("$(SRCS:.c=.o)", GNUMake),
                },
                TextPart::Reference {
                    range: 13..15,
                    parsed: Ok(ParsedReference {
                        name: "@".to_string(),
                        modifiers: vec![],
                    }),
                },
            ]
        );
    }

    #[test]
    fn test_split_references_nested() {
        assert_eq!(
            split("x$(A_$(B))y${C$(D)}", GNUMake),
            vec![
                ('L', "x"),
                ('R', "$(A_$(B))"),
                ('L', "y"),
                ('R', "${C$(D)}"),
            ]
        );
    }

    fn call_args(text: &str) -> Option<(String, Vec<&str>, usize)> {
        let (call, len) = FunctionCall::parse_prefix(text).unwrap()?;
        let args = call.arguments.iter().map(|r| &text[r.clone()]).collect();
        Some((call.name, args, len))
    }

    #[test]
    fn test_function_call_arguments() {
        assert_eq!(
            call_args("$(patsubst %.c,%.o,$(SRCS)) x"),
            Some(("patsubst".to_string(), vec!["%.c", "%.o", "$(SRCS)"], 27))
        );
        assert_eq!(
            call_args("${subst a,b,c}"),
            Some(("subst".to_string(), vec!["a", "b", "c"], 14))
        );
        assert_eq!(
            call_args("$(wildcard \t *.c )"),
            Some(("wildcard".to_string(), vec!["*.c "], 18))
        );
        assert_eq!(
            call_args("$(info )"),
            Some(("info".to_string(), vec![""], 8))
        );
        assert_eq!(
            call_args("$(if ,a,)"),
            Some(("if".to_string(), vec!["", "a", ""], 9))
        );
    }

    #[test]
    fn test_function_call_arguments_max() {
        // Commas after the last argument a function takes are part of it.
        assert_eq!(
            call_args("$(subst a,b,c,d)"),
            Some(("subst".to_string(), vec!["a", "b", "c,d"], 16))
        );
        assert_eq!(
            call_args("$(info a,b)"),
            Some(("info".to_string(), vec!["a,b"], 11))
        );
        assert_eq!(
            call_args("$(call f,a,b,c,d)"),
            Some(("call".to_string(), vec!["f", "a", "b", "c", "d"], 17))
        );
    }

    #[test]
    fn test_function_call_arguments_nesting() {
        assert_eq!(
            call_args("$(word 2,$(x,y) (a,b))"),
            Some(("word".to_string(), vec!["2", "$(x,y) (a,b)"], 22))
        );
        // Only the delimiters of the call itself nest, as in GNU make, which
        // fails on `$(if ${x,y},T,F)` with an unterminated reference.
        assert_eq!(
            call_args("$(if ${x,y},T,F)"),
            Some(("if".to_string(), vec!["${x", "y}", "T,F"], 16))
        );
        assert_eq!(
            call_args("${if $(x,y),T,F}"),
            Some(("if".to_string(), vec!["$(x", "y)", "T,F"], 16))
        );
        assert_eq!(
            call_args("${if ${x,y},T,F}"),
            Some(("if".to_string(), vec!["${x,y}", "T", "F"], 16))
        );
    }

    #[test]
    fn test_function_call_not_a_call() {
        assert_eq!(call_args("$(X)"), None);
        assert_eq!(call_args("$(info)"), None);
        assert_eq!(call_args("$(info(x) y)"), None);
        assert_eq!(call_args("$(foo a,b)"), None);
        assert_eq!(call_args("$X"), None);
        assert_eq!(call_args("$$(info a)"), None);
        assert_eq!(call_args("x"), None);
    }

    #[test]
    fn test_function_call_unclosed() {
        assert_eq!(
            FunctionCall::parse_prefix("$(subst a,b,$(c)"),
            Err(syntax_error(
                16,
                ReferenceSyntaxErrorKind::UnclosedExpression,
                "unclosed reference, expecting ')'"
            ))
        );
        assert_eq!(
            FunctionCall::parse_prefix("${info").map_err(|e| e.syntax_kind()),
            Err(Some(ReferenceSyntaxErrorKind::UnclosedExpression))
        );
    }

    #[test]
    fn test_function_call_partial() {
        let partial = |text| {
            let (call, len) = FunctionCall::parse_partial_prefix(text).unwrap()?;
            let args: Vec<_> = call.arguments.iter().map(|r| &text[r.clone()]).collect();
            Some((call.name, args, len))
        };
        assert_eq!(
            partial("$(subst a,"),
            Some(("subst".to_string(), vec!["a", ""], None))
        );
        assert_eq!(
            partial("$(subst a,b,c,d"),
            Some(("subst".to_string(), vec!["a", "b", "c,d"], None))
        );
        assert_eq!(
            partial("${if ${x,y},T"),
            Some(("if".to_string(), vec!["${x,y}", "T"], None))
        );
        assert_eq!(
            partial("$(info "),
            Some(("info".to_string(), vec![""], None))
        );
        assert_eq!(
            partial("$(subst a,b,c) x"),
            Some(("subst".to_string(), vec!["a", "b", "c"], Some(14)))
        );
        assert_eq!(partial("$(foo a,"), None);
        assert_eq!(partial("$X"), None);
        assert_eq!(
            FunctionCall::parse_partial_prefix("$(subst").map_err(|e| e.syntax_kind()),
            Err(Some(ReferenceSyntaxErrorKind::UnclosedExpression))
        );
    }

    #[test]
    fn test_split_references_function_call() {
        let parts = split_references("$(wildcard *.c) $(X)", GNUMake);
        assert_eq!(
            parts[0],
            TextPart::Reference {
                range: 0..15,
                parsed: Err(ReferenceError::FunctionCall {
                    name: "wildcard".to_string()
                }),
            }
        );
        assert_eq!(
            split("$(wildcard *.c) $(X)", GNUMake),
            vec![('E', "$(wildcard *.c)"), ('L', " "), ('R', "$(X)")]
        );
        // Only GNU make has functions.
        assert_eq!(
            split("$(wildcard *.c)", POSIXMake),
            vec![('R', "$(wildcard *.c)")]
        );
    }

    #[test]
    fn test_split_references_malformed() {
        assert_eq!(split("a $(B c", GNUMake), vec![('L', "a "), ('E', "$(B c")]);
        assert_eq!(split("a $", GNUMake), vec![('L', "a "), ('E', "$")]);
        // The nested reference is unclosed, but the outer one is closed.
        assert_eq!(
            split("$(X:a=${A) b", GNUMake),
            vec![('E', "$(X:a=${A)"), ('L', " b")]
        );
    }

    #[test]
    fn test_split_references_bsd() {
        assert_eq!(
            split("cc ${SRCS:M*.c:S/$/x/} -o $@ $$x", BSDMake),
            vec![
                ('L', "cc "),
                ('R', "${SRCS:M*.c:S/$/x/}"),
                ('L', " -o "),
                ('R', "$@"),
                ('L', " "),
                ('$', "$$"),
                ('L', "x"),
            ]
        );
        assert_eq!(
            split("${A:S/\\#/x/} \\#", BSDMake),
            vec![('R', "${A:S/\\#/x/}"), ('L', " \\#")]
        );
        assert_eq!(split("${A:S} ${B}", BSDMake), vec![('E', "${A:S} ${B}")]);
    }

    #[test]
    fn test_split_references_bsd_sysv_closing_brace_after() {
        // bmake expands `${S:a=b{}}` with S=a to `b{}`.
        let parts = split_references("${S:a=b{}}", BSDMake);
        assert_eq!(
            parts,
            vec![
                TextPart::Reference {
                    range: 0..9,
                    parsed: Ok(reference("S", vec![sysv("a", "b{")])),
                },
                TextPart::Literal(9..10),
            ]
        );
        assert_eq!(
            ParsedReference::parse_prefix("${S:a=b{}}", BSDMake),
            Ok((reference("S", vec![sysv("a", "b{")]), 9))
        );
        assert!(ParsedReference::parse("${S:a=b{}", BSDMake).is_err());
    }

    #[test]
    fn test_split_references_nmake() {
        assert_eq!(
            split("$(CC) $@ $(OBJS:.obj=.o)", NMake),
            vec![
                ('R', "$(CC)"),
                ('L', " "),
                ('R', "$@"),
                ('L', " "),
                ('R', "$(OBJS:.obj=.o)"),
            ]
        );
    }

    #[test]
    fn test_nmake_substitution_strings_are_literal() {
        // nmake's substitution strings can't invoke macros, so the reference
        // ends at the first `)`, as the parser reads it.
        assert_eq!(
            split("$(SRCS: = $(DIR)\\) $(OBJS:.c=$O)", NMake),
            vec![
                ('R', "$(SRCS: = $(DIR)"),
                ('L', "\\) "),
                ('R', "$(OBJS:.c=$O)"),
            ]
        );
        assert_eq!(
            ParsedReference::parse_prefix("$(SRCS: = $(DIR)\\)", NMake),
            Ok((reference("SRCS", vec![sysv(" ", " $(DIR")]), 16))
        );
        assert_eq!(
            ParsedReference::parse("$(OBJS:.c=$O)", NMake),
            Ok(reference("OBJS", vec![sysv(".c", "$O")]))
        );
        // Other references and GNU make substitutions still nest.
        assert_eq!(
            ParsedReference::parse("$($(A):x=y)", NMake),
            Ok(reference("$(A)", vec![sysv("x", "y")]))
        );
        assert_eq!(
            ParsedReference::parse("$(SRCS: = $(DIR)\\)", GNUMake),
            Ok(reference(
                "SRCS",
                vec![Modifier::SysVSubstitute {
                    from: lit(" "),
                    to: ModifierArg::new([text(" "), expr("$(DIR)"), text("\\")]),
                }]
            ))
        );
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
            Err(ReferenceError::Syntax {
                offset, message, ..
            }) => (offset, message),
            other => panic!("expected syntax error, got {:?}", other),
        }
    }

    #[test]
    fn test_bsd_expr_extent() {
        assert_eq!(bsd_expr_extent("${X:S/$/x/} y"), Some((11, vec![])));
        assert_eq!(bsd_expr_extent("${X:S,},x,}}"), Some((11, vec![])));
        assert_eq!(
            bsd_expr_extent("${A.$B:S/${C}/$$/:M$D*:@v@${v}@}"),
            Some((32, vec![4..6, 9..13, 14..16, 19..21, 26..30]))
        );
        assert_eq!(bsd_expr_extent("$X:"), Some((2, vec![])));
        // The expression that make parses after `$$` is part of it.
        assert_eq!(
            bsd_expr_extent("${X:a=$${Y:S/${Z}/a/}$W} b"),
            Some((24, vec![6..8, 21..23]))
        );
        assert_eq!(bsd_expr_extent("${X:S/a/b"), None);
        assert_eq!(bsd_expr_extent("$$"), None);
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
        assert_eq!(one("${SRCS:M*.c}"), Modifier::Match(lit("*.c")));
        assert_eq!(one("${SRCS:N*.c}"), Modifier::NoMatch(lit("*.c")));
        assert_eq!(
            bsd("${CPPFLAGS:M-[ID]*}"),
            reference("CPPFLAGS", vec![Modifier::Match(lit("-[ID]*"))])
        );
        // Braces are balanced, so a nested reference may contain colons.
        assert_eq!(
            mods("${X:M${PAT:Q}:Q}"),
            vec![
                Modifier::Match(ModifierArg::new([expr("${PAT:Q}")])),
                Modifier::Quote
            ]
        );
        assert_eq!(one("${X:M{a,b}*}"), Modifier::Match(lit("{a,b}*")));
        // An escaped delimiter loses its backslash, an escaped opening
        // brace does not.
        assert_eq!(one("${X:Ma\\:b}"), Modifier::Match(lit("a:b")));
        assert_eq!(one("${X:Ma\\}b}"), Modifier::Match(lit("a}b")));
        assert_eq!(one("${X:Ma\\{b}"), Modifier::Match(lit("a\\{b")));
        assert_eq!(one("${X:M\\*}"), Modifier::Match(lit("\\*")));
        assert_eq!(one("${X:M}"), Modifier::Match(lit("")));
        // `=` does not make this a SysV substitution.
        assert_eq!(one("${X:Ma=b}"), Modifier::Match(lit("a=b")));
    }

    #[test]
    fn test_match_expressions() {
        assert_eq!(
            one("${X:Ma$Y${Z}b$$c$(W)}"),
            Modifier::Match(ModifierArg::new([
                text("a"),
                expr("$Y"),
                expr("${Z}"),
                text("b"),
                ModifierArgPart::EscapedDollar,
                text("c"),
                expr("$(W)"),
            ]))
        );
        assert_eq!(
            one("${X:M$$$$*}"),
            Modifier::Match(ModifierArg::new([
                ModifierArgPart::EscapedDollar,
                ModifierArgPart::EscapedDollar,
                text("*"),
            ]))
        );
        assert_eq!(
            one("${X:N*.${EXT:tl}}"),
            Modifier::NoMatch(ModifierArg::new([text("*."), expr("${EXT:tl}")]))
        );
        // Make expands a `$` at the end of the pattern to nothing.
        assert_eq!(
            one("${X:Mb$}"),
            Modifier::Match(ModifierArg::new([text("b"), expr("$")]))
        );
        // Make reports an invalid expression only when expanding it.
        assert_eq!(
            one("${X:Ma${Y:S}}"),
            Modifier::Match(ModifierArg::new([text("a"), expr("${Y:S}")]))
        );
        // The expressions are found after unescaping.
        assert_eq!(
            one("${X:M\\:${:U\\}x}}"),
            Modifier::Match(ModifierArg::new([text(":"), expr("${:U}"), text("x}")]))
        );
    }

    #[test]
    fn test_match_escapes_nested_deeply() {
        // Each level unescapes its pattern, which must not parse the levels
        // below it again for every level above it.
        let depth = MAX_DEPTH - 1;
        let nested = format!("{}$X{}", "${X:M\\{".repeat(depth), "}".repeat(depth));
        let modifiers = bsd(&nested).modifiers;
        assert_eq!(
            modifiers,
            vec![Modifier::Match(ModifierArg::new([
                text("\\{"),
                expr(&nested[7..nested.len() - 1]),
            ]))]
        );
    }

    #[test]
    fn test_match_escapes_and_expressions() {
        // Escapes are only removed if one comes before the first `$`, and
        // then also from the nested expressions.
        assert_eq!(
            one("${W:M${:U\\:}}"),
            Modifier::Match(ModifierArg::new([expr("${:U\\:}")]))
        );
        assert_eq!(
            one("${X:M${:U}\\:}"),
            Modifier::Match(ModifierArg::new([expr("${:U}"), text("\\:")]))
        );
        assert_eq!(
            one("${X:M\\:${:U}}"),
            Modifier::Match(ModifierArg::new([text(":"), expr("${:U}")]))
        );
        assert_eq!(
            one("${X:M\\:${:U\\:}}"),
            Modifier::Match(ModifierArg::new([text(":"), expr("${:U:}")]))
        );
        assert_eq!(
            one("${X:M${:U\\:}\\:}"),
            Modifier::Match(ModifierArg::new([expr("${:U\\:}"), text("\\:")]))
        );
        assert_eq!(
            one("${X:N$$\\:}"),
            Modifier::NoMatch(ModifierArg::new([
                ModifierArgPart::EscapedDollar,
                text("\\:")
            ]))
        );
        assert_eq!(
            one("${X:N\\:$$}"),
            Modifier::NoMatch(ModifierArg::new([
                text(":"),
                ModifierArgPart::EscapedDollar
            ]))
        );
        // An escaped opening brace keeps its backslash but still enables
        // unescaping.
        assert_eq!(
            one("${X:M\\{${:U\\}}}"),
            Modifier::Match(ModifierArg::new([text("\\{"), expr("${:U}"), text("}")]))
        );
        assert_eq!(
            mods("${X:M${:U\\:}:Q}"),
            vec![
                Modifier::Match(ModifierArg::new([expr("${:U\\:}")])),
                Modifier::Quote
            ]
        );
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
        let matched = || ModifierArgPart::Matched;
        assert_eq!(
            one("${X:S/^a/&&\\&/}"),
            Modifier::Substitute {
                from: lit("a"),
                to: ModifierArg::new([matched(), matched(), text("&")]),
                anchor_start: true,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:S/${A}/[&]/}"),
            Modifier::Substitute {
                from: ModifierArg::new([expr("${A}")]),
                to: ModifierArg::new([text("["), matched(), text("]")]),
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
    }

    #[test]
    fn test_lone_dollar_in_args() {
        let dollar = || ModifierArgPart::EscapedDollar;
        assert_eq!(
            one("${:Ua$}"),
            Modifier::Default(ModifierArg::new([text("a"), expr("$")]))
        );
        assert_eq!(
            mods("${:Ua$:Q}"),
            vec![
                Modifier::Default(ModifierArg::new([text("a"), expr("$")])),
                Modifier::Quote
            ]
        );
        assert_eq!(
            one("${W:Da$}"),
            Modifier::Defined(ModifierArg::new([text("a"), expr("$")]))
        );
        assert_eq!(
            one("${:Ua$$$}"),
            Modifier::Default(ModifierArg::new([text("a"), dollar(), expr("$")]))
        );
        assert_eq!(
            one("${W:Da$$$}"),
            Modifier::Defined(ModifierArg::new([text("a"), dollar(), expr("$")]))
        );
        assert_eq!(
            one("$(:Ua$})"),
            Modifier::Default(ModifierArg::new([text("a"), expr("$"), text("}")]))
        );
        assert_eq!(
            mods("${:U%s:gmtime=1$:Q}"),
            vec![
                Modifier::Default(lit("%s")),
                Modifier::GmTime(Some(ModifierArg::new([text("1"), expr("$")]))),
                Modifier::Quote
            ]
        );
        // Before the closing brace, the `$` is literal.
        assert_eq!(one("${X:gmtime=1$}"), Modifier::GmTime(Some(lit("1$"))));
        assert_eq!(
            one("${X:S/a$}/b/}"),
            Modifier::Substitute {
                from: ModifierArg::new([text("a"), expr("$"), text("}")]),
                to: lit("b"),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        assert_eq!(bsd_expr_extent("${:Ua$} b"), Some((7, vec![])));
    }

    #[test]
    fn test_escaped_dollar_in_args() {
        let dollar = || ModifierArgPart::EscapedDollar;
        let matched = || ModifierArgPart::Matched;
        // `&` is not replaced with the parts of the text to match, so the
        // `$$` that anchors it is not followed by other text.
        assert_eq!(
            one("${X:S/a$$/[&]/}"),
            Modifier::Substitute {
                from: ModifierArg::new([text("a"), dollar()]),
                to: ModifierArg::new([text("["), matched(), text("]")]),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:S/a$$/&Q/}"),
            Modifier::Substitute {
                from: ModifierArg::new([text("a"), dollar()]),
                to: ModifierArg::new([matched(), text("Q")]),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        // In `:C`, make replaces `&` only after expanding the replacement.
        assert_eq!(
            one("${X:C/a/&\\&/}"),
            Modifier::RegexSubstitute {
                regex: lit("a"),
                replacement: lit("&\\&"),
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:S/a/$$x/}"),
            Modifier::Substitute {
                from: lit("a"),
                to: ModifierArg::new([dollar(), text("x")]),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        // Unlike a single `$`, `$$` before the delimiter does not anchor.
        assert_eq!(
            one("${X:S/a$$/b$$/}"),
            Modifier::Substitute {
                from: ModifierArg::new([text("a"), dollar()]),
                to: ModifierArg::new([text("b"), dollar()]),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:S/a$$$/&/}"),
            Modifier::Substitute {
                from: ModifierArg::new([text("a"), dollar()]),
                to: ModifierArg::new([ModifierArgPart::Matched]),
                anchor_start: false,
                anchor_end: true,
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:C/a$$/$${x}/}"),
            Modifier::RegexSubstitute {
                regex: ModifierArg::new([text("a"), dollar()]),
                replacement: ModifierArg::new([dollar(), text("{x}")]),
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:a$$=$${x}}"),
            Modifier::SysVSubstitute {
                from: ModifierArg::new([text("a"), dollar()]),
                to: ModifierArg::new([dollar(), text("{x}")]),
            }
        );
        assert_eq!(
            one("${X:U$$x}"),
            Modifier::Default(ModifierArg::new([dollar(), text("x")]))
        );
        assert_eq!(
            one("${X:Dz$$}"),
            Modifier::Defined(ModifierArg::new([text("z"), dollar()]))
        );
        assert_eq!(
            one("${X:?$$x:$$}"),
            Modifier::IfElse {
                then_branch: ModifierArg::new([dollar(), text("x")]),
                else_branch: ModifierArg::new([dollar()]),
            }
        );
        assert_eq!(
            one("${X:!echo $$$$!}"),
            Modifier::ShellCommand(ModifierArg::new([text("echo "), dollar(), dollar()]))
        );
        assert_eq!(
            one("${X::=$$x}"),
            Modifier::Assign {
                op: AssignOp::Set,
                value: ModifierArg::new([dollar(), text("x")]),
            }
        );
        assert_eq!(
            one("${X:[$$x]}"),
            Modifier::Words(WordSelector::Unexpanded(ModifierArg::new([
                dollar(),
                text("x")
            ])))
        );
        assert_eq!(
            one("${X:gmtime=1$$}"),
            Modifier::GmTime(Some(ModifierArg::new([text("1"), dollar()])))
        );
        // make parses the second `$` as the start of an expression, which
        // decides where the argument ends.
        assert_eq!(
            one("${X:a=$${x}}"),
            Modifier::SysVSubstitute {
                from: lit("a"),
                to: ModifierArg::new([dollar(), text("{x}")]),
            }
        );
        assert_eq!(
            one("${X:S/a/$${x:S,b,/,}\\//}"),
            Modifier::Substitute {
                from: lit("a"),
                to: ModifierArg::new([dollar(), text("{x:S,b,/,}/")]),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        assert_eq!(
            mods("${X:Ua$$\\:Q}"),
            vec![
                Modifier::Default(ModifierArg::new([text("a"), dollar(), text("\\")])),
                Modifier::Quote
            ]
        );
        assert_eq!(
            syntax("${X:S/a/$$\\//}"),
            (
                12,
                "missing delimiter ':' after modifier ':S/a/$$\\/'".to_string()
            )
        );
        assert_eq!(
            one("${X:S(a($$(}"),
            Modifier::Substitute {
                from: lit("a"),
                to: ModifierArg::new([dollar()]),
                anchor_start: false,
                anchor_end: false,
                flags: Default::default(),
            }
        );
        assert_eq!(
            one("${X:?$${x:S,b,:,}:n}"),
            Modifier::IfElse {
                then_branch: ModifierArg::new([dollar(), text("{x:S,b,:,}")]),
                else_branch: lit("n"),
            }
        );
        // An escaped dollar is not literal text.
        assert_eq!(lit("$").as_literal_str(), Some("$"));
        assert_eq!(ModifierArg::new([dollar()]).as_literal_str(), None);
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
            reference("SRCS", vec![Modifier::Match(lit("*.c")), sysv(".c", ".o")])
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
                    Modifier::Match(lit("no")),
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
                Modifier::GmTime(Some(lit("1"))),
                Modifier::LocalTime(None),
                Modifier::LocalTime(Some(lit("2"))),
            ]
        );
        assert_eq!(
            mods("${X:gmtime=${T}:localtime=1${T}2}"),
            vec![
                Modifier::GmTime(Some(ModifierArg::new([expr("${T}")]))),
                Modifier::LocalTime(Some(ModifierArg::new([text("1"), expr("${T}"), text("2")]))),
            ]
        );
        // make only checks the time value when evaluating the expression.
        assert_eq!(
            mods("${X:gmtime=x:gmtime=}"),
            vec![
                Modifier::GmTime(Some(lit("x"))),
                Modifier::GmTime(Some(lit("")))
            ]
        );
        assert_eq!(
            mods(r"${X:gmtime=1\:2\}\$$}"),
            vec![Modifier::GmTime(Some(lit("1:2}$$")))]
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
            syntax("${X:mtime=${T}}"),
            (
                10,
                "invalid argument '${T}}' for modifier ':mtime'".to_string()
            )
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
    fn test_unseparated_indirect() {
        // From NetBSD's unit-tests/varmod-indirect.mk.
        assert_eq!(
            mods("${value:L:${:Dempty}S,value,replaced,}"),
            vec![
                Modifier::Literal,
                Modifier::UnseparatedIndirect("${:Dempty}".to_string()),
                subst("value", "replaced", Default::default()),
            ]
        );
        assert_eq!(
            mods("${X:${A}${B}}"),
            vec![
                Modifier::UnseparatedIndirect("${A}".to_string()),
                Modifier::Indirect("${B}".to_string()),
            ]
        );
        // From NetBSD's share/mk/bsd.man.mk.
        assert_eq!(
            mods("${MLINKS:${_FLATTEN}M${_dst:${_FLATTEN}Q}:[\\#]}"),
            vec![
                Modifier::UnseparatedIndirect("${_FLATTEN}".to_string()),
                Modifier::Match(ModifierArg::new([expr("${_dst:${_FLATTEN}Q}")])),
                Modifier::Words(WordSelector::Count),
            ]
        );
        assert_eq!(
            ParsedReference::parse("${X:${A}Z}", BSDMake),
            Err(ReferenceError::UnknownModifier {
                offset: 8,
                modifier: "Z".to_string()
            })
        );
        // The value of an indirect modifier is parsed as modifiers on its
        // own, which may end in a colon.
        assert_eq!(
            ParsedReference::parse_body(":tl:", BSDMake),
            Ok(reference("", vec![Modifier::ToLower]))
        );
    }

    #[test]
    fn test_chain() {
        assert_eq!(
            bsd("${SRCS:M*.c:S/.c/.o/g:Q}"),
            reference(
                "SRCS",
                vec![
                    Modifier::Match(lit("*.c")),
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
    }

    #[test]
    fn test_syntax_error_kinds() {
        use ReferenceSyntaxErrorKind::*;
        let kind = |text: &str, variant| {
            ParsedReference::parse(text, variant)
                .unwrap_err()
                .syntax_kind()
        };
        let cases = [
            ("${X}y", BSDMake, TrailingText),
            ("X", BSDMake, ExpectedDollar),
            ("$$", BSDMake, EscapedDollar),
            ("$", BSDMake, MissingVariableName),
            ("${X", BSDMake, UnclosedExpression),
            ("$(X", GNUMake, UnclosedExpression),
            ("$(X:a=${A)", GNUMake, UnclosedExpression),
            ("$(X:Lx)", BSDMake, MissingModifierSeparator),
            ("${X:S", BSDMake, MissingModifierDelimiter),
            ("${X:[]}", BSDMake, BadModifier),
            ("${X:@$v@x@}", BSDMake, DollarInLoopVariable),
            (r"${X:ts\400}", BSDMake, InvalidCharacterNumber),
            ("${X:range=x}", BSDMake, InvalidRangeNumber),
            ("${X:mtime=x}", BSDMake, InvalidMtimeArgument),
            ("${X:S/a/b", BSDMake, UnfinishedModifier),
        ];
        for (text, variant, expected) in cases {
            assert_eq!(kind(text, variant), Some(expected), "{}", text);
        }
        assert_eq!(kind("${X:Z}", BSDMake), None);
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
    fn test_nested_extents_parse_each_expression_once() {
        // Finding the expressions nested in each expression parsed the
        // inner ones again for each level, taking time cubic in the depth.
        let depth = 100;
        for (open, close) in [("${X:M", "}"), ("${X:", "=b}"), ("${X:U", "}")] {
            let nest = (0..depth).fold("a".to_string(), |inner, _| format!("{open}{inner}{close}"));
            PARSED_EXPRS.with(|n| n.set(0));
            let text = format!("Y = {nest}\n");
            let parsed = crate::Makefile::parse_with_variant(&text, BSDMake);
            assert!(parsed.is_ok());
            assert_eq!(parsed.tree().variable_references().count(), depth);
            assert_eq!(split_references(&nest, BSDMake).len(), 1);
            let count = PARSED_EXPRS.with(|n| n.get());
            assert!(count <= 8 * depth, "parsed {count} expressions for {open}");
        }
    }

    #[test]
    fn test_parse_prefix_linear() {
        // An evaluator parses each reference in a value with the rest of the
        // value after it, so the work must not depend on the length of the
        // rest.
        let text = "${X:S/a/b/g} \\# ".repeat(20000);
        UNESCAPED_BYTES.with(|n| n.set(0));
        let mut pos = 0;
        let mut count = 0;
        while let Some(offset) = text[pos..].find('$') {
            pos += offset;
            let (parsed, len) = ParsedReference::parse_prefix(&text[pos..], BSDMake).unwrap();
            assert_eq!(parsed, reference("X", vec![subst("a", "b", global())]));
            pos += len;
            count += 1;
        }
        assert_eq!(count, 20000);
        let scanned = UNESCAPED_BYTES.with(|n| n.get());
        assert!(
            scanned <= 10 * text.len(),
            "unescaped {} bytes for {} bytes of text",
            scanned,
            text.len()
        );
    }

    #[test]
    fn test_parse_prefix_long() {
        // Parse all of the text at once, as parse_prefix did before it
        // parsed growing prefixes.
        fn parse_whole(text: &str) -> Result<(ParsedReference, usize), ReferenceError> {
            let unescaped = UnescapedHash::new(text);
            let mut parser = Parser::new(&unescaped.text);
            let parsed = parser.parse_expr().map_err(|e| unescaped.map_error(e))?;
            Ok((parsed, unescaped.original_offset(parser.pos)))
        }
        let templates = [
            "${X:S/PAD/b/g} rest",
            "${X:MPAD\\#*} \\# rest",
            "${X:foo{}PAD a=b} c}",
            "${X:fooPAD{ a=b} c}",
            "${X:fooPAD} a=b}",
            "${X:_=PAD} rest",
            "${X:_=PAD",
            "${X:ts\\0PAD} rest",
            "${X:gmtime=PAD} rest",
            "${X:mtime=PAD} rest",
            "${X:UPAD:hash} rest",
            "${X:UPAD:hash",
            "${X:UPAD:range=12} rest",
            "${X:UPAD:sh}",
            "${X:@v@PAD${v}@} rest",
            "${X:S/PAD\\\\#/x/}",
            "${X:S/PAD\\#/x/}",
            "${X:UPAD:Z} rest",
            "${X:UPAD",
            "${PAD:Q}${Y}",
        ];
        let pads = ["a", "1", "\\", "\\#", "\\\\", "\u{e9}", "${Y}", "}"];
        for template in templates {
            for pad in pads {
                for n in 0..140 {
                    let text = template.replace("PAD", &pad.repeat(n));
                    assert_eq!(
                        ParsedReference::parse_prefix(&text, BSDMake),
                        parse_whole(&text),
                        "{:?}",
                        text
                    );
                }
            }
        }
    }

    #[test]
    fn test_escaped_hash() {
        // make replaces `\#` with `#` before parsing a line.
        assert_eq!(one("${X:[\\#]}"), Modifier::Words(WordSelector::Count));
        assert_eq!(one("${X:M\\#*}"), Modifier::Match(lit("#*")));
        assert_eq!(one("${X:S/\\#/x/}"), subst("#", "x", Default::default()));
        // An escaped backslash does not escape the `#`.
        assert_eq!(one("${X:M\\\\#}"), Modifier::Match(lit("\\\\#")));
        assert_eq!(
            ParsedReference::parse_prefix("${X:[\\#]} == 1", BSDMake),
            Ok((
                reference("X", vec![Modifier::Words(WordSelector::Count)]),
                9
            ))
        );
        assert_eq!(
            ParsedReference::parse("${X:M\\#:Z}", BSDMake),
            Err(ReferenceError::UnknownModifier {
                offset: 8,
                modifier: "Z".to_string()
            })
        );
        assert_eq!(
            ParsedReference::parse_body("X:M\\#*", BSDMake),
            Ok(reference("X", vec![Modifier::Match(lit("#*"))]))
        );
        assert_eq!(
            bsd_expr_extent("${A:S/\\#/${B}/:M$C} ${D}"),
            Some((19, vec![9..13, 16..18]))
        );
        assert_eq!(
            ParsedReference::parse("$(X:\\#=x)", GNUMake),
            Ok(reference("X", vec![sysv("\\#", "x")]))
        );
    }

    #[test]
    fn test_parse_body() {
        assert_eq!(
            ParsedReference::parse_body("SRCS:M*.c:.c=.o", BSDMake),
            Ok(reference(
                "SRCS",
                vec![Modifier::Match(lit("*.c")), sysv(".c", ".o")]
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
                kind: ReferenceSyntaxErrorKind::UnclosedExpression,
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
    fn test_nmake_all_dependents() {
        // `$**` is nmake's list of all dependents of the target.
        assert_eq!(
            ParsedReference::parse("$**", NMake),
            Ok(reference("**", vec![]))
        );
        assert_eq!(
            ParsedReference::parse_prefix("$***", NMake),
            Ok((reference("**", vec![]), 3))
        );
        assert_eq!(
            ParsedReference::parse("$(**F)", NMake),
            Ok(reference("**F", vec![]))
        );
        assert_eq!(
            split("$** $(**D) $*.c $@", NMake),
            vec![
                ('R', "$**"),
                ('L', " "),
                ('R', "$(**D)"),
                ('L', " "),
                ('R', "$*"),
                ('L', ".c "),
                ('R', "$@"),
            ]
        );
        // Other makes take `$**` as `$*` followed by `*`.
        for variant in [GNUMake, POSIXMake] {
            assert_eq!(
                ParsedReference::parse_prefix("$**", variant),
                Ok((reference("*", vec![]), 2))
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
                    Modifier::Match(lit("*.[cly]")),
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
                    Modifier::Match(lit("no")),
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
        assert_eq!(arg.as_literal_str(), None);
        assert_eq!(lit("ab").as_literal_str(), Some("ab"));
        assert_eq!(lit("").as_literal_str(), Some(""));
        #[allow(deprecated)]
        {
            assert_eq!(arg.as_literal(), None);
            assert_eq!(lit("ab").as_literal(), Some("ab".to_string()));
            assert_eq!(lit("").as_literal(), Some("".to_string()));
        }
        assert!(lit("").is_empty());
        assert!(!arg.is_empty());
        let dollar = ModifierArg::new([text("a"), ModifierArgPart::EscapedDollar, text("b")]);
        assert_eq!(
            dollar.parts(),
            &[text("a"), ModifierArgPart::EscapedDollar, text("b")]
        );
        assert_eq!(dollar.as_literal_str(), None);
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

    #[test]
    fn test_deeply_nested_expression() {
        let nested = |depth: usize| format!("{}X{}", "${".repeat(depth), "}".repeat(depth));
        assert!(ParsedReference::parse(&nested(MAX_DEPTH), MakefileVariant::BSDMake).is_ok());
        for depth in [MAX_DEPTH + 1, 2000] {
            assert_eq!(
                ParsedReference::parse(&nested(depth), MakefileVariant::BSDMake),
                Err(syntax_error(
                    2 * MAX_DEPTH,
                    ReferenceSyntaxErrorKind::TooDeeplyNested,
                    "expressions nested too deeply"
                ))
            );
        }
    }

    #[test]
    fn test_deeply_nested_modifier_arguments() {
        for (open, close) in [
            ("${X:S/a/", "/}"),
            ("${X:C/a/", "/}"),
            ("${X:U", "}"),
            ("${X:D", "}"),
            ("${X:a=", "}"),
            ("${X:?", ":b}"),
            ("${X:?a:", "}"),
            ("${X:!", "!}"),
            ("${X::=", "}"),
            ("${X:[", "]}"),
            ("${X:gmtime=", "}"),
            ("${X", "}"),
        ] {
            let nested = |depth: usize| format!("{}$X{}", open.repeat(depth), close.repeat(depth));
            assert!(
                ParsedReference::parse(&nested(MAX_DEPTH), MakefileVariant::BSDMake).is_ok(),
                "{open}"
            );
            assert_eq!(
                ParsedReference::parse(&nested(2000), MakefileVariant::BSDMake)
                    .unwrap_err()
                    .syntax_kind(),
                Some(ReferenceSyntaxErrorKind::TooDeeplyNested),
                "{open}"
            );
        }
    }

    #[test]
    fn test_deeply_nested() {
        // Parsing these took time exponential in the nesting depth.
        let nest = |open: &str, close: &str| {
            (0..40).fold("a".to_string(), |inner, _| format!("{open}{inner}{close}"))
        };
        let sysv = nest("${X:", "=b}");
        let parsed = bsd(&sysv);
        assert_eq!(parsed.name, "X");
        assert_eq!(
            parsed.modifiers,
            vec![Modifier::SysVSubstitute {
                from: ModifierArg::new([expr(&sysv[4..sysv.len() - 3])]),
                to: lit("b"),
            }]
        );
        let matches = nest("${X:M", "}");
        assert_eq!(
            bsd(&matches).modifiers,
            vec![Modifier::Match(ModifierArg::new([expr(
                &matches[5..matches.len() - 1]
            )]))]
        );
        let unclosed = &matches[..matches.len() - 1];
        assert!(ParsedReference::parse(unclosed, BSDMake).is_err());
        assert!(crate::Makefile::parse_with_variant(&format!("Y = {sysv}\n"), BSDMake).is_ok());
        assert!(crate::Makefile::parse_with_variant(&format!("Y = {matches}\n"), BSDMake).is_ok());
    }
}
