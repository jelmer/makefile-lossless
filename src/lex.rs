use crate::lossless::ASSIGNMENT_OPERATORS;
use crate::{MakefileVariant, SyntaxKind};
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum LineType {
    Recipe,
    Other,
}

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    line_type: Option<LineType>,
    continuation: bool,
    /// Parity of the current backslash run: true once an odd number have been
    /// emitted, so the next backslash is escaped (`\\`) and a following newline
    /// is literal, not a continuation. Mirrors the parser's
    /// `pending_backslash_escape`.
    pending_backslash_escape: bool,
    /// Whether BSD make syntax is accepted.
    bsd: bool,
    /// Whether GNU make syntax is accepted.
    gnu: bool,
    /// Whether `#` inside a variable reference or function call is literal,
    /// as in GNU make, rather than the start of a comment.
    hash_in_references: bool,
    /// Whether nmake syntax is accepted, where a line starting with spaces
    /// is a command line too.
    nmake: bool,
    /// Whether the previous token was a `[`. BSD make does not treat `#` as
    /// a comment there, so that the `:[#]` modifier works.
    after_lbracket: bool,
    /// Whether the previous line was a recipe line ending in a backslash, so
    /// that this line continues the recipe.
    recipe_continuation: bool,
    /// Whether the current line continues a recipe line, so that a `#` at
    /// its start is part of the command rather than a comment.
    continues_recipe: bool,
    /// Number of parentheses and braces open inside `$(...)` and `${...}`
    /// references on the current logical line.
    reference_depth: usize,
    /// Number of `$` tokens directly before the current one.
    dollars: usize,
    /// The character that starts a recipe line, set with GNU make's
    /// `.RECIPEPREFIX`.
    recipe_prefix: char,
    /// Text of the current logical line, unless it is a recipe line or
    /// its first word shows that it can't start a `define` block or assign
    /// to `.RECIPEPREFIX`.
    line: Option<String>,
    /// Whether the first word of the current logical line has been seen.
    line_checked: bool,
    /// Text of the current logical line, including recipe lines, if it is
    /// in a `define` block.
    raw_line: String,
    /// The GNU make `define` whose body is being read, if any.
    define: Option<Define>,
    /// For nmake, whether the first operator on the current logical line
    /// is `=`, making it a macro definition. `None` before any operator.
    nmake_definition: Option<bool>,
    /// For nmake, whether the current logical line has an unclosed `"`, in
    /// which carets are literal.
    // TODO: Check whether nmake starts a comment at a `#` in a quoted
    // string; its documentation doesn't say.
    nmake_quoted: bool,
    /// For nmake, the number of inline files still to read, from the `<<`
    /// in the last command line.
    nmake_inline_files: usize,
    /// Whether no token has been read yet on the current logical line.
    line_start: bool,
    /// Whether the current logical line so far is a `.` at its start,
    /// optionally followed by whitespace, so that a directive name follows.
    after_directive_dot: bool,
    /// Whether `#` can start a comment.
    comments: bool,
}

/// A GNU make `define` block whose body is being read.
struct Define {
    /// The number of `define` lines not yet closed by an `endef`.
    depth: usize,
    /// The assignment operator, if this defines `.RECIPEPREFIX`.
    recipe_prefix_op: Option<&'static str>,
    /// The text of the body so far.
    body: String,
}

/// Whether `text` ends in an odd number of backslashes, so that the last
/// one is not escaped by the one before it.
pub(crate) fn ends_with_unescaped_backslash(text: &str) -> bool {
    text.chars().rev().take_while(|&c| c == '\\').count() % 2 == 1
}

/// The characters that nmake takes literally after a `^`.
pub(crate) const NMAKE_ESCAPABLE: &[char] = &[
    ':', ';', '#', '(', ')', '$', '^', '\\', '{', '}', '!', '@', '-',
];

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str, variant: Option<MakefileVariant>) -> Self {
        Lexer {
            input: input.chars().peekable(),
            continuation: false,
            line_type: None,
            pending_backslash_escape: false,
            bsd: matches!(variant, None | Some(MakefileVariant::BSDMake)),
            gnu: matches!(variant, None | Some(MakefileVariant::GNUMake)),
            hash_in_references: !matches!(
                variant,
                Some(MakefileVariant::BSDMake | MakefileVariant::NMake)
            ),
            nmake: variant == Some(MakefileVariant::NMake),
            after_lbracket: false,
            recipe_continuation: false,
            continues_recipe: false,
            reference_depth: 0,
            dollars: 0,
            recipe_prefix: '\t',
            line: Some(String::new()),
            line_checked: false,
            raw_line: String::new(),
            define: None,
            nmake_definition: None,
            nmake_quoted: false,
            nmake_inline_files: 0,
            line_start: true,
            after_directive_dot: false,
            comments: true,
        }
    }

    /// Track `define` blocks and `.RECIPEPREFIX` assignments at the end of
    /// a logical line. `line` is the text of the line if it is not a recipe
    /// line and `raw` its text in any case.
    fn end_logical_line(&mut self, line: Option<String>, raw: String) {
        let Some(define) = &mut self.define else {
            if let Some(line) = line {
                if let Some(recipe_prefix_op) = Self::define_header(&line) {
                    self.define = Some(Define {
                        depth: 1,
                        recipe_prefix_op,
                        body: String::new(),
                    });
                } else {
                    self.update_recipe_prefix(&line);
                }
            }
            return;
        };
        // Like make, only look for `define` and `endef` on lines that do
        // not start with the recipe prefix.
        if !raw.starts_with(self.recipe_prefix) {
            let raw = raw.replace("\\\r\n", " ").replace("\\\n", " ");
            let rest = raw.trim_start_matches(Self::is_whitespace);
            let keyword = |keyword: &str| {
                rest.strip_prefix(keyword)
                    .is_some_and(|r| r.is_empty() || r.starts_with([' ', '\t', '\r', '\n']))
            };
            if keyword("endef") {
                define.depth -= 1;
            } else if keyword("define") {
                define.depth += 1;
            }
        }
        if define.depth > 0 {
            define.body.push_str(&raw);
            return;
        }
        let define = self.define.take().unwrap();
        if let Some(op) = define.recipe_prefix_op {
            let body = define.body.replace("\r\n", "\n");
            // The newline before `endef` is not part of the value.
            self.set_recipe_prefix(op, body.strip_suffix('\n').unwrap_or(&body));
        }
    }

    /// If `line` starts a `define` block, return the assignment operator if
    /// it defines `.RECIPEPREFIX`. This follows the parser's check, in which
    /// `define = 1` assigns to a variable named "define".
    fn define_header(line: &str) -> Option<Option<&'static str>> {
        let line = line.replace("\\\r\n", " ").replace("\\\n", " ");
        let mut rest = line.trim_end_matches(['\r', '\n']).trim_start();
        loop {
            if let Some(r) = rest.strip_prefix("define") {
                if r.is_empty() || r.starts_with([' ', '\t', '#']) {
                    rest = r.trim_start();
                    break;
                }
            }
            let modifier = ["override", "export", "unexport", "private"]
                .into_iter()
                .find(|m| {
                    rest.strip_prefix(m)
                        .is_some_and(|r| r.starts_with(Self::is_whitespace))
                })?;
            rest = rest[modifier.len()..].trim_start();
        }
        if ASSIGNMENT_OPERATORS.iter().any(|op| rest.starts_with(op)) {
            return None;
        }
        let Some(rest) = rest.strip_prefix(".RECIPEPREFIX") else {
            return Some(None);
        };
        let rest = rest.trim_start();
        if rest.is_empty() || rest.starts_with('#') {
            return Some(Some("="));
        }
        Some(
            ["=", ":=", "::=", ":::=", "+=", "?="]
                .into_iter()
                .find(|op| rest.starts_with(op)),
        )
    }

    /// Stop collecting the text of the current line if `token` is the
    /// first word on it, and the line can't start a `define` block or assign
    /// to `.RECIPEPREFIX`: it doesn't start with `define`, `.RECIPEPREFIX`
    /// or a modifier such as `override`.
    fn check_line_start(&mut self, token: &(SyntaxKind, String)) {
        if self.line_checked
            || matches!(
                token.0,
                SyntaxKind::WHITESPACE
                    | SyntaxKind::INDENT
                    | SyntaxKind::BACKSLASH
                    | SyntaxKind::NEWLINE
            )
        {
            return;
        }
        self.line_checked = true;
        if !token.1.starts_with(['d', '.', 'o', 'e', 'u', 'p']) {
            self.line = None;
        }
    }

    /// Update the recipe prefix if `line` assigns to `.RECIPEPREFIX`.
    fn update_recipe_prefix(&mut self, line: &str) {
        let line = line.replace("\\\r\n", " ").replace("\\\n", " ");
        let mut rest = line.trim_start();
        // GNU make takes these modifiers in any order, and repeated.
        while let Some(r) = ["override", "export", "unexport", "private"]
            .into_iter()
            .find_map(|m| {
                rest.strip_prefix(m)
                    .filter(|r| r.starts_with(Self::is_whitespace))
            })
        {
            rest = r.trim_start();
        }
        let Some(rest) = rest.strip_prefix(".RECIPEPREFIX") else {
            return;
        };
        let rest = rest.trim_start();
        let Some((op, value)) = ["=", ":=", "::=", ":::=", "+=", "?="]
            .iter()
            .find_map(|op| Some((*op, rest.strip_prefix(op)?)))
        else {
            return;
        };
        let value = value.trim_start();
        let value = if value.starts_with('#') { "" } else { value };
        self.set_recipe_prefix(op, value);
    }

    /// Set the recipe prefix from an assignment of `value` to
    /// `.RECIPEPREFIX` with operator `op`.
    fn set_recipe_prefix(&mut self, op: &str, value: &str) {
        let first = match value.chars().next() {
            // An immediately expanded reference.
            // TODO: Expand variable references.
            Some('$') if op != "=" && !value.starts_with("$$") => return,
            first => first,
        };
        match op {
            // `.RECIPEPREFIX` is always defined.
            "?=" => {}
            "+=" if self.recipe_prefix != '\t' => {}
            _ => self.recipe_prefix = first.unwrap_or('\t'),
        }
    }

    fn is_whitespace(c: char) -> bool {
        c == ' ' || c == '\t'
    }

    /// Whether `c` separates words outside recipes. BSD make takes any
    /// character `isspace()` accepts, including a lone CR.
    fn is_word_separator(&self, c: char) -> bool {
        Self::is_whitespace(c) || (self.bsd && !self.gnu && matches!(c, '\r' | '\x0b' | '\x0c'))
    }

    /// Read word separators up to the end of the line.
    fn read_word_separators(&mut self) -> String {
        let mut result = String::new();
        while let Some(&c) = self.input.peek() {
            if self.at_newline() || !self.is_word_separator(c) {
                break;
            }
            self.input.next();
            result.push(c);
        }
        result
    }

    /// Whether the input is at a line ending. Like GNU make and BSD make,
    /// only take LF and CRLF as line endings; a lone CR is an ordinary
    /// character.
    fn at_newline(&self) -> bool {
        let mut probe = self.input.clone();
        match probe.next() {
            Some('\n') => true,
            Some('\r') => probe.next() == Some('\n'),
            _ => false,
        }
    }

    /// Whether the input is at a CRLF whose CR BSD make takes as escaped
    /// by an unescaped backslash before it, so that the line ends at the LF
    /// and is not continued.
    fn at_escaped_cr(&self, after_backslash: bool) -> bool {
        let mut probe = self.input.clone();
        self.bsd
            && !self.gnu
            && after_backslash
            && probe.next() == Some('\r')
            && probe.next() == Some('\n')
    }

    /// Read the rest of a recipe line as text, noting whether it continues
    /// on the next line.
    fn read_recipe_text(&mut self) -> (SyntaxKind, String) {
        let text = self.read_line();
        self.recipe_continuation = ends_with_unescaped_backslash(&text);
        if self.nmake {
            self.nmake_inline_files += text.matches("<<").count();
        }
        (SyntaxKind::TEXT, text)
    }

    /// Read up to the end of the line.
    fn read_line(&mut self) -> String {
        let mut result = String::new();
        let mut after_backslash = false;
        loop {
            if self.at_newline() && !self.at_escaped_cr(after_backslash) {
                break;
            }
            let Some(c) = self.input.next() else {
                break;
            };
            after_backslash = c == '\\' && !after_backslash;
            result.push(c);
        }
        result
    }

    /// For BSD make, the length of the identifier starting with `c` up to
    /// the end of a conditional directive name, if the name is followed by
    /// something other than a letter. BSD make reads the name up to the
    /// first non-letter, so `.if0` is `.if 0`.
    fn bsd_conditional_name_len(&self, c: char) -> Option<usize> {
        if !self.bsd || self.gnu {
            return None;
        }
        let skip = if self.line_start && c == '.' {
            1
        } else if self.after_directive_dot {
            0
        } else {
            return None;
        };
        let word: String = self
            .input
            .clone()
            .take_while(|&c| Self::is_valid_identifier_char(c))
            .collect();
        let rest = &word[skip..];
        let name_len = rest
            .find(|c: char| !c.is_ascii_alphabetic())
            .unwrap_or(rest.len());
        let conditional = matches!(
            &rest[..name_len],
            "if" | "ifdef"
                | "ifndef"
                | "ifmake"
                | "ifnmake"
                | "elif"
                | "elifdef"
                | "elifndef"
                | "elifmake"
                | "elifnmake"
                | "else"
                | "endif"
        );
        (conditional && name_len < rest.len()).then_some(skip + name_len)
    }

    fn is_valid_identifier_char(c: char) -> bool {
        c.is_ascii_alphabetic()
            || c.is_ascii_digit()
            || c == '_'
            || c == '/'
            || c == '.'
            || c == '-'
            || c == '%'
    }

    /// Read a comment up to the end of the line. Outside recipes, a comment
    /// ending in an unescaped backslash continues on the next line.
    fn read_comment(&mut self) -> String {
        let mut comment = self.read_line();
        while self.line_type == Some(LineType::Other)
            && ends_with_unescaped_backslash(&comment)
            && self.at_newline()
        {
            if let Some(cr) = self.input.next_if_eq(&'\r') {
                comment.push(cr);
            }
            comment.extend(self.input.next());
            comment.push_str(&self.read_line());
        }
        comment
    }

    fn read_while<F>(&mut self, predicate: F) -> String
    where
        F: Fn(char) -> bool,
    {
        let mut result = String::new();
        while let Some(&c) = self.input.peek() {
            if predicate(c) {
                result.push(c);
                self.input.next();
            } else {
                break;
            }
        }
        result
    }

    fn next_token(&mut self) -> Option<(SyntaxKind, String)> {
        // A backslash continues the line only when it is not itself escaped by
        // a preceding backslash. `escaped` is the run parity carried over from
        // the previous token; clear the field here so any non-backslash token
        // resets the run.
        let escaped = self.pending_backslash_escape;
        self.pending_backslash_escape = false;
        let after_lbracket = self.after_lbracket;
        self.after_lbracket = false;
        if let Some(&c) = self.input.peek() {
            let recipe_continuation =
                self.line_type.is_none() && std::mem::take(&mut self.recipe_continuation);
            if self.line_type.is_none() {
                self.continues_recipe = recipe_continuation;
            }
            match (c, self.line_type) {
                (_, None) if self.nmake_inline_files > 0 && !self.at_newline() => {
                    // A line of an nmake inline file, up to a line starting
                    // with `<<`.
                    self.line_type = Some(LineType::Recipe);
                    let text = self.read_line();
                    if text.starts_with("<<") {
                        self.nmake_inline_files -= 1;
                    }
                    return Some((SyntaxKind::TEXT, text));
                }
                // A prefix set to a newline, by a `define` whose value starts
                // with an empty line, allows no recipe lines.
                (c, None)
                    if c == self.recipe_prefix && c != '\t' && c != '\n' && !self.continuation =>
                {
                    self.input.next();
                    self.line_type = Some(LineType::Recipe);
                    return Some((SyntaxKind::INDENT, c.to_string()));
                }
                ('\t', None)
                    if self.recipe_prefix != '\t' && !self.continuation && !recipe_continuation =>
                {
                    // Only the recipe prefix introduces a recipe line.
                    self.line_type = Some(LineType::Other);
                    return Some((SyntaxKind::WHITESPACE, self.read_while(Self::is_whitespace)));
                }
                ('\t', None) if !self.continuation => {
                    self.input.next();
                    self.line_type = Some(LineType::Recipe);
                    return Some((SyntaxKind::INDENT, "\t".to_string()));
                }
                ('\t', None) => {
                    // Continuation line: tab is indent but not a recipe
                    self.input.next();
                    self.line_type = Some(LineType::Other);
                    self.continuation = false;
                    return Some((SyntaxKind::INDENT, "\t".to_string()));
                }
                (' ', None) if recipe_continuation || (self.nmake && !self.continuation) => {
                    // A space-indented continuation of a recipe line, or an
                    // nmake command line, which may start with spaces.
                    self.line_type = Some(LineType::Recipe);
                    return Some((SyntaxKind::INDENT, self.read_while(|ch| ch == ' ')));
                }
                (_, None) if recipe_continuation && !self.at_newline() => {
                    // An unindented continuation of a recipe line, which
                    // make passes on to the shell as is, `#` included.
                    self.line_type = Some(LineType::Recipe);
                    return Some(self.read_recipe_text());
                }
                (' ', None) if !self.continuation => {
                    // Only a tab introduces a recipe line; leading spaces are
                    // allowed before ordinary makefile lines.
                    self.line_type = Some(LineType::Other);
                    return Some((SyntaxKind::WHITESPACE, self.read_while(Self::is_whitespace)));
                }
                (' ', None) => {
                    // Continuation line: spaces are indent but not a recipe
                    let spaces = self.read_while(|ch| ch == ' ');
                    self.line_type = Some(LineType::Other);
                    self.continuation = false;
                    return Some((SyntaxKind::INDENT, spaces));
                }
                (_, None) => {
                    self.line_type = Some(LineType::Other);
                    self.continuation = false;
                }
                (_, _) => {}
            }

            match c {
                _ if self.at_newline() => {
                    self.line_type = None;
                    // Take CRLF as a single line ending.
                    let mut text = String::new();
                    text.extend(self.input.next_if_eq(&'\r'));
                    text.extend(self.input.next());
                    return Some((SyntaxKind::NEWLINE, text));
                }
                '#' if self.line_type == Some(LineType::Other)
                    && (!self.comments
                        || (self.bsd && after_lbracket)
                        || (self.hash_in_references && self.reference_depth > 0)) => {}
                // GNU and BSD make pass a `#` at the start of a continuation
                // line on to the shell with the rest of the command.
                '#' if self.line_type == Some(LineType::Recipe)
                    && self.continues_recipe
                    && !self.nmake => {}
                '#' => {
                    let comment = self.read_comment();
                    // GNU and BSD make continue a recipe line starting with
                    // `#` like any other, although nmake ends a comment at
                    // the end of the line.
                    if self.line_type == Some(LineType::Recipe) && !self.nmake {
                        self.recipe_continuation = ends_with_unescaped_backslash(&comment);
                    }
                    return Some((SyntaxKind::COMMENT, comment));
                }
                _ => {}
            }

            match self.line_type.unwrap() {
                LineType::Recipe => Some(self.read_recipe_text()),
                LineType::Other => match c {
                    c if self.is_word_separator(c) => {
                        Some((SyntaxKind::WHITESPACE, self.read_word_separators()))
                    }
                    c if Self::is_valid_identifier_char(c) => {
                        let text = match self.bsd_conditional_name_len(c) {
                            Some(len) => self.input.by_ref().take(len).collect(),
                            None => self.read_while(Self::is_valid_identifier_char),
                        };
                        Some((SyntaxKind::IDENTIFIER, text))
                    }
                    // Make does not treat quotes specially when reading a
                    // line, so each quote is a token of its own.
                    '"' | '\'' => {
                        self.input.next();
                        if c == '"' && self.nmake {
                            self.nmake_quoted = !self.nmake_quoted;
                        }
                        Some((SyntaxKind::QUOTE, c.to_string()))
                    }
                    ':' => {
                        // Only take as many characters as form a valid
                        // operator (`:`, `::`, `:=`, `::=` or `:::=`); the
                        // rest belongs to whatever follows, e.g. `X:==y`.
                        let mut probe = self.input.clone();
                        let mut colons = 0;
                        while probe.next_if_eq(&':').is_some() {
                            colons += 1;
                        }
                        let len = if colons <= 3 && probe.peek() == Some(&'=') {
                            colons + 1
                        } else {
                            colons.min(2)
                        };
                        let text = self.input.by_ref().take(len).collect();
                        Some((SyntaxKind::OPERATOR, text))
                    }
                    // Only GNU make has grouped targets; other makes take
                    // the `&` in `a b &: c` as a target.
                    '&' if self.gnu => {
                        // `&:` and `&::` separate grouped targets from their
                        // prerequisites; any other `&` is just a character.
                        let mut probe = self.input.clone();
                        probe.next();
                        let mut colons = 0;
                        while probe.next_if_eq(&':').is_some() {
                            colons += 1;
                        }
                        let len = if (1..=2).contains(&colons) && probe.peek() != Some(&'=') {
                            colons + 1
                        } else {
                            1
                        };
                        let text: String = self.input.by_ref().take(len).collect();
                        let kind = if len > 1 {
                            SyntaxKind::OPERATOR
                        } else {
                            SyntaxKind::TEXT
                        };
                        Some((kind, text))
                    }
                    // Only `?=` and `+=` are operators; a lone `?` or `+` is
                    // part of a name such as `c++filt`.
                    '?' | '+' => {
                        let mut text = self.input.next().unwrap().to_string();
                        if let Some(eq) = self.input.next_if_eq(&'=') {
                            text.push(eq);
                            Some((SyntaxKind::OPERATOR, text))
                        } else {
                            Some((SyntaxKind::TEXT, text))
                        }
                    }
                    '=' => {
                        self.input.next();
                        Some((SyntaxKind::OPERATOR, "=".to_string()))
                    }
                    '!' => {
                        // `!=` is the shell assignment operator; a lone `!`
                        // is the BSD make "always rebuild" dependency
                        // operator, or negation in a conditional.
                        self.input.next();
                        if self.input.peek() == Some(&'=') {
                            self.input.next();
                            Some((SyntaxKind::OPERATOR, "!=".to_string()))
                        } else {
                            Some((SyntaxKind::OPERATOR, "!".to_string()))
                        }
                    }
                    '(' => {
                        self.input.next();
                        Some((SyntaxKind::LPAREN, "(".to_string()))
                    }
                    ')' => {
                        self.input.next();
                        Some((SyntaxKind::RPAREN, ")".to_string()))
                    }
                    '{' => {
                        self.input.next();
                        Some((SyntaxKind::LBRACE, "{".to_string()))
                    }
                    '}' => {
                        self.input.next();
                        Some((SyntaxKind::RBRACE, "}".to_string()))
                    }
                    '$' => {
                        self.input.next();
                        Some((SyntaxKind::DOLLAR, "$".to_string()))
                    }
                    ',' => {
                        self.input.next();
                        Some((SyntaxKind::COMMA, ",".to_string()))
                    }
                    '^' if self.nmake => {
                        self.input.next();
                        // A caret in a quoted string is literal, except at the
                        // end of a line.
                        if let Some(escaped) = self
                            .input
                            .next_if(|c| !self.nmake_quoted && NMAKE_ESCAPABLE.contains(c))
                        {
                            return Some((SyntaxKind::TEXT, format!("^{escaped}")));
                        }
                        // In a macro definition, a caret at the end of the
                        // line continues the definition with a newline.
                        if self.nmake_definition == Some(true) && self.at_newline() {
                            self.continuation = true;
                        }
                        Some((SyntaxKind::TEXT, "^".to_string()))
                    }
                    '\\' => {
                        self.input.next();
                        // `\#` is a literal hash rather than the start of a
                        // comment. nmake only has `^#` for that.
                        if !escaped && !self.nmake && self.input.peek() == Some(&'#') {
                            self.input.next();
                            return Some((SyntaxKind::TEXT, "\\#".to_string()));
                        }
                        if self.at_escaped_cr(!escaped) {
                            self.input.next();
                            return Some((SyntaxKind::TEXT, "\\\r".to_string()));
                        }
                        // A backslash-newline is a continuation only if this
                        // backslash is not escaped by a preceding one.
                        if !escaped && self.at_newline() {
                            self.continuation = true;
                        }
                        self.pending_backslash_escape = !escaped;
                        Some((SyntaxKind::BACKSLASH, "\\".to_string()))
                    }
                    // nmake's `$**`, all dependents of the target.
                    '*' if self.nmake && self.dollars % 2 == 1 && {
                        let mut probe = self.input.clone();
                        probe.next();
                        probe.peek() == Some(&'*')
                    } =>
                    {
                        let text = self.input.by_ref().take(2).collect();
                        Some((SyntaxKind::TEXT, text))
                    }
                    // Any other character is plain text to make.
                    _ => {
                        self.input.next();
                        self.after_lbracket = c == '[';
                        Some((SyntaxKind::TEXT, c.to_string()))
                    }
                },
            }
        } else {
            None
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = (crate::SyntaxKind, String);

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.next_token()?;
        let at_line_start = std::mem::replace(&mut self.line_start, false);
        self.after_directive_dot = match token.0 {
            SyntaxKind::IDENTIFIER => at_line_start && token.1 == ".",
            SyntaxKind::WHITESPACE => self.after_directive_dot,
            _ => false,
        };
        if self.gnu {
            if self.line_type == Some(LineType::Recipe) {
                self.line = None;
            } else if self.line.is_some() {
                self.check_line_start(&token);
            }
            if let Some(line) = &mut self.line {
                line.push_str(&token.1);
            }
            if self.define.is_some() {
                self.raw_line.push_str(&token.1);
            }
            if token.0 == SyntaxKind::NEWLINE && !self.continuation {
                let line = self.line.replace(String::new());
                self.line_checked = false;
                let raw = std::mem::take(&mut self.raw_line);
                self.end_logical_line(line, raw);
            }
        }
        match token.0 {
            SyntaxKind::LPAREN | SyntaxKind::LBRACE
                if self.reference_depth > 0 || self.dollars % 2 == 1 =>
            {
                self.reference_depth += 1
            }
            SyntaxKind::RPAREN | SyntaxKind::RBRACE => {
                self.reference_depth = self.reference_depth.saturating_sub(1)
            }
            SyntaxKind::NEWLINE if !self.continuation => {
                self.line_start = true;
                self.reference_depth = 0;
                self.nmake_definition = None;
                self.nmake_quoted = false;
            }
            SyntaxKind::OPERATOR
                if self.nmake_definition.is_none() && self.line_type == Some(LineType::Other) =>
            {
                self.nmake_definition = Some(token.1 == "=")
            }
            _ => {}
        }
        self.dollars = if token.0 == SyntaxKind::DOLLAR {
            self.dollars + 1
        } else {
            0
        };
        Some(token)
    }
}

pub(crate) fn lex(input: &str, variant: Option<MakefileVariant>) -> Vec<(SyntaxKind, String)> {
    Lexer::new(input, variant).collect()
}

/// The character that starts a recipe line after `input`, as set by the
/// `.RECIPEPREFIX` assignments in it that the parser follows.
pub(crate) fn recipe_prefix_after(input: &str) -> char {
    if !input.contains(".RECIPEPREFIX") {
        return '\t';
    }
    let mut lexer = Lexer::new(input, None);
    while lexer.next().is_some() {}
    lexer.recipe_prefix
}

/// Lex `input`, treating its first line as an ordinary makefile line even if
/// it starts with a tab.
pub(crate) fn lex_non_recipe_line(
    input: &str,
    variant: Option<MakefileVariant>,
) -> Vec<(SyntaxKind, String)> {
    let mut lexer = Lexer::new(input, variant);
    lexer.line_type = Some(LineType::Other);
    lexer.collect()
}

/// Lex the first logical line of `input`, including its line ending, as an
/// ordinary makefile line even if it starts with a tab.
pub(crate) fn lex_first_non_recipe_line(
    input: &str,
    variant: Option<MakefileVariant>,
) -> Vec<(SyntaxKind, String)> {
    let mut lexer = Lexer::new(input, variant);
    lexer.line_type = Some(LineType::Other);
    let mut tokens = vec![];
    while let Some(token) = lexer.next() {
        let line_end = token.0 == SyntaxKind::NEWLINE && !lexer.continuation;
        tokens.push(token);
        if line_end {
            break;
        }
    }
    tokens
}

/// Lex text inside a variable reference in a recipe line or `define`
/// body, where `#` does not start a comment. Each line is lexed as an
/// ordinary makefile line.
pub(crate) fn lex_reference_text(
    input: &str,
    variant: Option<MakefileVariant>,
) -> Vec<(SyntaxKind, String)> {
    input
        .split_inclusive('\n')
        .flat_map(|line| {
            let mut lexer = Lexer::new(line, variant);
            lexer.line_type = Some(LineType::Other);
            lexer.comments = false;
            lexer.collect::<Vec<_>>()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::SyntaxKind::*;

    fn lex_default(input: &str) -> Vec<(SyntaxKind, String)> {
        lex(input, None)
    }

    #[test]
    fn test_empty() {
        assert_eq!(lex_default(""), vec![]);
    }

    #[test]
    fn test_simple() {
        assert_eq!(
            lex_default(
                r#"VARIABLE = value

rule: prerequisite
	recipe
"#
            )
            .iter()
            .map(|(kind, text)| (*kind, text.as_str()))
            .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "VARIABLE"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (IDENTIFIER, "value"),
                (NEWLINE, "\n"),
                (NEWLINE, "\n"),
                (IDENTIFIER, "rule"),
                (OPERATOR, ":"),
                (WHITESPACE, " "),
                (IDENTIFIER, "prerequisite"),
                (NEWLINE, "\n"),
                (INDENT, "\t"),
                (TEXT, "recipe"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_crlf() {
        assert_eq!(
            lex_default("X = a \\\r\n\tb\r\nall:\r\n\techo\r\n"),
            vec![
                (IDENTIFIER, "X".to_string()),
                (WHITESPACE, " ".to_string()),
                (OPERATOR, "=".to_string()),
                (WHITESPACE, " ".to_string()),
                (IDENTIFIER, "a".to_string()),
                (WHITESPACE, " ".to_string()),
                (BACKSLASH, "\\".to_string()),
                (NEWLINE, "\r\n".to_string()),
                (INDENT, "\t".to_string()),
                (IDENTIFIER, "b".to_string()),
                (NEWLINE, "\r\n".to_string()),
                (IDENTIFIER, "all".to_string()),
                (OPERATOR, ":".to_string()),
                (NEWLINE, "\r\n".to_string()),
                (INDENT, "\t".to_string()),
                (TEXT, "echo".to_string()),
                (NEWLINE, "\r\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_lone_cr() {
        // Only CRLF and LF end a line; a lone CR is an ordinary character.
        assert_eq!(
            lex_default("X = a\rb\\\rc\r\r\n# d\re\nall:\n\tf\rg\n"),
            vec![
                (IDENTIFIER, "X".to_string()),
                (WHITESPACE, " ".to_string()),
                (OPERATOR, "=".to_string()),
                (WHITESPACE, " ".to_string()),
                (IDENTIFIER, "a".to_string()),
                (TEXT, "\r".to_string()),
                (IDENTIFIER, "b".to_string()),
                (BACKSLASH, "\\".to_string()),
                (TEXT, "\r".to_string()),
                (IDENTIFIER, "c".to_string()),
                (TEXT, "\r".to_string()),
                (NEWLINE, "\r\n".to_string()),
                (COMMENT, "# d\re".to_string()),
                (NEWLINE, "\n".to_string()),
                (IDENTIFIER, "all".to_string()),
                (OPERATOR, ":".to_string()),
                (NEWLINE, "\n".to_string()),
                (INDENT, "\t".to_string()),
                (TEXT, "f\rg".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_shell_assignment_operator() {
        assert_eq!(
            lex_default("X!=cmd\n"),
            vec![
                (IDENTIFIER, "X".to_string()),
                (OPERATOR, "!=".to_string()),
                (IDENTIFIER, "cmd".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_bang_operator() {
        assert_eq!(
            lex_default("a! b\n"),
            vec![
                (IDENTIFIER, "a".to_string()),
                (OPERATOR, "!".to_string()),
                (WHITESPACE, " ".to_string()),
                (IDENTIFIER, "b".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_escaped_hash() {
        assert_eq!(
            lex_default("X=a\\#b # c\n"),
            vec![
                (IDENTIFIER, "X".to_string()),
                (OPERATOR, "=".to_string()),
                (IDENTIFIER, "a".to_string()),
                (TEXT, "\\#".to_string()),
                (IDENTIFIER, "b".to_string()),
                (WHITESPACE, " ".to_string()),
                (COMMENT, "# c".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_escaped_backslash_before_hash() {
        // `\\#` is an escaped backslash followed by a comment.
        assert_eq!(
            lex_default("X=a\\\\#c\n"),
            vec![
                (IDENTIFIER, "X".to_string()),
                (OPERATOR, "=".to_string()),
                (IDENTIFIER, "a".to_string()),
                (BACKSLASH, "\\".to_string()),
                (BACKSLASH, "\\".to_string()),
                (COMMENT, "#c".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_hash_after_bracket() {
        let bsd = vec![
            (IDENTIFIER, "X".to_string()),
            (OPERATOR, "=".to_string()),
            (DOLLAR, "$".to_string()),
            (LBRACE, "{".to_string()),
            (IDENTIFIER, "L".to_string()),
            (OPERATOR, ":".to_string()),
            (TEXT, "[".to_string()),
            (TEXT, "#".to_string()),
            (TEXT, "]".to_string()),
            (RBRACE, "}".to_string()),
            (NEWLINE, "\n".to_string()),
        ];
        assert_eq!(lex("X=${L:[#]}\n", Some(MakefileVariant::BSDMake)), bsd);
        assert_eq!(lex("X=${L:[#]}\n", None), bsd);
        assert_eq!(lex("X=${L:[#]}\n", Some(MakefileVariant::GNUMake)), bsd);
        assert_eq!(
            lex("X=${L:[#]}\n", Some(MakefileVariant::NMake)),
            vec![
                (IDENTIFIER, "X".to_string()),
                (OPERATOR, "=".to_string()),
                (DOLLAR, "$".to_string()),
                (LBRACE, "{".to_string()),
                (IDENTIFIER, "L".to_string()),
                (OPERATOR, ":".to_string()),
                (TEXT, "[".to_string()),
                (COMMENT, "#]}".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_hash_in_reference() {
        let literal = vec![
            (IDENTIFIER, "X".to_string()),
            (OPERATOR, "=".to_string()),
            (DOLLAR, "$".to_string()),
            (LPAREN, "(".to_string()),
            (IDENTIFIER, "a".to_string()),
            (WHITESPACE, " ".to_string()),
            (TEXT, "#".to_string()),
            (IDENTIFIER, "b".to_string()),
            (RPAREN, ")".to_string()),
            (WHITESPACE, " ".to_string()),
            (COMMENT, "#c".to_string()),
            (NEWLINE, "\n".to_string()),
        ];
        let comment = vec![
            (IDENTIFIER, "X".to_string()),
            (OPERATOR, "=".to_string()),
            (DOLLAR, "$".to_string()),
            (LPAREN, "(".to_string()),
            (IDENTIFIER, "a".to_string()),
            (WHITESPACE, " ".to_string()),
            (COMMENT, "#b) #c".to_string()),
            (NEWLINE, "\n".to_string()),
        ];
        let input = "X=$(a #b) #c\n";
        assert_eq!(lex(input, None), literal);
        assert_eq!(lex(input, Some(MakefileVariant::GNUMake)), literal);
        assert_eq!(lex(input, Some(MakefileVariant::POSIXMake)), literal);
        assert_eq!(lex(input, Some(MakefileVariant::BSDMake)), comment);
        assert_eq!(lex(input, Some(MakefileVariant::NMake)), comment);
    }

    #[test]
    fn test_hash_after_escaped_dollar() {
        assert_eq!(
            lex("X=$$(a #b)\n", Some(MakefileVariant::GNUMake)),
            vec![
                (IDENTIFIER, "X".to_string()),
                (OPERATOR, "=".to_string()),
                (DOLLAR, "$".to_string()),
                (DOLLAR, "$".to_string()),
                (LPAREN, "(".to_string()),
                (IDENTIFIER, "a".to_string()),
                (WHITESPACE, " ".to_string()),
                (COMMENT, "#b)".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_hash_in_recipe_reference() {
        assert_eq!(
            lex("a:\n\techo $(x #y)\n", Some(MakefileVariant::GNUMake)),
            vec![
                (IDENTIFIER, "a".to_string()),
                (OPERATOR, ":".to_string()),
                (NEWLINE, "\n".to_string()),
                (INDENT, "\t".to_string()),
                (TEXT, "echo $(x #y)".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_quote_hiding_reference_close() {
        // The quote does not hide the `}` that closes the reference.
        assert_eq!(
            lex_default("${:U'}=a'\n"),
            vec![
                (DOLLAR, "$".to_string()),
                (LBRACE, "{".to_string()),
                (OPERATOR, ":".to_string()),
                (IDENTIFIER, "U".to_string()),
                (QUOTE, "'".to_string()),
                (RBRACE, "}".to_string()),
                (OPERATOR, "=".to_string()),
                (IDENTIFIER, "a".to_string()),
                (QUOTE, "'".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_quoted_paren_in_reference() {
        // Make does not look at quotes, so the quoted `)` closes the
        // reference.
        assert_eq!(
            lex_default("$(if a,')')\n"),
            vec![
                (DOLLAR, "$".to_string()),
                (LPAREN, "(".to_string()),
                (IDENTIFIER, "if".to_string()),
                (WHITESPACE, " ".to_string()),
                (IDENTIFIER, "a".to_string()),
                (COMMA, ",".to_string()),
                (QUOTE, "'".to_string()),
                (RPAREN, ")".to_string()),
                (QUOTE, "'".to_string()),
                (RPAREN, ")".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_quotes_not_grouped() {
        // Neither GNU make nor BSD make treats quotes specially when
        // reading a line.
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::BSDMake),
            Some(MakefileVariant::POSIXMake),
            Some(MakefileVariant::NMake),
        ] {
            assert_eq!(
                lex("X = '$(Y) \\\n b' \"a#b\"\n", variant),
                vec![
                    (IDENTIFIER, "X".to_string()),
                    (WHITESPACE, " ".to_string()),
                    (OPERATOR, "=".to_string()),
                    (WHITESPACE, " ".to_string()),
                    (QUOTE, "'".to_string()),
                    (DOLLAR, "$".to_string()),
                    (LPAREN, "(".to_string()),
                    (IDENTIFIER, "Y".to_string()),
                    (RPAREN, ")".to_string()),
                    (WHITESPACE, " ".to_string()),
                    (BACKSLASH, "\\".to_string()),
                    (NEWLINE, "\n".to_string()),
                    (INDENT, " ".to_string()),
                    (IDENTIFIER, "b".to_string()),
                    (QUOTE, "'".to_string()),
                    (WHITESPACE, " ".to_string()),
                    (QUOTE, "\"".to_string()),
                    (IDENTIFIER, "a".to_string()),
                    (COMMENT, "#b\"".to_string()),
                    (NEWLINE, "\n".to_string()),
                ],
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_comment_continuation() {
        assert_eq!(
            lex_default("# a \\\nb\n# c \\\\\nX=1\n"),
            vec![
                (COMMENT, "# a \\\nb".to_string()),
                (NEWLINE, "\n".to_string()),
                (COMMENT, "# c \\\\".to_string()),
                (NEWLINE, "\n".to_string()),
                (IDENTIFIER, "X".to_string()),
                (OPERATOR, "=".to_string()),
                (IDENTIFIER, "1".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_punctuation_is_text() {
        assert_eq!(
            lex_default("X = a && b\n"),
            vec![
                (IDENTIFIER, "X".to_string()),
                (WHITESPACE, " ".to_string()),
                (OPERATOR, "=".to_string()),
                (WHITESPACE, " ".to_string()),
                (IDENTIFIER, "a".to_string()),
                (WHITESPACE, " ".to_string()),
                (TEXT, "&".to_string()),
                (TEXT, "&".to_string()),
                (WHITESPACE, " ".to_string()),
                (IDENTIFIER, "b".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_bare_export() {
        assert_eq!(
            lex_default(
                r#"export
"#
            )
            .iter()
            .map(|(kind, text)| (*kind, text.as_str()))
            .collect::<Vec<_>>(),
            vec![(IDENTIFIER, "export"), (NEWLINE, "\n"),]
        );
    }

    #[test]
    fn test_export() {
        assert_eq!(
            lex_default(
                r#"export VARIABLE
"#
            )
            .iter()
            .map(|(kind, text)| (*kind, text.as_str()))
            .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "export"),
                (WHITESPACE, " "),
                (IDENTIFIER, "VARIABLE"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_export_assignment() {
        assert_eq!(
            lex_default(
                r#"export VARIABLE := value
"#
            )
            .iter()
            .map(|(kind, text)| (*kind, text.as_str()))
            .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "export"),
                (WHITESPACE, " "),
                (IDENTIFIER, "VARIABLE"),
                (WHITESPACE, " "),
                (OPERATOR, ":="),
                (WHITESPACE, " "),
                (IDENTIFIER, "value"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_multiple_prerequisites() {
        assert_eq!(
            lex_default(
                r#"rule: prerequisite1 prerequisite2
	recipe

"#
            )
            .iter()
            .map(|(kind, text)| (*kind, text.as_str()))
            .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "rule"),
                (OPERATOR, ":"),
                (WHITESPACE, " "),
                (IDENTIFIER, "prerequisite1"),
                (WHITESPACE, " "),
                (IDENTIFIER, "prerequisite2"),
                (NEWLINE, "\n"),
                (INDENT, "\t"),
                (TEXT, "recipe"),
                (NEWLINE, "\n"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_variable_question() {
        assert_eq!(
            lex_default("VARIABLE ?= value\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "VARIABLE"),
                (WHITESPACE, " "),
                (OPERATOR, "?="),
                (WHITESPACE, " "),
                (IDENTIFIER, "value"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_conditional() {
        assert_eq!(
            lex_default(
                r#"ifneq (a, b)
endif
"#
            )
            .iter()
            .map(|(kind, text)| (*kind, text.as_str()))
            .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "ifneq"),
                (WHITESPACE, " "),
                (LPAREN, "("),
                (IDENTIFIER, "a"),
                (COMMA, ","),
                (WHITESPACE, " "),
                (IDENTIFIER, "b"),
                (RPAREN, ")"),
                (NEWLINE, "\n"),
                (IDENTIFIER, "endif"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_variable_paren() {
        assert_eq!(
            lex_default("VARIABLE = $(value)\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "VARIABLE"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (DOLLAR, "$"),
                (LPAREN, "("),
                (IDENTIFIER, "value"),
                (RPAREN, ")"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_variable_paren2() {
        assert_eq!(
            lex_default("VARIABLE = $(value)$(value2)\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "VARIABLE"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (DOLLAR, "$"),
                (LPAREN, "("),
                (IDENTIFIER, "value"),
                (RPAREN, ")"),
                (DOLLAR, "$"),
                (LPAREN, "("),
                (IDENTIFIER, "value2"),
                (RPAREN, ")"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_oom() {
        let text = r#"
#!/usr/bin/make -f
#
# debhelper-7 [debian/rules] for cups-pdf
#
# COPYRIGHT © 2003-2021 Martin-Éric Racine <martin-eric.racine@iki.fi>
#
# LICENSE
# GPLv2+: GNU GPL version 2 or later <http://gnu.org/licenses/gpl.html>
#
export CC       := $(shell dpkg-architecture --query DEB_HOST_GNU_TYPE)-gcc
export CPPFLAGS := $(shell dpkg-buildflags --get CPPFLAGS)
export CFLAGS   := $(shell dpkg-buildflags --get CFLAGS)
export LDFLAGS  := $(shell dpkg-buildflags --get LDFLAGS)
#export DEB_BUILD_MAINT_OPTIONS = hardening=+all,-bindnow,-pie
# Append flags for Long File Support (LFS)
# LFS_CPPFLAGS does not exist
export DEB_CFLAGS_MAINT_APPEND  +=$(shell getconf LFS_CFLAGS) $(HARDENING_CFLAGS)
export DEB_LDFLAGS_MAINT_APPEND +=$(shell getconf LFS_LDFLAGS) $(HARDENING_LDFLAGS)

override_dh_auto_build-arch:
	$(CC) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o src/cups-pdf src/cups-pdf.c -lcups

override_dh_auto_clean:
	rm -f src/cups-pdf src/*.o

%:
	dh $@
#EOF
    "#;

        let _lexed = lex_default(text);
    }

    #[test]
    fn test_pattern_rule() {
        assert_eq!(
            lex_default("%.o: %.c\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "%.o"),
                (OPERATOR, ":"),
                (WHITESPACE, " "),
                (IDENTIFIER, "%.c"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_include_directive() {
        assert_eq!(
            lex_default("-include .env\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "-include"),
                (WHITESPACE, " "),
                (IDENTIFIER, ".env"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_slash_in_identifier() {
        assert_eq!(
            lex_default("usr/bin/foo: src/main.o\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "usr/bin/foo"),
                (OPERATOR, ":"),
                (WHITESPACE, " "),
                (IDENTIFIER, "src/main.o"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_backslash_in_variable_continuation() {
        let input = "VAR ?= $(shell cmd | \\\n\t\tsed -rne 's,^V: ([^-]+).*,\\1,p')\n";
        let tokens = lex_default(input);
        // Check that the backslash before '1' is preserved
        let text: String = tokens.iter().map(|(_, t)| t.as_str()).collect();
        assert_eq!(input, text, "Token text reconstruction differs from input");
    }

    #[test]
    fn test_operator_not_greedy() {
        let ops = |input: &str| {
            lex_default(input)
                .into_iter()
                .filter(|(kind, _)| *kind == OPERATOR)
                .map(|(_, text)| text)
                .collect::<Vec<_>>()
        };
        assert_eq!(ops("X?==y\n"), vec!["?=", "="]);
        assert_eq!(ops("X+==y\n"), vec!["+=", "="]);
        assert_eq!(ops("X:==y\n"), vec![":=", "="]);
        assert_eq!(ops("X::==y\n"), vec!["::=", "="]);
        assert_eq!(ops("X:::==y\n"), vec![":::=", "="]);
        assert_eq!(ops("X ?= =y\n"), vec!["?=", "="]);
        assert_eq!(ops("X?=?y\n"), vec!["?="]);
        assert_eq!(ops("X?=:y\n"), vec!["?=", ":"]);
        assert_eq!(ops("X=::y\n"), vec!["=", "::"]);
        assert_eq!(ops("X==y\n"), vec!["=", "="]);
        assert_eq!(ops("a::?b\n"), vec!["::"]);
        assert_eq!(ops("a:::b\n"), vec!["::", ":"]);
        assert_eq!(ops("a?:b\n"), vec![":"]);
        assert_eq!(ops("a:=:b\n"), vec![":=", ":"]);
        assert_eq!(ops("a:: b\n"), vec!["::"]);
        assert_eq!(ops("$(OBJS): %.o: %.c\n"), vec![":", ":"]);
        assert_eq!(ops("$(X:.c=.o)\n"), vec![":", "="]);
        assert_eq!(ops("URL = http://x\n"), vec!["=", ":"]);
        assert_eq!(ops("a b &: c\n"), vec!["&:"]);
        assert_eq!(ops("a b&::c\n"), vec!["&::"]);
        assert_eq!(ops("a&b: c\n"), vec![":"]);
        assert_eq!(ops("X = a && b\n"), vec!["="]);
        assert_eq!(ops("a &:= b\n"), vec![":="]);
    }

    #[test]
    fn test_operator_followed_by_equals_tokens() {
        assert_eq!(
            lex_default("X?==y\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (IDENTIFIER, "X"),
                (OPERATOR, "?="),
                (OPERATOR, "="),
                (IDENTIFIER, "y"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_space_indented_line() {
        assert_eq!(
            lex_default("  X = 1\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (WHITESPACE, "  "),
                (IDENTIFIER, "X"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (IDENTIFIER, "1"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_space_indented_recipe_continuation() {
        assert_eq!(
            lex_default("\techo a \\\n    b\n")
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (INDENT, "\t"),
                (TEXT, "echo a \\"),
                (NEWLINE, "\n"),
                (INDENT, "    "),
                (TEXT, "b"),
                (NEWLINE, "\n"),
            ]
        );
    }

    #[test]
    fn test_nmake_space_indented_line() {
        assert_eq!(
            lex("  echo a \\\n b\n", Some(MakefileVariant::NMake))
                .iter()
                .map(|(kind, text)| (*kind, text.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (INDENT, "  "),
                (TEXT, "echo a \\"),
                (NEWLINE, "\n"),
                (INDENT, " "),
                (TEXT, "b"),
                (NEWLINE, "\n"),
            ]
        );
    }

    fn lex_nmake(input: &str) -> Vec<(SyntaxKind, String)> {
        lex(input, Some(MakefileVariant::NMake))
    }

    fn tokens(tokens: &[(SyntaxKind, &str)]) -> Vec<(SyntaxKind, String)> {
        tokens.iter().map(|(k, t)| (*k, t.to_string())).collect()
    }

    #[test]
    fn test_nmake_caret_escapes() {
        assert_eq!(
            lex_nmake("X = a^#b # c\n"),
            tokens(&[
                (IDENTIFIER, "X"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (IDENTIFIER, "a"),
                (TEXT, "^#"),
                (IDENTIFIER, "b"),
                (WHITESPACE, " "),
                (COMMENT, "# c"),
                (NEWLINE, "\n"),
            ])
        );
        assert_eq!(
            lex_nmake("X = a^\\\nY = ^^#b\n"),
            tokens(&[
                (IDENTIFIER, "X"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (IDENTIFIER, "a"),
                (TEXT, "^\\"),
                (NEWLINE, "\n"),
                (IDENTIFIER, "Y"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (TEXT, "^^"),
                (COMMENT, "#b"),
                (NEWLINE, "\n"),
            ])
        );
        // A caret before any other character is not an escape.
        assert_eq!(
            lex_nmake("X = ^a^$(Y)\n"),
            tokens(&[
                (IDENTIFIER, "X"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (TEXT, "^"),
                (IDENTIFIER, "a"),
                (TEXT, "^$"),
                (LPAREN, "("),
                (IDENTIFIER, "Y"),
                (RPAREN, ")"),
                (NEWLINE, "\n"),
            ])
        );
    }

    #[test]
    fn test_caret_not_escape_in_other_variants() {
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::BSDMake),
            Some(MakefileVariant::POSIXMake),
        ] {
            assert_eq!(
                lex("X = a^#b\n", variant),
                tokens(&[
                    (IDENTIFIER, "X"),
                    (WHITESPACE, " "),
                    (OPERATOR, "="),
                    (WHITESPACE, " "),
                    (IDENTIFIER, "a"),
                    (TEXT, "^"),
                    (COMMENT, "#b"),
                    (NEWLINE, "\n"),
                ]),
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_nmake_caret_newline() {
        // In a macro definition, a caret at the end of the line continues
        // the definition on the next line.
        assert_eq!(
            lex_nmake("X = a^\n\tb\n"),
            tokens(&[
                (IDENTIFIER, "X"),
                (WHITESPACE, " "),
                (OPERATOR, "="),
                (WHITESPACE, " "),
                (IDENTIFIER, "a"),
                (TEXT, "^"),
                (NEWLINE, "\n"),
                (INDENT, "\t"),
                (IDENTIFIER, "b"),
                (NEWLINE, "\n"),
            ])
        );
        // Elsewhere it does not.
        assert_eq!(
            lex_nmake("a: b^\n\tc\n"),
            tokens(&[
                (IDENTIFIER, "a"),
                (OPERATOR, ":"),
                (WHITESPACE, " "),
                (IDENTIFIER, "b"),
                (TEXT, "^"),
                (NEWLINE, "\n"),
                (INDENT, "\t"),
                (TEXT, "c"),
                (NEWLINE, "\n"),
            ])
        );
    }

    #[test]
    fn test_nmake_caret_in_command() {
        // Commands are lexed as a whole, carets included.
        assert_eq!(
            lex_nmake("a:\n\techo ^#a^\\\n"),
            tokens(&[
                (IDENTIFIER, "a"),
                (OPERATOR, ":"),
                (NEWLINE, "\n"),
                (INDENT, "\t"),
                (TEXT, "echo ^#a^\\"),
                (NEWLINE, "\n"),
            ])
        );
    }

    #[test]
    fn test_recipe_prefix() {
        let prefix = recipe_prefix_after;
        assert_eq!(prefix(".RECIPEPREFIX = >\n"), '>');
        assert_eq!(prefix(".RECIPEPREFIX := ab # comment\n"), 'a');
        assert_eq!(prefix("override .RECIPEPREFIX ::= >\n"), '>');
        assert_eq!(prefix("private .RECIPEPREFIX := >\n"), '>');
        assert_eq!(prefix("unexport .RECIPEPREFIX = >\n"), '>');
        assert_eq!(prefix("export override .RECIPEPREFIX = >\n"), '>');
        assert_eq!(prefix("override private\texport .RECIPEPREFIX = >\n"), '>');
        assert_eq!(prefix("override override .RECIPEPREFIX = >\n"), '>');
        assert_eq!(prefix("exported .RECIPEPREFIX = >\n"), '\t');
        assert_eq!(prefix(".RECIPEPREFIX \\\n  = >\n"), '>');
        assert_eq!(prefix(".RECIPEPREFIX = >\n.RECIPEPREFIX =\n"), '\t');
        assert_eq!(prefix(".RECIPEPREFIX = > # c\n"), '>');
        assert_eq!(prefix(".RECIPEPREFIX = # c\n"), '\t');
        assert_eq!(prefix(".RECIPEPREFIX ?= >\n"), '\t');
        assert_eq!(prefix(".RECIPEPREFIX += >\n"), '>');
        assert_eq!(prefix(".RECIPEPREFIX = >\n.RECIPEPREFIX += x\n"), '>');
        assert_eq!(prefix(".RECIPEPREFIX = $(P)\n"), '$');
        assert_eq!(prefix(".RECIPEPREFIXES = >\n"), '\t');
        assert_eq!(prefix("all:\n\t.RECIPEPREFIX = >\n"), '\t');
        let mut lexer = Lexer::new(".RECIPEPREFIX = >\n", Some(MakefileVariant::BSDMake));
        lexer.by_ref().for_each(drop);
        assert_eq!(lexer.recipe_prefix, '\t');
    }

    #[test]
    fn test_define_recipe_prefix() {
        let prefix = |text: &str| {
            let mut lexer = Lexer::new(text, None);
            lexer.by_ref().for_each(drop);
            lexer.recipe_prefix
        };
        assert_eq!(prefix("define .RECIPEPREFIX\n>\nendef\n"), '>');
        assert_eq!(prefix("define .RECIPEPREFIX :=\n>x\nfoo\nendef\n"), '>');
        assert_eq!(prefix("define .RECIPEPREFIX=\n>\nendef\n"), '>');
        assert_eq!(prefix("override define .RECIPEPREFIX # c\n>\nendef\n"), '>');
        assert_eq!(prefix("unexport define .RECIPEPREFIX\n>\nendef\n"), '>');
        assert_eq!(
            prefix("override unexport define .RECIPEPREFIX\n>\nendef\n"),
            '>'
        );
        assert_eq!(prefix("define .RECIPEPREFIX \\\n=\n>\nendef\n"), '>');
        assert_eq!(prefix("define .RECIPEPREFIX\r\n>\r\nendef\r\n"), '>');
        assert_eq!(prefix("define .RECIPEPREFIX\n  >\nendef\n"), ' ');
        assert_eq!(
            prefix(".RECIPEPREFIX = >\ndefine .RECIPEPREFIX\nendef\n"),
            '\t'
        );
        assert_eq!(
            prefix(".RECIPEPREFIX = >\ndefine .RECIPEPREFIX\n\nendef\n"),
            '\t'
        );
        assert_eq!(prefix("define .RECIPEPREFIX\n\nfoo\nendef\n"), '\n');
        // No line starts with that prefix, not even an empty one.
        assert_eq!(
            lex("define .RECIPEPREFIX\n\nfoo\nendef\n\nx\n", None)[9..],
            [
                (NEWLINE, "\n".into()),
                (IDENTIFIER, "x".into()),
                (NEWLINE, "\n".into())
            ]
        );
        assert_eq!(prefix("define .RECIPEPREFIX ?=\n>\nendef\n"), '\t');
        assert_eq!(prefix("define .RECIPEPREFIX +=\n>\nendef\n"), '>');
        assert_eq!(
            prefix(".RECIPEPREFIX = >\ndefine .RECIPEPREFIX +=\n;\nendef\n"),
            '>'
        );
        // The value is not set before the `endef`.
        assert_eq!(prefix("define .RECIPEPREFIX\n>\n"), '\t');
        // A continued line or one starting with the recipe prefix does not
        // end the definition, nor does `endef` followed by a comment.
        assert_eq!(prefix("define .RECIPEPREFIX\n>\\\nendef\n"), '\t');
        assert_eq!(prefix("define .RECIPEPREFIX\n>\n\tendef\n"), '\t');
        assert_eq!(prefix("define .RECIPEPREFIX\n>\nendef#c\n"), '\t');
        assert_eq!(prefix("define .RECIPEPREFIX\n>\n  endef # c\n"), '>');
        assert_eq!(
            prefix(".RECIPEPREFIX = >\ndefine .RECIPEPREFIX\n>endef\n;\nendef\n"),
            '>'
        );
        assert_eq!(
            prefix(".RECIPEPREFIX = >\ndefine .RECIPEPREFIX\n\tendef\n;\nendef\n"),
            '\t'
        );
        // Nested definitions.
        assert_eq!(
            prefix("define .RECIPEPREFIX\n  define X\nendef\n>\nendef\n"),
            ' '
        );
        assert_eq!(
            prefix("define X\ndefine .RECIPEPREFIX\n>\nendef\nendef\n"),
            '\t'
        );
        // An assignment in the body of another variable does not count.
        assert_eq!(prefix("define X\n.RECIPEPREFIX = >\nendef\n"), '\t');
        assert_eq!(prefix("define .RECIPEPREFIXES\n>\nendef\n"), '\t');
        // An assignment to a variable named "define".
        assert_eq!(prefix("define = 1\n.RECIPEPREFIX = >\n"), '>');
    }
}
