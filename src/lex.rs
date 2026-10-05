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
    /// Number of parentheses and braces open inside `$(...)` and `${...}`
    /// references on the current logical line, outside quoted strings.
    reference_depth: usize,
    /// Number of `$` tokens directly before the current one.
    dollars: usize,
    /// The character that starts a recipe line, set with GNU make's
    /// `.RECIPEPREFIX`.
    // TODO: The editing APIs still start new recipe lines with a tab.
    recipe_prefix: char,
    /// Text of the current logical line, if it is not a recipe line.
    line: Option<String>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str, variant: Option<MakefileVariant>) -> Self {
        Lexer {
            input: input.chars().peekable(),
            continuation: false,
            line_type: None,
            pending_backslash_escape: false,
            bsd: matches!(variant, None | Some(MakefileVariant::BSDMake)),
            gnu: variant != Some(MakefileVariant::BSDMake),
            hash_in_references: !matches!(
                variant,
                Some(MakefileVariant::BSDMake | MakefileVariant::NMake)
            ),
            nmake: variant == Some(MakefileVariant::NMake),
            after_lbracket: false,
            recipe_continuation: false,
            reference_depth: 0,
            dollars: 0,
            recipe_prefix: '\t',
            line: Some(String::new()),
        }
    }

    /// Update the recipe prefix if `line` assigns to `.RECIPEPREFIX`.
    // TODO: Handle `define .RECIPEPREFIX`.
    fn update_recipe_prefix(&mut self, line: &str) {
        let line = line.replace("\\\r\n", " ").replace("\\\n", " ");
        let mut rest = line.trim_start();
        for keyword in ["override", "export"] {
            if let Some(r) = rest.strip_prefix(keyword) {
                if r.starts_with(Self::is_whitespace) {
                    rest = r.trim_start();
                }
            }
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
        let first = match value.chars().next() {
            None | Some('#') => None,
            // An immediately expanded reference.
            // TODO: Expand variable references.
            Some('$') if op != "=" && !value.starts_with("$$") => return,
            Some(c) => Some(c),
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

    /// Read up to the end of the line.
    fn read_line(&mut self) -> String {
        let mut result = String::new();
        while !self.at_newline() {
            let Some(c) = self.input.next() else {
                break;
            };
            result.push(c);
        }
        result
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

    /// Check whether a matching close-quote appears on the current line.
    /// Make doesn't treat quotes as syntactic; we only group them so that
    /// embedded parens don't confuse $(...) parsing. If the quote is
    /// unterminated (or asymmetric, like `it's`), grouping would do more
    /// harm than good — so we only group when there's a partner on the
    /// same line. A backslash escapes the next character.
    fn has_matching_close_quote(&self, quote: char) -> bool {
        let mut probe = self.input.clone();
        probe.next(); // Skip the opening quote we already peeked.
        while let Some(c) = probe.next() {
            if c == '\n' {
                return false;
            }
            if c == '\\' {
                probe.next();
                continue;
            }
            if c == quote {
                return true;
            }
        }
        false
    }

    /// Whether the quote at the current position should start a quoted
    /// string. Make doesn't treat quotes as syntactic; grouping only serves
    /// to keep e.g. the `)` in `$(if a,')')` from closing the reference.
    /// Inside a reference, don't group if that would hide the delimiter
    /// closing it, as in `${:U'}=x'`.
    fn should_group_quote(&self, quote: char) -> bool {
        if !self.has_matching_close_quote(quote) {
            return false;
        }
        if self.reference_depth == 0 {
            return true;
        }
        let mut probe = self.input.clone();
        probe.next();
        let mut quoted = Vec::new();
        while let Some(c) = probe.next() {
            if c == quote {
                break;
            }
            quoted.push(c);
            if c == '\\' {
                quoted.extend(probe.next());
            }
        }
        let rest: Vec<char> = probe.take_while(|&c| c != '\n').collect();
        // Whether the open references are closed on this line.
        let closes = |chars: &mut dyn Iterator<Item = &char>| {
            let mut depth = self.reference_depth;
            for c in chars {
                match c {
                    '(' | '{' => depth += 1,
                    ')' | '}' => {
                        depth -= 1;
                        if depth == 0 {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
            false
        };
        closes(&mut rest.iter()) || !closes(&mut quoted.iter().chain(rest.iter()))
    }

    fn read_quoted_string(&mut self) -> String {
        let mut result = String::new();
        let quote = self.input.next().unwrap(); // Consume opening quote
        result.push(quote);

        while let Some(&c) = self.input.peek() {
            if c == quote {
                result.push(c);
                self.input.next();
                break;
            } else if c == '\\' {
                result.push(c);
                self.input.next(); // Consume backslash
                if let Some(next) = self.input.next() {
                    result.push(next);
                }
            } else {
                result.push(c);
                self.input.next();
            }
        }
        result
    }

    /// Read a comment up to the end of the line. Outside recipes, a comment
    /// ending in an unescaped backslash continues on the next line.
    fn read_comment(&mut self) -> String {
        let mut comment = self.read_line();
        while self.line_type == Some(LineType::Other)
            && comment.chars().rev().take_while(|&c| c == '\\').count() % 2 == 1
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
            match (c, self.line_type) {
                (c, None) if c == self.recipe_prefix && c != '\t' && !self.continuation => {
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
                    && ((self.bsd && after_lbracket)
                        || (self.hash_in_references && self.reference_depth > 0)) => {}
                '#' => {
                    return Some((SyntaxKind::COMMENT, self.read_comment()));
                }
                _ => {}
            }

            match self.line_type.unwrap() {
                LineType::Recipe => {
                    let text = self.read_line();
                    let trailing_backslashes =
                        text.chars().rev().take_while(|&c| c == '\\').count();
                    self.recipe_continuation = trailing_backslashes % 2 == 1;
                    Some((SyntaxKind::TEXT, text))
                }
                LineType::Other => match c {
                    c if Self::is_whitespace(c) => {
                        Some((SyntaxKind::WHITESPACE, self.read_while(Self::is_whitespace)))
                    }
                    c if Self::is_valid_identifier_char(c) => Some((
                        SyntaxKind::IDENTIFIER,
                        self.read_while(Self::is_valid_identifier_char),
                    )),
                    '"' | '\'' => {
                        if self.should_group_quote(c) {
                            Some((SyntaxKind::QUOTE, self.read_quoted_string()))
                        } else {
                            // Lone quote — emit as a single-character QUOTE
                            // token so paren counting in $(...) still works.
                            self.input.next();
                            Some((SyntaxKind::QUOTE, c.to_string()))
                        }
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
                    // BSD make has no grouped targets, and takes the `&` in
                    // `a b &: c` as a target.
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
                    '?' | '+' => {
                        let mut text = self.input.next().unwrap().to_string();
                        if let Some(eq) = self.input.next_if_eq(&'=') {
                            text.push(eq);
                        }
                        Some((SyntaxKind::OPERATOR, text))
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
                    '\\' => {
                        self.input.next();
                        // `\#` is a literal hash rather than the start of a
                        // comment.
                        if !escaped && self.input.peek() == Some(&'#') {
                            self.input.next();
                            return Some((SyntaxKind::TEXT, "\\#".to_string()));
                        }
                        // A backslash-newline is a continuation only if this
                        // backslash is not escaped by a preceding one.
                        if !escaped && self.at_newline() {
                            self.continuation = true;
                        }
                        self.pending_backslash_escape = !escaped;
                        Some((SyntaxKind::BACKSLASH, "\\".to_string()))
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
        if self.gnu {
            if self.line_type == Some(LineType::Recipe) {
                self.line = None;
            } else if let Some(line) = &mut self.line {
                line.push_str(&token.1);
            }
            if token.0 == SyntaxKind::NEWLINE && !self.continuation {
                if let Some(line) = self.line.replace(String::new()) {
                    self.update_recipe_prefix(&line);
                }
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
            SyntaxKind::NEWLINE if !self.continuation => self.reference_depth = 0,
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

/// Lex `input`, treating its first line as an ordinary makefile line even if
/// it starts with a tab. Also returns whether the input ends in a line
/// continuation.
pub(crate) fn lex_non_recipe_line(
    input: &str,
    variant: Option<MakefileVariant>,
) -> (Vec<(SyntaxKind, String)>, bool) {
    let mut lexer = Lexer::new(input, variant);
    lexer.line_type = Some(LineType::Other);
    let tokens: Vec<_> = lexer.by_ref().collect();
    // A continued comment takes in the newline and the next line, so if
    // the input ends in a newline that is part of a comment, the comment
    // continues past it.
    let comment_continues = tokens
        .last()
        .is_some_and(|(kind, text)| *kind == SyntaxKind::COMMENT && text.ends_with('\n'));
    (tokens, lexer.continuation || comment_continues)
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
        // Grouping `'}=a'` would hide the `}` that closes the reference.
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
    fn test_quote_hiding_paren_in_reference() {
        // The reference is still closed after the quoted `)`.
        assert_eq!(
            lex_default("$(if a,')')\n"),
            vec![
                (DOLLAR, "$".to_string()),
                (LPAREN, "(".to_string()),
                (IDENTIFIER, "if".to_string()),
                (WHITESPACE, " ".to_string()),
                (IDENTIFIER, "a".to_string()),
                (COMMA, ",".to_string()),
                (QUOTE, "')'".to_string()),
                (RPAREN, ")".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
    }

    #[test]
    fn test_quote_outside_reference() {
        // Braces outside references don't matter to make.
        assert_eq!(
            lex_default("X = '{' '}'\n"),
            vec![
                (IDENTIFIER, "X".to_string()),
                (WHITESPACE, " ".to_string()),
                (OPERATOR, "=".to_string()),
                (WHITESPACE, " ".to_string()),
                (QUOTE, "'{'".to_string()),
                (WHITESPACE, " ".to_string()),
                (QUOTE, "'}'".to_string()),
                (NEWLINE, "\n".to_string()),
            ]
        );
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
        assert_eq!(ops("X?=?y\n"), vec!["?=", "?"]);
        assert_eq!(ops("X?=:y\n"), vec!["?=", ":"]);
        assert_eq!(ops("X=::y\n"), vec!["=", "::"]);
        assert_eq!(ops("X==y\n"), vec!["=", "="]);
        assert_eq!(ops("a::?b\n"), vec!["::", "?"]);
        assert_eq!(ops("a:::b\n"), vec!["::", ":"]);
        assert_eq!(ops("a?:b\n"), vec!["?", ":"]);
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

    #[test]
    fn test_recipe_prefix() {
        let prefix = |text: &str| {
            let mut lexer = Lexer::new(text, None);
            lexer.by_ref().for_each(drop);
            lexer.recipe_prefix
        };
        assert_eq!(prefix(".RECIPEPREFIX = >\n"), '>');
        assert_eq!(prefix(".RECIPEPREFIX := ab # comment\n"), 'a');
        assert_eq!(prefix("override .RECIPEPREFIX ::= >\n"), '>');
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
}
