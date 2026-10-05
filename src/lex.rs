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
    /// Whether the previous token was a `[`. BSD make does not treat `#` as
    /// a comment there, so that the `:[#]` modifier works.
    after_lbracket: bool,
    /// Whether the previous line was a recipe line ending in a backslash, so
    /// that this line continues the recipe.
    recipe_continuation: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str, variant: Option<MakefileVariant>) -> Self {
        Lexer {
            input: input.chars().peekable(),
            continuation: false,
            line_type: None,
            pending_backslash_escape: false,
            bsd: matches!(variant, None | Some(MakefileVariant::BSDMake)),
            after_lbracket: false,
            recipe_continuation: false,
        }
    }

    fn is_whitespace(c: char) -> bool {
        c == ' ' || c == '\t'
    }

    fn is_newline(c: char) -> bool {
        c == '\n' || c == '\r'
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
            if Self::is_newline(c) {
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
                (' ', None) if recipe_continuation => {
                    // Space-indented continuation of a recipe line
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
                c if Self::is_newline(c) => {
                    self.line_type = None;
                    let mut text = self.input.next()?.to_string();
                    // GNU make treats CRLF as a single line ending.
                    if c == '\r' {
                        if let Some(lf) = self.input.next_if_eq(&'\n') {
                            text.push(lf);
                        }
                    }
                    return Some((SyntaxKind::NEWLINE, text));
                }
                '#' if !(self.bsd && after_lbracket && self.line_type == Some(LineType::Other)) => {
                    return Some((
                        SyntaxKind::COMMENT,
                        self.read_while(|c| !Self::is_newline(c)),
                    ));
                }
                _ => {}
            }

            match self.line_type.unwrap() {
                LineType::Recipe => {
                    let text = self.read_while(|c| !Self::is_newline(c));
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
                        if self.has_matching_close_quote(c) {
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
                        if !escaped && self.input.peek().is_some_and(|&c| Self::is_newline(c)) {
                            self.continuation = true;
                        }
                        self.pending_backslash_escape = !escaped;
                        Some((SyntaxKind::BACKSLASH, "\\".to_string()))
                    }
                    _ => {
                        self.input.next();
                        self.after_lbracket = c == '[';
                        Some((SyntaxKind::ERROR, c.to_string()))
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
        self.next_token()
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
    let tokens = lexer.by_ref().collect();
    (tokens, lexer.continuation)
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
            (ERROR, "[".to_string()),
            (ERROR, "#".to_string()),
            (ERROR, "]".to_string()),
            (RBRACE, "}".to_string()),
            (NEWLINE, "\n".to_string()),
        ];
        assert_eq!(lex("X=${L:[#]}\n", Some(MakefileVariant::BSDMake)), bsd);
        assert_eq!(lex("X=${L:[#]}\n", None), bsd);
        assert_eq!(
            lex("X=${L:[#]}\n", Some(MakefileVariant::GNUMake)),
            vec![
                (IDENTIFIER, "X".to_string()),
                (OPERATOR, "=".to_string()),
                (DOLLAR, "$".to_string()),
                (LBRACE, "{".to_string()),
                (IDENTIFIER, "L".to_string()),
                (OPERATOR, ":".to_string()),
                (ERROR, "[".to_string()),
                (COMMENT, "#]}".to_string()),
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
}
