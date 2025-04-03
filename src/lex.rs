use crate::SyntaxKind;
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
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer {
            input: input.chars().peekable(),
            line_type: None,
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
            || c == '.'
            || c == '-'
            || c == '%'
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
                self.input.next(); // Consume backslash
                if let Some(next) = self.input.next() {
                    // Handle any escaped character, not just quotes
                    result.push(next);
                }
            } else if c == '$' {
                // Handle variable references inside quotes
                result.push(c);
                self.input.next();
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
        if let Some(&c) = self.input.peek() {
            match (c, self.line_type) {
                ('\t', None) => {
                    self.input.next();
                    self.line_type = Some(LineType::Recipe);
                    return Some((SyntaxKind::INDENT, "\t".to_string()));
                }
                (' ', None) => {
                    // Check if this is the start of a space-indented recipe (2 or 4 spaces)
                    let spaces = self.read_while(|ch| ch == ' ');
                    if spaces.len() >= 2 {
                        self.line_type = Some(LineType::Recipe);
                        return Some((SyntaxKind::INDENT, spaces));
                    } else {
                        // If just a single space, treat as normal whitespace
                        self.line_type = Some(LineType::Other);
                        return Some((SyntaxKind::WHITESPACE, spaces));
                    }
                }
                (_, None) => {
                    self.line_type = Some(LineType::Other);
                }
                (_, _) => {}
            }

            match c {
                c if Self::is_newline(c) => {
                    self.line_type = None;
                    return Some((SyntaxKind::NEWLINE, self.input.next()?.to_string()));
                }
                '#' => {
                    return Some((
                        SyntaxKind::COMMENT,
                        self.read_while(|c| !Self::is_newline(c)),
                    ));
                }
                _ => {}
            }

            match self.line_type.unwrap() {
                LineType::Recipe => {
                    Some((SyntaxKind::TEXT, self.read_while(|c| !Self::is_newline(c))))
                }
                LineType::Other => match c {
                    c if Self::is_whitespace(c) => {
                        Some((SyntaxKind::WHITESPACE, self.read_while(Self::is_whitespace)))
                    }
                    c if Self::is_valid_identifier_char(c) => Some((
                        SyntaxKind::IDENTIFIER,
                        self.read_while(Self::is_valid_identifier_char),
                    )),
                    '"' | '\'' => Some((SyntaxKind::QUOTE, self.read_quoted_string())),
                    ':' | '=' | '?' | '+' => {
                        let text = self.input.next().unwrap().to_string()
                            + self
                                .read_while(|c| c == ':' || c == '=' || c == '?')
                                .as_str();
                        Some((SyntaxKind::OPERATOR, text))
                    }
                    '(' => {
                        self.input.next();
                        Some((SyntaxKind::LPAREN, "(".to_string()))
                    }
                    ')' => {
                        self.input.next();
                        Some((SyntaxKind::RPAREN, ")".to_string()))
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
                        Some((SyntaxKind::BACKSLASH, "\\".to_string()))
                    }
                    _ => {
                        self.input.next();
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

pub(crate) fn lex(input: &str) -> Vec<(SyntaxKind, String)> {
    let mut lexer = Lexer::new(input);
    lexer.by_ref().collect::<Vec<_>>()
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::SyntaxKind::*;

    #[test]
    fn test_empty() {
        assert_eq!(lex(""), vec![]);
    }

    #[test]
    fn test_simple() {
        assert_eq!(
            lex(r#"VARIABLE = value

rule: prerequisite
	recipe
"#)
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
    fn test_bare_export() {
        assert_eq!(
            lex(r#"export
"#)
            .iter()
            .map(|(kind, text)| (*kind, text.as_str()))
            .collect::<Vec<_>>(),
            vec![(IDENTIFIER, "export"), (NEWLINE, "\n"),]
        );
    }

    #[test]
    fn test_export() {
        assert_eq!(
            lex(r#"export VARIABLE
"#)
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
            lex(r#"export VARIABLE := value
"#)
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
            lex(r#"rule: prerequisite1 prerequisite2
	recipe

"#)
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
            lex("VARIABLE ?= value\n")
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
            lex(r#"ifneq (a, b)
endif
"#)
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
            lex("VARIABLE = $(value)\n")
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
            lex("VARIABLE = $(value)$(value2)\n")
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

        let _lexed = lex(text);
    }

    #[test]
    fn test_pattern_rule() {
        assert_eq!(
            lex("%.o: %.c\n")
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
            lex("-include .env\n")
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
}
