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
        c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '-'
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
                    return Some((SyntaxKind::COMMENT, self.read_while(|c| !Self::is_newline(c))));
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
                    c if Self::is_valid_identifier_char(c) => {
                        Some((SyntaxKind::IDENTIFIER, self.read_while(Self::is_valid_identifier_char)))
                    }
                    ':' | '=' | '?'| '+' => {
                        Some((SyntaxKind::OPERATOR, self.read_while(|c| c == ':' || c == '=' || c == '?')))
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
                    '"' => {
                        self.input.next();
                        Some((SyntaxKind::QUOTE, "\"".to_string()))
                    }
                    _ => {
                        self.input.next();
                        Some((SyntaxKind::ERROR, c.to_string()))
                    }
                }
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
    use crate::SyntaxKind::*;
    #[test]
    fn test_empty() {
        assert_eq!(super::lex(""), vec![]);
    }

    #[test]
    fn test_simple() {
        assert_eq!(
            super::lex(
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
    fn test_multiple_prerequisites() {
        assert_eq!(
            super::lex(
                r#"rule: prerequisite1 prerequisite2
	recipe

"#            )
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
            super::lex("VARIABLE ?= value\n").iter().map(|(kind, text)| (*kind, text.as_str())).collect::<Vec<_>>(),
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
            super::lex(r#"ifneq (a, b)
endif
"#).iter().map(|(kind, text)| (*kind, text.as_str())).collect::<Vec<_>>(),
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
            super::lex("VARIABLE = $(value)\n").iter().map(|(kind, text)| (*kind, text.as_str())).collect::<Vec<_>>(),
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
            super::lex("VARIABLE = $(value)$(value2)\n").iter().map(|(kind, text)| (*kind, text.as_str())).collect::<Vec<_>>(),
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
}
