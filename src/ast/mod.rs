pub mod archive;
pub mod bsd;
pub mod conditional;
pub mod expression_statement;
pub mod include;
pub mod makefile;
pub mod rule;
pub mod variable;
pub mod vpath;

use crate::lossless::{SyntaxElement, SyntaxNode, SyntaxToken};
use crate::SyntaxKind::{BACKSLASH, INDENT, NEWLINE, WHITESPACE};

/// Whether `token` is the backslash of a backslash-newline line
/// continuation. A backslash escaped by an odd run of preceding backslashes
/// (`\\`) does not continue the line.
fn is_continuation_backslash(token: &SyntaxToken) -> bool {
    token.kind() == BACKSLASH
        && token.next_token().is_some_and(|t| t.kind() == NEWLINE)
        && std::iter::successors(token.prev_token(), |t| t.prev_token())
            .take_while(|t| t.kind() == BACKSLASH)
            .count()
            % 2
            == 0
}

/// Whether `element` is part of a line continuation: the backslash, the
/// newline following it or the indentation of the continued line.
pub(crate) fn is_continuation(element: &SyntaxElement) -> bool {
    let Some(token) = element.as_token() else {
        return false;
    };
    match token.kind() {
        BACKSLASH => is_continuation_backslash(token),
        NEWLINE => token
            .prev_token()
            .is_some_and(|t| is_continuation_backslash(&t)),
        INDENT => token
            .prev_token()
            .is_some_and(|t| is_continuation(&t.into())),
        _ => false,
    }
}

/// The text of `node` with each line continuation and the whitespace around
/// it collapsed into a single space, as GNU make does outside recipes, and
/// any other CRLF line endings converted to LF.
pub(crate) fn collapse_continuations(node: &SyntaxNode) -> String {
    let mut text = String::new();
    let mut in_continuation = false;
    for token in node
        .descendants_with_tokens()
        .filter_map(|it| it.into_token())
    {
        if is_continuation(&token.clone().into()) {
            if !in_continuation {
                text.truncate(text.trim_end_matches([' ', '\t']).len());
                text.push(' ');
                in_continuation = true;
            }
        } else if in_continuation && token.kind() == WHITESPACE {
            // Leading whitespace on the continued line.
        } else {
            in_continuation = false;
            text.push_str(if token.kind() == NEWLINE {
                "\n"
            } else {
                token.text()
            });
        }
    }
    text
}
