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
use crate::SyntaxKind::{
    BACKSLASH, COMMENT, DOLLAR, INDENT, LBRACE, LPAREN, NEWLINE, TEXT, WHITESPACE,
};

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

/// Whether `node` is a variable reference delimited by parentheses or
/// braces, such as `$(X)` or `${X}`.
fn is_delimited_reference(node: &SyntaxNode) -> bool {
    let mut children = node.children_with_tokens().map(|it| it.kind());
    matches!(
        (children.next(), children.next()),
        (Some(DOLLAR), Some(LPAREN | LBRACE))
    )
}

/// Whether `token` is inside a delimited variable reference, looking no
/// further up than `root`.
fn in_reference(token: &SyntaxToken, root: &SyntaxNode) -> bool {
    for node in token.parent_ancestors() {
        if is_delimited_reference(&node) {
            return true;
        }
        if &node == root {
            break;
        }
    }
    false
}

/// The text of `tokens` (all within `root`) as GNU make sees it after
/// reading a logical line, before expansion.
///
/// Each line continuation and the whitespace around it is collapsed into a
/// single space, halving the backslashes preceding the one that continues
/// the line, and CRLF line endings are converted to LF.
///
/// With `comments`, the text is also treated as a line from which a
/// trailing comment has been removed: `\#` outside variable references
/// becomes `#`, and the backslashes before it or before the comment are
/// halved.
pub(crate) fn logical_text(
    root: &SyntaxNode,
    tokens: impl IntoIterator<Item = SyntaxToken>,
    comments: bool,
) -> String {
    let mut text = String::new();
    // Backslashes not yet added to `text`, since how many are kept depends
    // on what follows them.
    let mut backslashes = 0;
    let mut in_continuation = false;
    let mut last = None;
    for token in tokens {
        match token.kind() {
            BACKSLASH if is_continuation_backslash(&token) => {
                let kept = backslashes / 2;
                backslashes = 0;
                if kept == 0 {
                    text.truncate(text.trim_end_matches([' ', '\t']).len());
                } else {
                    text.push_str(&"\\".repeat(kept));
                }
                text.push(' ');
                in_continuation = true;
            }
            BACKSLASH => {
                backslashes += 1;
                in_continuation = false;
            }
            NEWLINE | INDENT if is_continuation(&token.clone().into()) => {}
            WHITESPACE if in_continuation => {}
            TEXT if comments && token.text() == "\\#" && !in_reference(&token, root) => {
                text.push_str(&"\\".repeat(backslashes / 2));
                text.push('#');
                backslashes = 0;
                in_continuation = false;
            }
            kind => {
                text.push_str(&"\\".repeat(backslashes));
                backslashes = 0;
                in_continuation = false;
                text.push_str(if kind == NEWLINE { "\n" } else { token.text() });
            }
        }
        last = Some(token);
    }
    let before_comment = last
        .and_then(|t| t.next_token())
        .is_some_and(|t| t.kind() == COMMENT);
    if comments && before_comment {
        backslashes /= 2;
    }
    text.push_str(&"\\".repeat(backslashes));
    text
}

/// The text of `node` with each line continuation and the whitespace around
/// it collapsed into a single space, as GNU make does outside recipes, and
/// any other CRLF line endings converted to LF.
pub(crate) fn collapse_continuations(node: &SyntaxNode) -> String {
    let tokens = node
        .descendants_with_tokens()
        .filter_map(|it| it.into_token());
    logical_text(node, tokens, false)
}
