pub mod archive;
pub mod bsd;
pub mod conditional;
pub mod expression_statement;
pub mod include;
pub mod load;
pub mod makefile;
pub mod rule;
pub mod variable;
pub mod vpath;

use crate::lossless::{SyntaxElement, SyntaxNode, SyntaxToken};
use crate::MakefileVariant;
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

/// The line ending to use for new lines in the tree containing `node`: that
/// of the tree's first line break, or `"\n"` if it has none yet.
pub(crate) fn line_ending(node: &SyntaxNode) -> String {
    let root = node
        .ancestors()
        .last()
        .expect("ancestors() includes the node itself");
    root.descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == NEWLINE)
        .map_or_else(|| "\n".to_string(), |t| t.text().to_string())
}

/// How a make implementation forms a logical line from physical lines.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LineSyntax {
    /// GNU make: whitespace before a line continuation is dropped, and the
    /// backslashes before a continuation, `\#` or a comment are halved.
    /// `#` inside a variable reference is not a comment.
    Gnu,
    /// POSIX make, and GNU make after `.POSIX:`: as GNU make, but the
    /// whitespace before a line continuation is kept.
    Posix,
    /// BSD make: whitespace before a line continuation is kept, backslashes
    /// are never halved, `\#` is unescaped and `#` starts a comment even
    /// inside variable references, and trailing whitespace is removed.
    Bsd,
    /// Microsoft nmake: as POSIX make, but `\#` is not an escape.
    // TODO: Support nmake's `^` escapes, such as `^#` and `^\`.
    NMake,
}

impl From<MakefileVariant> for LineSyntax {
    fn from(variant: MakefileVariant) -> Self {
        match variant {
            MakefileVariant::GNUMake => Self::Gnu,
            MakefileVariant::POSIXMake => Self::Posix,
            MakefileVariant::BSDMake => Self::Bsd,
            MakefileVariant::NMake => Self::NMake,
        }
    }
}

/// The text of `tokens` (all within `root`) as make sees it after reading a
/// logical line, before expansion.
///
/// Each line continuation is collapsed into a single space as described by
/// `syntax`, and CRLF line endings are converted to LF.
///
/// With `comments`, the text is also treated as a line from which a
/// trailing comment has been removed, which makes a difference for `\#`
/// and the backslashes before the comment.
pub(crate) fn logical_text(
    root: &SyntaxNode,
    tokens: impl IntoIterator<Item = SyntaxToken>,
    syntax: LineSyntax,
    comments: bool,
) -> String {
    let halve = |n: usize| if syntax == LineSyntax::Bsd { n } else { n / 2 };
    let mut text = String::new();
    // Backslashes not yet added to `text`, since how many are kept depends
    // on what follows them.
    let mut backslashes = 0;
    let mut in_continuation = false;
    // BSD make keeps a backslash-escaped space when removing trailing
    // whitespace; this is the length of the text up to such a space.
    let mut keep = 0;
    let mut last = None;
    for token in tokens {
        match token.kind() {
            COMMENT if comments && syntax == LineSyntax::Bsd => break,
            // The tree may come from a variant in which `#` inside a
            // reference is literal, but BSD make only exempts `[#`.
            TEXT if comments
                && syntax == LineSyntax::Bsd
                && token.text() == "#"
                && !token.prev_token().is_some_and(|t| t.text().ends_with('[')) =>
            {
                break
            }
            BACKSLASH if is_continuation_backslash(&token) => {
                let kept = halve(backslashes);
                backslashes = 0;
                if kept == 0 && syntax == LineSyntax::Gnu {
                    text.truncate(text.trim_end_matches([' ', '\t']).len());
                }
                text.push_str(&"\\".repeat(kept));
                text.push(' ');
                in_continuation = true;
            }
            BACKSLASH => {
                backslashes += 1;
                in_continuation = false;
            }
            NEWLINE | INDENT if is_continuation(&token.clone().into()) => {}
            WHITESPACE if in_continuation => {}
            TEXT if comments && token.text() == "\\#" => match syntax {
                LineSyntax::NMake => {
                    text.push_str(&"\\".repeat(backslashes + 1));
                    backslashes = 0;
                    break;
                }
                LineSyntax::Gnu | LineSyntax::Posix if in_reference(&token, root) => {
                    text.push_str(&"\\".repeat(backslashes));
                    text.push_str(token.text());
                    backslashes = 0;
                    in_continuation = false;
                }
                _ => {
                    text.push_str(&"\\".repeat(halve(backslashes)));
                    text.push('#');
                    backslashes = 0;
                    in_continuation = false;
                }
            },
            kind => {
                text.push_str(&"\\".repeat(backslashes));
                if backslashes % 2 == 1 && kind == WHITESPACE {
                    keep = text.len() + 1;
                }
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
        backslashes = halve(backslashes);
    }
    text.push_str(&"\\".repeat(backslashes));
    if syntax == LineSyntax::Bsd {
        text.truncate(text.trim_end_matches([' ', '\t']).len().max(keep));
    }
    text
}

/// The text of `node` with each line continuation and the whitespace around
/// it collapsed into a single space, as GNU make does outside recipes, and
/// any other CRLF line endings converted to LF.
pub(crate) fn collapse_continuations(node: &SyntaxNode) -> String {
    let tokens = node
        .descendants_with_tokens()
        .filter_map(|it| it.into_token());
    logical_text(node, tokens, LineSyntax::Gnu, false)
}
