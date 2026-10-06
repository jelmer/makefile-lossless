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

use crate::lex::NMAKE_ESCAPABLE;
use crate::lossless::{detached_elements, SyntaxElement, SyntaxNode, SyntaxToken};
use crate::MakefileVariant;
use crate::SyntaxKind::{
    self, BACKSLASH, BLANK_LINE, COMMENT, CONDITIONAL, CONDITIONAL_ENDIF, CONDITIONAL_IF,
    DIRECTIVE, DOLLAR, EXPRESSION_STATEMENT, FOR_END, FOR_HEADER, FOR_LOOP, INCLUDE, INDENT,
    LBRACE, LOAD, LPAREN, NEWLINE, RECIPE, RULE, TEXT, VARIABLE, VPATH, WHITESPACE,
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

/// Whether nodes of this kind hold the line break that ends them, rather
/// than being part of a longer line.
fn holds_line_break(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        RULE | RECIPE
            | VARIABLE
            | INCLUDE
            | VPATH
            | CONDITIONAL
            | CONDITIONAL_IF
            | CONDITIONAL_ENDIF
            | FOR_LOOP
            | FOR_HEADER
            | FOR_END
            | DIRECTIVE
            | EXPRESSION_STATEMENT
            | LOAD
            | BLANK_LINE
    )
}

/// The last token in `node`.
///
/// rowan's `SyntaxNode::last_token` only follows the last child, so it returns
/// None when that child is an empty node, which our trees contain (e.g. the
/// prerequisites of `a:` or the value of `X =`).
// TODO: rowan 0.18 walks past empty children, so this can probably be dropped
// after upgrading to it.
fn last_token(node: &SyntaxNode) -> Option<SyntaxToken> {
    node.descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .last()
}

/// `node`, or a copy of it with `eol` appended if it doesn't end in a line
/// break, so that it can be inserted in front of another line.
pub(crate) fn with_trailing_newline(node: &SyntaxNode, eol: &str) -> SyntaxNode {
    if last_token(node).is_none_or(|t| t.kind() == NEWLINE) {
        return node.clone();
    }
    let copy = SyntaxNode::new_root_mut(node.green().into_owned());
    terminate_line_before(&copy, copy.children_with_tokens().count(), eol);
    copy
}

/// Make sure the text before child `index` of `parent` ends in a line
/// break, so that a new line can be inserted there. If it doesn't, `eol` is
/// added where the parser would have put it. Returns the index to insert at,
/// which shifts if the line break was added to `parent` itself.
pub(crate) fn terminate_line_before(parent: &SyntaxNode, index: usize, eol: &str) -> usize {
    let Some((prev, last)) = parent
        .children_with_tokens()
        .take(index)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .find_map(|it| {
            let last = match &it {
                SyntaxElement::Node(n) => last_token(n)?,
                SyntaxElement::Token(t) => t.clone(),
            };
            Some((it, last))
        })
    else {
        return index;
    };
    if last.kind() == NEWLINE {
        return index;
    }
    let newline = detached_elements(&[(NEWLINE, eol)], None);
    match prev {
        SyntaxElement::Node(mut node) if holds_line_break(node.kind()) => {
            while let Some(child) = node
                .last_child_or_token()
                .and_then(|it| it.into_node())
                .filter(|n| holds_line_break(n.kind()))
            {
                node = child;
            }
            let len = node.children_with_tokens().count();
            node.splice_children(len..len, newline);
            index
        }
        _ => {
            parent.splice_children(index..index, newline);
            index + 1
        }
    }
}

/// The index in the parent of `node` before the comment lines directly
/// above it: consecutive whole-line comments, other than a shebang, with no
/// blank line between them and `node`. Such comments document `node`, so
/// anything inserted before it should go before them.
///
/// The parser puts comments that follow a recipe in the preceding rule, so
/// they are moved out of it to the parent of `node` first.
pub(crate) fn index_before_doc_comment(node: &SyntaxNode) -> usize {
    let parent = node.parent().expect("node must have a parent");
    let mut start = None;
    let mut token = node
        .descendants_with_tokens()
        .find_map(|it| it.into_token())
        .and_then(|t| t.prev_token());
    while let Some(newline) = token.filter(|t| t.kind() == NEWLINE) {
        let Some(comment) = newline.prev_token().filter(|t| {
            t.kind() == COMMENT
                && !t.text().starts_with("#!")
                && t.parent_ancestors().any(|a| a == parent)
        }) else {
            break;
        };
        // Only whole-line comments count, not trailing ones like `X = 1 # x`
        let before = comment.prev_token();
        if before.as_ref().is_some_and(|t| t.kind() != NEWLINE) {
            break;
        }
        start = Some(comment);
        token = before;
    }
    let Some(start) = start else {
        return node.index();
    };
    let mut element = SyntaxElement::Token(start);
    loop {
        let container = element.parent().expect("element is below parent");
        if container == parent {
            return element.index();
        }
        let index = element.index();
        let tail: Vec<_> = container.children_with_tokens().skip(index).collect();
        container.splice_children(index..index + tail.len(), vec![]);
        let after = container.index() + 1;
        container
            .parent()
            .expect("container is below parent")
            .splice_children(after..after, tail);
        element = container
            .next_sibling_or_token()
            .expect("tail was moved after container");
    }
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
    /// Microsoft nmake: as POSIX make, but `\#` is not an escape. Instead,
    /// a caret escapes the characters in [`NMAKE_ESCAPABLE`], and one at
    /// the end of a line of a macro definition stands for a newline.
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
/// and the backslashes before the comment, and nmake's `^` escapes are
/// unescaped.
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
            TEXT if comments && syntax == LineSyntax::NMake && token.text().starts_with('^') => {
                text.push_str(&"\\".repeat(backslashes));
                backslashes = 0;
                in_continuation = false;
                match token.text().strip_prefix('^') {
                    Some(c) if c.len() == 1 && c.starts_with(NMAKE_ESCAPABLE) => text.push_str(c),
                    // The newline that follows stands for the caret.
                    Some("")
                        if token.next_token().is_some_and(|t| {
                            t.kind() == NEWLINE && t.parent_ancestors().any(|n| &n == root)
                        }) => {}
                    _ => text.push_str(token.text()),
                }
            }
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
        // BSD make removes anything `isspace()` accepts.
        let trimmed = text.trim_end_matches([' ', '\t', '\r', '\x0b', '\x0c']);
        text.truncate(trimmed.len().max(keep));
    }
    text
}

/// Escape each `#` in `path` outside variable references, so that make
/// does not read it as the start of a comment.
///
/// GNU make halves the backslashes before `\#` and, if `before_comment`,
/// those at the end of the path; BSD make does neither and also starts a
/// comment at a `#` inside a variable reference.
pub(crate) fn escape_hashes(path: &str, bsd: bool, before_comment: bool) -> String {
    let mut escaped = String::new();
    let mut backslashes = 0;
    // The closing delimiters of the variable references `c` is in.
    let mut closers = Vec::new();
    let mut chars = path.chars().peekable();
    while let Some(c) = chars.next() {
        escaped.push(c);
        match c {
            '\\' => {
                backslashes += 1;
                continue;
            }
            '$' => match chars.next_if(|n| matches!(n, '(' | '{' | '$')) {
                Some('(') => {
                    escaped.push('(');
                    closers.push(')');
                }
                Some('{') => {
                    escaped.push('{');
                    closers.push('}');
                }
                Some(dollar) => escaped.push(dollar),
                None => {}
            },
            '(' if !closers.is_empty() => closers.push(')'),
            '{' if !closers.is_empty() => closers.push('}'),
            ')' | '}' if closers.last() == Some(&c) => {
                closers.pop();
            }
            '#' if bsd || closers.is_empty() => {
                escaped.pop();
                if !bsd {
                    escaped.push_str(&"\\".repeat(backslashes));
                }
                escaped.push_str("\\#");
            }
            _ => {}
        }
        backslashes = 0;
    }
    if before_comment && !bsd {
        escaped.push_str(&"\\".repeat(backslashes));
    }
    escaped
}

/// The text of `node` with each line continuation collapsed into a single
/// space as described by `syntax`, and any other CRLF line endings
/// converted to LF.
pub(crate) fn collapse_continuations(node: &SyntaxNode, syntax: LineSyntax) -> String {
    let tokens = node
        .descendants_with_tokens()
        .filter_map(|it| it.into_token());
    logical_text(node, tokens, syntax, false)
}
