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
mod word_list;

use crate::lex::NMAKE_ESCAPABLE;
use crate::lossless::{
    detached_elements, Error, ErrorInfo, ParseError, SyntaxElement, SyntaxNode, SyntaxToken,
};
use crate::MakefileVariant;
use crate::SyntaxKind::{
    self, BACKSLASH, BLANK_LINE, COMMENT, CONDITIONAL, CONDITIONAL_ENDIF, CONDITIONAL_IF,
    DIRECTIVE, DOLLAR, EXPRESSION_STATEMENT, FOR_END, FOR_HEADER, FOR_LOOP, INCLUDE, INDENT,
    LBRACE, LOAD, LPAREN, NEWLINE, PREREQUISITE, RECIPE, RULE, TEXT, VARIABLE, VPATH, WHITESPACE,
};
use std::ops::Range;

/// An error for invalid input to the method `context`.
pub(crate) fn edit_error(context: &str, message: String) -> Error {
    Error::Parse(ParseError {
        errors: vec![ErrorInfo {
            kind: crate::ParseErrorKind::Other,
            message,
            line: 1,
            context: context.to_string(),
        }],
    })
}

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

/// A line directly above an item that holds nothing but a comment or
/// whitespace.
pub(crate) struct LineAbove {
    /// The tokens of the line in source order, including its line ending.
    pub(crate) tokens: Vec<SyntaxToken>,
    /// The comment on the line, or `None` for a blank line.
    pub(crate) comment: Option<SyntaxToken>,
}

/// The token before `token`. Unlike [`SyntaxToken::prev_token`], this
/// skips nodes without tokens, such as an empty PREREQUISITES node.
pub(crate) fn prev_token(token: &SyntaxToken) -> Option<SyntaxToken> {
    let mut element = SyntaxElement::Token(token.clone());
    loop {
        let Some(prev) = element.prev_sibling_or_token() else {
            element = element.parent()?.into();
            continue;
        };
        match prev {
            SyntaxElement::Token(t) => return Some(t),
            SyntaxElement::Node(n) => match n
                .descendants_with_tokens()
                .filter_map(|it| it.into_token())
                .last()
            {
                Some(t) => return Some(t),
                None => element = n.into(),
            },
        }
    }
}

/// The token after `token`, skipping nodes without tokens.
pub(crate) fn next_token(token: &SyntaxToken) -> Option<SyntaxToken> {
    let mut element = SyntaxElement::Token(token.clone());
    loop {
        let Some(next) = element.next_sibling_or_token() else {
            element = element.parent()?.into();
            continue;
        };
        match next {
            SyntaxElement::Token(t) => return Some(t),
            SyntaxElement::Node(n) => {
                match n.descendants_with_tokens().find_map(|it| it.into_token()) {
                    Some(t) => return Some(t),
                    None => element = n.into(),
                }
            }
        }
    }
}

/// Whether a line starts after `prev`, the token before it.
fn starts_line(prev: Option<&SyntaxToken>) -> bool {
    prev.is_none_or(|t| t.kind() == NEWLINE && !is_continuation(&t.clone().into()))
}

/// The indentation before `node`, if it starts a line.
pub(crate) fn line_indent(node: &SyntaxNode) -> Option<SyntaxToken> {
    let indent = prev_token(&node.first_token()?)?;
    (indent.kind() == WHITESPACE && starts_line(prev_token(&indent).as_ref())).then_some(indent)
}

/// The comment and blank lines directly above `node`, nearest first.
///
/// This stops at a line with anything else on it, so a trailing comment as
/// in `X = 1 # x` and a comment continuing the previous line with a
/// backslash are not included. It also stops at a shebang line and at the
/// start of the parent of `node`. The lines are found by token, as the
/// parser puts comments that follow a recipe into the preceding rule.
///
/// The comment lines before the first blank line document `node`.
pub(crate) fn lines_above(node: &SyntaxNode) -> Vec<LineAbove> {
    let mut lines = Vec::new();
    let Some(parent) = node.parent() else {
        return lines;
    };
    let in_parent = |t: &SyntaxToken| t.parent_ancestors().any(|a| a == parent);
    let Some(first) = node.first_token() else {
        return lines;
    };
    let mut prev = match line_indent(node) {
        Some(indent) => prev_token(&indent),
        None => prev_token(&first),
    };
    if !starts_line(prev.as_ref()) {
        return lines;
    }
    while let Some(newline) = prev.filter(&in_parent) {
        let mut tokens = vec![newline.clone()];
        let mut comment = None;
        let mut before = prev_token(&newline);
        if let Some(token) = before.clone().filter(|t| t.kind() == COMMENT) {
            if token.text().starts_with("#!") || !in_parent(&token) {
                break;
            }
            before = prev_token(&token);
            tokens.push(token.clone());
            comment = Some(token);
        }
        if let Some(token) = before.clone().filter(|t| t.kind() == WHITESPACE) {
            before = prev_token(&token);
            tokens.push(token);
        }
        if !starts_line(before.as_ref()) {
            break;
        }
        tokens.reverse();
        lines.push(LineAbove { tokens, comment });
        prev = before;
    }
    lines
}

/// A green node or token.
pub(crate) type GreenElement = rowan::NodeOrToken<rowan::GreenNode, rowan::GreenToken>;

fn same_green(element: &SyntaxElement, green: &GreenElement) -> bool {
    match (element, green) {
        (rowan::NodeOrToken::Node(node), rowan::NodeOrToken::Node(green)) => {
            *node.green() == **green
        }
        (rowan::NodeOrToken::Token(token), rowan::NodeOrToken::Token(green)) => {
            token.green() == &**green
        }
        _ => false,
    }
}

/// Make the children of `node` the same as `new`, keeping those at the
/// start and the end that already are.
pub(crate) fn replace_children(node: &SyntaxNode, new: Vec<GreenElement>) {
    let old: Vec<_> = node.children_with_tokens().collect();
    let prefix = old
        .iter()
        .zip(&new)
        .take_while(|(old, new)| same_green(old, new))
        .count();
    let suffix = old[prefix..]
        .iter()
        .rev()
        .zip(new[prefix..].iter().rev())
        .take_while(|(old, new)| same_green(old, new))
        .count();
    let middle = new[prefix..new.len() - suffix].to_vec();
    let root = SyntaxNode::new_root_mut(rowan::GreenNode::new(
        crate::SyntaxKind::ROOT.into(),
        middle,
    ));
    let elements: Vec<_> = root.children_with_tokens().collect();
    replace_range(node, prefix..old.len() - suffix, elements);
}

/// Replace the children of `node` in `range` with `new`.
///
/// Use this rather than `node.splice_children(range, new)`, which in
/// rowan 0.16 only detaches the first element of a longer range.
pub(crate) fn replace_range(node: &SyntaxNode, range: Range<usize>, new: Vec<SyntaxElement>) {
    let start = range.start;
    detach_elements(
        node.children_with_tokens()
            .skip(start)
            .take(range.len())
            .collect::<Vec<_>>(),
    );
    node.splice_children(start..start, new);
}

/// Detach `elements` from the tree one by one.
///
/// Use this rather than `splice_children` over a range of several elements,
/// which in rowan 0.16 only detaches the first element of the range.
pub(crate) fn detach_elements(elements: impl IntoIterator<Item = SyntaxElement>) {
    for element in elements {
        element.detach();
    }
}

/// Detach `tokens` from the tree, along with any BLANK_LINE node left empty.
pub(crate) fn detach_tokens(tokens: impl IntoIterator<Item = SyntaxToken>) {
    for token in tokens {
        let parent = token.parent();
        token.detach();
        if let Some(parent) =
            parent.filter(|p| p.kind() == BLANK_LINE && p.first_child_or_token().is_none())
        {
            parent.detach();
        }
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

/// The text of the file containing `parent` before its child `index`.
pub(crate) fn text_before(parent: &SyntaxNode, index: usize) -> String {
    let offset = parent
        .children_with_tokens()
        .nth(index)
        .map_or(parent.text_range().end(), |it| it.text_range().start());
    let root = parent
        .ancestors()
        .last()
        .expect("ancestors() includes the node itself");
    let mut text = root.to_string();
    text.truncate(usize::from(offset - root.text_range().start()));
    text
}

/// The character that starts a recipe line inserted before child `index` of
/// `parent`: a tab, or the one set with GNU make's `.RECIPEPREFIX` in the
/// lines before it.
pub(crate) fn recipe_prefix_before(parent: &SyntaxNode, index: usize) -> char {
    crate::lex::recipe_prefix_after(&text_before(parent, index))
}

/// Replace the recipe prefix `old` at the start of each line of `recipe`
/// with `new`. make strips the prefix from continuation lines too.
pub(crate) fn replace_recipe_prefix(recipe: &SyntaxNode, old: char, new: char) {
    if old == new {
        return;
    }
    let indents: Vec<_> = recipe
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .filter(|t| t.kind() == INDENT && t.text().starts_with(old))
        .collect();
    for token in indents {
        let text = format!("{new}{}", &token.text()[old.len_utf8()..]);
        let index = token.index();
        recipe.splice_children(
            index..index + 1,
            detached_elements(&[(INDENT, &text)], None),
        );
    }
}

/// `node`, or a copy of it in which the recipe lines start with the recipe
/// prefix in effect where they would be after `before`, the text in front
/// of `node`. Recipes on a rule line, after `;`, are left alone.
pub(crate) fn with_recipe_prefix(node: &SyntaxNode, before: &str) -> SyntaxNode {
    let text = format!("{before}{node}");
    let changes = |node: &SyntaxNode| -> Vec<(SyntaxNode, char, char)> {
        let start = node.text_range().start();
        node.descendants()
            .filter(|n| n.kind() == RECIPE)
            .filter_map(|recipe| {
                let first = recipe.first_token().filter(|t| t.kind() == INDENT)?;
                let old = first.text().chars().next().filter(|c| *c != ' ')?;
                let offset = before.len() + usize::from(recipe.text_range().start() - start);
                let new = crate::lex::recipe_prefix_after(&text[..offset]);
                (old != new).then_some((recipe, old, new))
            })
            .collect()
    };
    if changes(node).is_empty() {
        return node.clone();
    }
    let copy = SyntaxNode::new_root_mut(node.green().into_owned());
    for (recipe, old, new) in changes(&copy) {
        replace_recipe_prefix(&recipe, old, new);
    }
    copy
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

/// Line breaks in `node` that are not `eol`, other than those after a
/// backslash: whether a backslash before a CRLF continues the line depends
/// on the make variant, which the tree doesn't record.
fn foreign_line_breaks(node: &SyntaxNode, eol: &str) -> Vec<SyntaxToken> {
    node.descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .filter(|t| {
            t.kind() == NEWLINE
                && t.text() != eol
                && t.prev_token().is_none_or(|p| !p.text().ends_with('\\'))
        })
        .collect()
}

/// `node`, or a copy of it in which line breaks are `eol` and with `eol`
/// appended if it doesn't end in a line break, so that it can be inserted
/// in front of another line of a makefile that uses `eol`.
pub(crate) fn with_trailing_newline(node: &SyntaxNode, eol: &str) -> SyntaxNode {
    if foreign_line_breaks(node, eol).is_empty()
        && last_token(node).is_none_or(|t| t.kind() == NEWLINE)
    {
        return node.clone();
    }
    let copy = SyntaxNode::new_root_mut(node.green().into_owned());
    for token in foreign_line_breaks(&copy, eol) {
        let index = token.index();
        token
            .parent()
            .expect("tokens always have a parent")
            .splice_children(index..index + 1, detached_elements(&[(NEWLINE, eol)], None));
    }
    terminate_line_before(&copy, copy.children_with_tokens().count(), eol);
    copy
}

/// Whether `last`, the last token of a line without a line break, ends in
/// a backslash that would continue the line if one was added.
fn ends_in_continuation(last: &SyntaxToken) -> bool {
    let mut backslashes = 0;
    let mut token = Some(last.clone());
    while let Some(t) = token {
        let run = t.text().chars().rev().take_while(|c| *c == '\\').count();
        backslashes += run;
        if run < t.text().chars().count() {
            break;
        }
        token = t.prev_token();
    }
    backslashes % 2 == 1
}

/// Make sure the text before child `index` of `parent` ends in a line
/// break, so that a new line can be inserted there. If it doesn't, `eol` is
/// added where the parser would have put it. Returns the index to insert at,
/// which shifts if the line break was added to `parent` itself.
///
/// If the line ends in a backslash, a line break would continue it onto the
/// inserted line, so a blank line is added as well to end it. GNU make
/// reads a backslash at the very end of a file literally, so this changes
/// the value of e.g. `X = a \` at the end of a file from `a \` to `a `.
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
    if ends_in_continuation(&last) {
        // The line break continuing the line goes with the backslash, as
        // the parser puts it, and the blank line after it in the item.
        let mut container = last.parent().expect("token has a parent");
        // A backslash ending the file is read as part of a prerequisite,
        // but one before a line break continues the prerequisite list.
        if container.kind() == PREREQUISITE {
            let outer = container.parent().expect("prerequisite has a parent");
            let after = container.index() + 1;
            last.detach();
            outer.splice_children(after..after, vec![last.clone().into()]);
            if container.first_child_or_token().is_none() {
                container.detach();
            }
            container = outer;
        }
        if last.kind() == COMMENT {
            let comment = detached_elements(&[(COMMENT, &format!("{}{eol}", last.text()))], None);
            container.splice_children(last.index()..last.index() + 1, comment);
        } else {
            let after = last.index() + 1;
            container.splice_children(after..after, detached_elements(&[(NEWLINE, eol)], None));
        }
        return match prev {
            // A blank line after a command belongs to the rule.
            SyntaxElement::Node(node) if node.kind() != RECIPE => {
                let len = node.children_with_tokens().count();
                node.splice_children(len..len, newline);
                index
            }
            _ => {
                parent.splice_children(index..index, newline);
                index + 1
            }
        };
    }
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

/// The comment lines that document `node`, nearest first: the lines from
/// [`lines_above`] up to the first blank line. These are the whole-line
/// comments directly above `node`, indented or not, other than a shebang,
/// a trailing comment or a comment that continues the line before it.
pub(crate) fn doc_comment_lines(node: &SyntaxNode) -> Vec<LineAbove> {
    lines_above(node)
        .into_iter()
        .take_while(|line| line.comment.is_some())
        .collect()
}

/// The first token of the line of `node` or of the comment lines
/// documenting it, as found by [`doc_comment_lines`], if that is not the
/// first token of `node` itself.
fn doc_comment_start(node: &SyntaxNode) -> Option<SyntaxToken> {
    doc_comment_lines(node)
        .pop()
        .map(|line| line.tokens[0].clone())
        .or_else(|| line_indent(node))
}

/// Move the comment lines documenting `node` and its indentation into the
/// parent of `node`, out of the preceding item.
///
/// The parser puts comments that follow a recipe in the preceding rule, so
/// they need moving before anything can be inserted between them and the
/// end of that rule.
pub(crate) fn hoist_doc_comment(node: &SyntaxNode) {
    let parent = node.parent().expect("node must have a parent");
    let Some(start) = doc_comment_start(node) else {
        return;
    };
    let mut element = SyntaxElement::Token(start);
    loop {
        let container = element.parent().expect("element is below parent");
        if container == parent {
            return;
        }
        let index = element.index();
        let tail: Vec<_> = container.children_with_tokens().skip(index).collect();
        detach_elements(tail.iter().cloned());
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

/// The index in the parent of `node` before the start of its line and the
/// comment lines documenting it, so that anything inserted there goes
/// before them. The comment lines must have been moved into the parent of
/// `node` with [`hoist_doc_comment`].
pub(crate) fn index_before_doc_comment(node: &SyntaxNode) -> usize {
    let Some(start) = doc_comment_start(node) else {
        return node.index();
    };
    assert_eq!(
        start.parent(),
        node.parent(),
        "doc comment must be hoisted first"
    );
    start.index()
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
    // nmake does not take backslashes as escapes before a comment.
    if comments && before_comment && syntax != LineSyntax::NMake {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lossless::Makefile;
    use crate::SyntaxKind::{EXPR, OPERATOR};
    use rowan::ast::AstNode;

    #[test]
    fn test_detach_elements_mixed() {
        let makefile: Makefile = "X := a b # c\nall:\n".parse().unwrap();
        let variable = makefile.variable_definitions().next().unwrap();
        let elements: Vec<_> = variable
            .syntax()
            .children_with_tokens()
            .skip(1)
            .take_while(|e| e.kind() != COMMENT)
            .collect();
        assert_eq!(
            elements.iter().map(|e| e.kind()).collect::<Vec<_>>(),
            vec![WHITESPACE, OPERATOR, WHITESPACE, EXPR]
        );
        detach_elements(elements);
        assert_eq!(makefile.to_string(), "X# c\nall:\n");
        assert_eq!(variable.syntax().to_string(), "X# c\n");
    }

    #[test]
    fn test_replace_range() {
        let makefile: Makefile = "X := a b # c\nall:\n".parse().unwrap();
        let variable = makefile.variable_definitions().next().unwrap();
        let last = variable.syntax().last_token().unwrap();
        replace_range(
            variable.syntax(),
            1..5,
            detached_elements(&[(OPERATOR, "="), (WHITESPACE, " ")], None),
        );
        assert_eq!(makefile.to_string(), "X= # c\nall:\n");
        assert_eq!(last.parent().as_ref(), Some(variable.syntax()));
    }
}
