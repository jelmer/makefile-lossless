use crate::SyntaxKind;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::GreenNodeBuilder;
use std::str::FromStr;

mod error;
mod parser;
mod recipe;
mod text_references;
mod variable_reference;

#[cfg(test)]
mod test_continuation;
#[cfg(test)]
mod test_crlf;
#[cfg(test)]
mod test_nmake;
#[cfg(test)]
mod tests;

pub use error::*;
pub(crate) use parser::*;
pub use recipe::*;
pub(crate) use text_references::*;
pub use variable_reference::*;

/// these two SyntaxKind types, allowing for a nicer SyntaxNode API where
/// "kinds" are values from our `enum SyntaxKind`, instead of plain u16 values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lang {}
impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

/// To work with the parse results we need a view into the
/// green tree - the Syntax tree.
/// It is also immutable, like a GreenNode,
/// but it contains parent pointers, offsets, and
/// has identity semantics.
pub(crate) type SyntaxNode = rowan::SyntaxNode<Lang>;
#[allow(unused)]
pub(crate) type SyntaxToken = rowan::SyntaxToken<Lang>;
#[allow(unused)]
pub(crate) type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;

/// Offsets just past each newline in the text of `green`, in ascending order.
fn line_starts(green: &rowan::GreenNodeData) -> Vec<rowan::TextSize> {
    fn walk(
        node: &rowan::GreenNodeData,
        mut offset: rowan::TextSize,
        out: &mut Vec<rowan::TextSize>,
    ) {
        for child in node.children() {
            match child {
                rowan::NodeOrToken::Node(n) => walk(n, offset, out),
                rowan::NodeOrToken::Token(t) => {
                    out.extend(
                        t.text()
                            .match_indices('\n')
                            .map(|(idx, _)| offset + rowan::TextSize::from((idx + 1) as u32)),
                    );
                }
            }
            offset += child.text_len();
        }
    }
    let mut out = Vec::new();
    walk(green, 0.into(), &mut out);
    out
}

thread_local! {
    /// Line starts for the most recently queried tree.
    ///
    /// Green nodes are immutable and mutating a tree gives its root a new
    /// green node, so the root green node identifies the text. Holding on to
    /// it keeps its address from being reused by another tree.
    static LINE_STARTS_CACHE: std::cell::RefCell<Option<(rowan::GreenNode, Vec<rowan::TextSize>)>> =
        const { std::cell::RefCell::new(None) };
}

/// Calculate line and column (both 0-indexed) for the given offset in the tree.
/// Column is measured in bytes from the start of the line.
pub(crate) fn line_col_at_offset(node: &SyntaxNode, offset: rowan::TextSize) -> (usize, usize) {
    let root = node.ancestors().last().unwrap_or_else(|| node.clone());
    let green = root.green();
    LINE_STARTS_CACHE.with_borrow_mut(|cache| {
        let cached = matches!(cache, Some((cached_green, _))
            if std::ptr::eq::<rowan::GreenNodeData>(&**cached_green, &*green));
        if !cached {
            let starts = line_starts(&green);
            *cache = Some((green.into_owned(), starts));
        }
        let starts = &cache.as_ref().unwrap().1;
        let line = starts.partition_point(|&start| start <= offset);
        let line_start = match line {
            0 => rowan::TextSize::from(0),
            _ => starts[line - 1],
        };
        (line, (offset - line_start).into())
    })
}

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(Clone, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        /// An AST node for $ast
        pub struct $ast(SyntaxNode);

        impl AstNode for $ast {
            type Language = Lang;

            fn can_cast(kind: SyntaxKind) -> bool {
                kind == $kind
            }

            fn cast(syntax: SyntaxNode) -> Option<Self> {
                if Self::can_cast(syntax.kind()) {
                    Some(Self(syntax))
                } else {
                    None
                }
            }

            fn syntax(&self) -> &SyntaxNode {
                &self.0
            }
        }

        impl $ast {
            /// Get the source range of this node, including any trailing
            /// newline it owns.
            ///
            /// # Example
            /// ```
            /// use makefile_lossless::{Makefile, TextRange};
            ///
            /// let makefile: Makefile = "VAR = 1\nall:\n\techo hi\n".parse().unwrap();
            /// let rule = makefile.rules().next().unwrap();
            /// assert_eq!(rule.text_range(), TextRange::new(8.into(), 22.into()));
            /// ```
            pub fn text_range(&self) -> rowan::TextRange {
                self.0.text_range()
            }

            /// Get the line number (0-indexed) where this node starts.
            pub fn line(&self) -> usize {
                line_col_at_offset(&self.0, self.0.text_range().start()).0
            }

            /// Get the column number (0-indexed, in bytes) where this node starts.
            pub fn column(&self) -> usize {
                line_col_at_offset(&self.0, self.0.text_range().start()).1
            }

            /// Get both line and column (0-indexed) where this node starts.
            /// Returns (line, column) where column is measured in bytes from the start of the line.
            pub fn line_col(&self) -> (usize, usize) {
                line_col_at_offset(&self.0, self.0.text_range().start())
            }
        }

        impl core::fmt::Display for $ast {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                write!(f, "{}", self.0.text())
            }
        }
    };
}

ast_node!(Makefile, ROOT);

impl Makefile {
    /// Capture an independent snapshot of this makefile.
    ///
    /// The returned value shares the underlying immutable green-node data
    /// with `self` at the time of the call, but lives in its own mutable
    /// tree: subsequent mutations to `self` do not propagate to the snapshot.
    /// Pair with [`Self::tree_eq`] to detect later mutations.
    pub fn snapshot(&self) -> Self {
        Makefile(SyntaxNode::new_root_mut(self.0.green().into_owned()))
    }

    /// Returns true iff the syntax trees of `self` and `other` are
    /// value-equal. An O(1) pointer-identity fast path makes this free for
    /// trees that still share state with a recent `snapshot()`.
    pub fn tree_eq(&self, other: &Self) -> bool {
        let a = self.0.green();
        let b = other.0.green();
        let a_ref: &rowan::GreenNodeData = &a;
        let b_ref: &rowan::GreenNodeData = &b;
        std::ptr::eq(a_ref as *const _, b_ref as *const _) || a_ref == b_ref
    }

    /// The source ranges of the line continuations in this makefile: each
    /// backslash-newline that joins two lines, from the backslash up to
    /// and including the line ending.
    ///
    /// A backslash escaped by another one (`\\`) does not continue the
    /// line, nor does an nmake `^\`. Continuations are found in any
    /// context: in rule lines, assignments and directives, in recipes and
    /// comments, and in `define` bodies, where make keeps them in the
    /// value.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    ///
    /// let makefile: Makefile = "A = a \\\n  b\nall:\n\techo \\\\\n".parse().unwrap();
    /// assert_eq!(
    ///     makefile.line_continuations().collect::<Vec<_>>(),
    ///     vec![TextRange::new(6.into(), 8.into())]
    /// );
    /// ```
    pub fn line_continuations(&self) -> impl Iterator<Item = rowan::TextRange> + '_ {
        self.0
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .flat_map(|token| token_continuations(&token))
    }
}

/// The line continuations within or starting in `token`.
fn token_continuations(token: &SyntaxToken) -> Vec<rowan::TextRange> {
    let start = token.text_range().start();
    if token.kind() == BACKSLASH {
        if !crate::ast::is_continuation(&token.clone().into()) {
            return vec![];
        }
        let end = token
            .next_token()
            .expect("a continuation backslash is followed by a newline")
            .text_range()
            .end();
        return vec![rowan::TextRange::new(start, end)];
    }
    // An nmake `^\` escapes the backslash.
    if token.kind() == NEWLINE || token.text() == "^\\" {
        return vec![];
    }
    // Recipe text and comments hold the backslash, and comments also the
    // newline.
    let text = token.text();
    let odd_backslashes = |before: &str| {
        let before = before.strip_suffix('\r').unwrap_or(before);
        let n = before.len() - before.trim_end_matches('\\').len();
        (n % 2 == 1).then(|| before.len() - 1)
    };
    let offset = |i: usize| start + rowan::TextSize::from(i as u32);
    let mut ranges: Vec<_> = text
        .match_indices('\n')
        .filter_map(|(i, _)| {
            odd_backslashes(&text[..i])
                .map(|backslash| rowan::TextRange::new(offset(backslash), offset(i + 1)))
        })
        .collect();
    let newline = token.next_token().filter(|t| t.kind() == NEWLINE);
    if let (Some(newline), Some(backslash)) = (newline, odd_backslashes(text)) {
        ranges.push(rowan::TextRange::new(
            offset(backslash),
            newline.text_range().end(),
        ));
    }
    ranges
}

ast_node!(Rule, RULE);
ast_node!(Recipe, RECIPE);
ast_node!(Identifier, IDENTIFIER);
ast_node!(VariableDefinition, VARIABLE);
ast_node!(Include, INCLUDE);
ast_node!(Vpath, VPATH);
ast_node!(Load, LOAD);
ast_node!(ExpressionStatement, EXPRESSION_STATEMENT);
ast_node!(ArchiveMembers, ARCHIVE_MEMBERS);
ast_node!(ArchiveMember, ARCHIVE_MEMBER);
ast_node!(Conditional, CONDITIONAL);
ast_node!(ForLoop, FOR_LOOP);
ast_node!(Directive, DIRECTIVE);

/// Convert CRLF line endings in `text` to LF.
///
/// The lexer keeps CRLF line endings as single NEWLINE tokens so that files
/// round-trip losslessly; accessors use this so that the values they return
/// do not depend on the line endings of the file.
pub(crate) fn lf_line_endings(text: &str) -> String {
    text.replace("\r\n", "\n")
}

/// The comment that starts at `token`, a COMMENT token, if it starts one.
///
/// Where references are parsed in comments, in recipe lines and `define`
/// bodies, a comment is split into COMMENT tokens around the EXPR nodes of
/// the references, which all belong to the comment started by the first
/// token.
pub(crate) fn comment_elements(token: &SyntaxToken) -> Option<Vec<SyntaxElement>> {
    let continues = std::iter::successors(token.prev_sibling_or_token(), |it| {
        it.prev_sibling_or_token()
    })
    .find(|it| it.kind() != EXPR)
    .is_some_and(|it| it.kind() == COMMENT);
    if continues {
        return None;
    }
    Some(
        std::iter::successors(Some(SyntaxElement::Token(token.clone())), |it| {
            it.next_sibling_or_token()
        })
        .take_while(|it| matches!(it.kind(), COMMENT | EXPR))
        .collect(),
    )
}

/// The text of `node`, with CRLF line endings converted to LF.
pub(crate) fn node_text(node: &SyntaxNode) -> String {
    lf_line_endings(&node.text().to_string())
}

///
/// This removes trailing NEWLINE tokens from the end of a RULE node to avoid
/// extra blank lines at the end of a file when the last rule is removed.
/// Build detached tree elements for splicing into a mutable tree: the given
/// tokens, followed by a RECIPE node holding `recipe` if given.
pub(crate) fn detached_elements(
    tokens: &[(SyntaxKind, &str)],
    recipe: Option<rowan::GreenNode>,
) -> Vec<SyntaxElement> {
    let mut children: Vec<rowan::NodeOrToken<rowan::GreenNode, rowan::GreenToken>> = tokens
        .iter()
        .map(|(kind, text)| rowan::GreenToken::new((*kind).into(), text).into())
        .collect();
    children.extend(recipe.map(Into::into));
    let root = SyntaxNode::new_root_mut(rowan::GreenNode::new(ROOT.into(), children));
    let elements: Vec<_> = root.children_with_tokens().collect();
    for element in &elements {
        element.detach();
    }
    elements
}

pub(crate) fn trim_trailing_newlines(node: &SyntaxNode) {
    // Collect all trailing NEWLINE tokens at the end of the rule and within RECIPE nodes
    let mut newlines_to_remove = vec![];
    let mut current = node.last_child_or_token();

    while let Some(element) = current {
        match &element {
            rowan::NodeOrToken::Token(token) if token.kind() == NEWLINE => {
                newlines_to_remove.push(token.clone());
                current = token.prev_sibling_or_token();
            }
            rowan::NodeOrToken::Node(n) if n.kind() == RECIPE => {
                // Also check for trailing newlines in the RECIPE node
                let mut recipe_current = n.last_child_or_token();
                while let Some(recipe_element) = recipe_current {
                    match &recipe_element {
                        rowan::NodeOrToken::Token(token) if token.kind() == NEWLINE => {
                            newlines_to_remove.push(token.clone());
                            recipe_current = token.prev_sibling_or_token();
                        }
                        _ => break,
                    }
                }
                break; // Stop after checking the last RECIPE node
            }
            _ => break,
        }
    }

    // Remove all but one trailing newline (keep at least one)
    // Remove from highest index to lowest to avoid index shifts
    if newlines_to_remove.len() > 1 {
        // Sort by index descending
        newlines_to_remove.sort_by_key(|t| std::cmp::Reverse(t.index()));

        for token in newlines_to_remove.iter().take(newlines_to_remove.len() - 1) {
            let parent = token.parent().unwrap();
            let idx = token.index();
            parent.splice_children(idx..idx + 1, vec![]);
        }
    }
}

/// Helper function to remove a node along with its preceding comments and up to 1 empty line.
///
/// This walks backward from the node, removing:
/// - The node itself
/// - All preceding comments (COMMENT tokens)
/// - Up to 1 empty line (consecutive NEWLINE tokens)
/// - Any WHITESPACE tokens between these elements
pub(crate) fn remove_with_preceding_comments(node: &SyntaxNode, parent: &SyntaxNode) {
    let mut collected_elements = vec![];
    let mut found_comment = false;

    // Walk backward to collect preceding comments, newlines, and whitespace
    let mut current = node.prev_sibling_or_token();
    while let Some(element) = current {
        match &element {
            rowan::NodeOrToken::Token(token) => match token.kind() {
                COMMENT => {
                    if token.text().starts_with("#!") {
                        break; // Don't remove shebang lines
                    }
                    found_comment = true;
                    collected_elements.push(element.clone());
                }
                NEWLINE | WHITESPACE => {
                    collected_elements.push(element.clone());
                }
                _ => break, // Hit something else, stop
            },
            rowan::NodeOrToken::Node(n) => {
                // Handle BLANK_LINE nodes which wrap newlines
                if n.kind() == BLANK_LINE {
                    collected_elements.push(element.clone());
                } else {
                    break; // Hit another node type, stop
                }
            }
        }
        current = element.prev_sibling_or_token();
    }

    // Determine which preceding elements to remove
    // If we found comments, remove them along with up to 1 blank line
    let mut elements_to_remove = vec![];
    let mut consecutive_newlines = 0;
    for element in collected_elements.iter().rev() {
        let should_remove = match element {
            rowan::NodeOrToken::Token(token) => match token.kind() {
                COMMENT => {
                    consecutive_newlines = 0;
                    found_comment
                }
                NEWLINE => {
                    consecutive_newlines += 1;
                    found_comment && consecutive_newlines <= 1
                }
                WHITESPACE => found_comment,
                _ => false,
            },
            rowan::NodeOrToken::Node(n) => {
                // Handle BLANK_LINE nodes (count as newlines)
                if n.kind() == BLANK_LINE {
                    consecutive_newlines += 1;
                    found_comment && consecutive_newlines <= 1
                } else {
                    false
                }
            }
        };

        if should_remove {
            elements_to_remove.push(element.clone());
        }
    }

    // Remove elements in reverse order (from highest index to lowest) to avoid index shifts
    // Start with the node itself, then preceding elements
    let mut all_to_remove = vec![rowan::NodeOrToken::Node(node.clone())];
    all_to_remove.extend(elements_to_remove.into_iter().rev());

    // Sort by index in descending order
    all_to_remove.sort_by_key(|el| std::cmp::Reverse(el.index()));

    for element in all_to_remove {
        let idx = element.index();
        parent.splice_children(idx..idx + 1, vec![]);
    }
}

impl FromStr for Rule {
    type Err = crate::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Rule::parse(s).to_rule_result()
    }
}

impl FromStr for Makefile {
    type Err = crate::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Makefile::parse(s).to_result()
    }
}
