//! In-place editing of whitespace-separated lists of names, such as the
//! targets and prerequisites of a rule.

use super::is_continuation;
use crate::lossless::{Error, SyntaxElement, SyntaxNode};
use crate::SyntaxKind::{self, COMMENT, NEWLINE, OPERATOR, ROOT, WHITESPACE};
use rowan::{GreenNode, GreenToken, NodeOrToken};

pub(crate) type GreenElement = NodeOrToken<GreenNode, GreenToken>;

/// A child of the node holding a list: one that is already there, or a new
/// one to insert.
#[derive(Clone)]
pub(crate) enum Piece {
    Kept(SyntaxElement),
    New(GreenElement),
}

impl Piece {
    fn is(&self, kind: SyntaxKind) -> bool {
        match self {
            Piece::Kept(element) => element.kind() == kind,
            Piece::New(green) => green.kind() == kind.into(),
        }
    }
}

fn space() -> Vec<Piece> {
    vec![Piece::New(GreenToken::new(WHITESPACE.into(), " ").into())]
}

fn has_newline(separator: &[Piece]) -> bool {
    separator.iter().any(|p| p.is(NEWLINE))
}

/// A detached element for `green`.
fn detached(green: &GreenElement) -> SyntaxElement {
    match green {
        NodeOrToken::Node(node) => SyntaxNode::new_root_mut(node.clone()).into(),
        NodeOrToken::Token(token) => {
            let root =
                SyntaxNode::new_root_mut(GreenNode::new(ROOT.into(), [token.clone().into()]));
            let element = root
                .first_child_or_token()
                .expect("the root holds the token");
            element.detach();
            element
        }
    }
}

/// Make `node` hold `pieces`, which were taken from a node with the same
/// children as `node`, such as `node` itself or a copy of it: detach the
/// children that are not kept and insert the new ones between the others.
pub(crate) fn apply(pieces: &[Piece], node: &SyntaxNode) {
    let children: Vec<SyntaxElement> = node.children_with_tokens().collect();
    let mut keep = vec![false; children.len()];
    let pieces: Vec<Piece> = pieces
        .iter()
        .map(|piece| match piece {
            Piece::Kept(element) => {
                keep[element.index()] = true;
                Piece::Kept(children[element.index()].clone())
            }
            Piece::New(_) => piece.clone(),
        })
        .collect();
    for (child, keep) in children.iter().zip(keep) {
        if !keep {
            child.detach();
        }
    }
    let mut index = 0;
    for piece in pieces {
        match piece {
            Piece::Kept(child) => index = child.index() + 1,
            Piece::New(green) => {
                node.splice_children(index..index, vec![detached(&green)]);
                index += 1;
            }
        }
    }
}

struct Word {
    elements: Vec<Piece>,
    /// The position of the word in the original list, if it is kept as
    /// written.
    original: Option<usize>,
}

/// The children of a TARGETS or PREREQUISITES node, split into words and
/// the separators between them. The words end at a comment or at the `|`
/// before order-only prerequisites.
pub(crate) struct WordList {
    head: Vec<Piece>,
    words: Vec<Word>,
    /// The whitespace and line continuations between consecutive words.
    separators: Vec<Vec<Piece>>,
    tail: Vec<Piece>,
    original_len: usize,
}

impl WordList {
    pub(crate) fn new(node: &SyntaxNode) -> Self {
        let mut head = Vec::new();
        let mut words: Vec<Word> = Vec::new();
        let mut separators = Vec::new();
        let mut pending = Vec::new();
        let mut in_word = false;
        let mut children = node.children_with_tokens();
        for child in children.by_ref() {
            let is_bar =
                child.kind() == OPERATOR && child.as_token().is_some_and(|t| t.text() == "|");
            if child.kind() == COMMENT || is_bar {
                pending.push(Piece::Kept(child));
                break;
            }
            if child.kind() == WHITESPACE || is_continuation(&child) {
                in_word = false;
                pending.push(Piece::Kept(child));
                continue;
            }
            if !in_word {
                let before = std::mem::take(&mut pending);
                if words.is_empty() {
                    head = before;
                } else {
                    separators.push(before);
                }
                words.push(Word {
                    elements: Vec::new(),
                    original: Some(words.len()),
                });
                in_word = true;
            }
            words
                .last_mut()
                .expect("a word was started")
                .elements
                .push(Piece::Kept(child));
        }
        let mut tail = pending;
        tail.extend(children.map(Piece::Kept));
        let original_len = words.len();
        WordList {
            head,
            words,
            separators,
            tail,
            original_len,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.words.len()
    }

    /// Whether the last word is directly followed by a comment, so that
    /// trailing backslashes in it are halved.
    pub(crate) fn ends_before_comment(&self) -> bool {
        self.tail.first().is_some_and(|p| p.is(COMMENT))
    }

    pub(crate) fn replace(&mut self, index: usize, elements: Vec<GreenElement>) {
        self.words[index] = Word {
            elements: elements.into_iter().map(Piece::New).collect(),
            original: None,
        };
    }

    /// Remove the word at `index` with one of the separators next to it:
    /// the one after it, unless that continues the line and the one before
    /// it does not, or there is no word after it.
    pub(crate) fn remove(&mut self, index: usize) {
        let last = index + 1 == self.words.len();
        self.words.remove(index);
        if self.separators.is_empty() {
            return;
        }
        let before_is_plain = index > 0 && !has_newline(&self.separators[index - 1]);
        if last || before_is_plain && has_newline(&self.separators[index]) {
            self.separators.remove(index - 1);
        } else {
            self.separators.remove(index);
        }
    }

    /// Insert a word at `index`: on the line of the word before it, or
    /// before the first word.
    pub(crate) fn insert(&mut self, index: usize, elements: Vec<GreenElement>) {
        let word = Word {
            elements: elements.into_iter().map(Piece::New).collect(),
            original: None,
        };
        if self.words.is_empty() {
            self.words.push(word);
        } else if index == 0 {
            self.words.insert(0, word);
            self.separators.insert(0, space());
        } else {
            self.words.insert(index, word);
            self.separators.insert(index - 1, space());
        }
    }

    /// Change the list from `old`, the names of the words as read, to
    /// `new`. Words in the common prefix and suffix of the two lists are
    /// kept as written; the others are replaced, removed or inserted, using
    /// `build` to write a name, given whether it is directly followed by a
    /// comment.
    ///
    /// A kept word that ends up before a comment, or no longer is, is
    /// written again, since make reads trailing backslashes differently
    /// there.
    pub(crate) fn edit(
        &mut self,
        old: &[String],
        new: &[String],
        build: impl Fn(&str, bool) -> Result<Vec<GreenElement>, Error>,
    ) -> Result<(), Error> {
        assert_eq!(old.len(), self.words.len());
        let prefix = old.iter().zip(new).take_while(|(a, b)| a == b).count();
        let max_suffix = old.len().min(new.len()) - prefix;
        let suffix = old
            .iter()
            .rev()
            .zip(new.iter().rev())
            .take(max_suffix)
            .take_while(|(a, b)| a == b)
            .count();
        let old_middle = old.len() - suffix - prefix;
        let new_middle = new.len() - suffix - prefix;
        let common = old_middle.min(new_middle);
        let before_comment = self.ends_before_comment();
        let is_last = |i: usize| before_comment && i + 1 == new.len();
        for i in prefix..prefix + common {
            if old[i] != new[i] {
                self.replace(i, build(&new[i], is_last(i))?);
            }
        }
        for i in (prefix + common..prefix + old_middle).rev() {
            self.remove(i);
        }
        let inserted = prefix + common..prefix + new_middle;
        for (i, name) in new
            .iter()
            .enumerate()
            .take(inserted.end)
            .skip(inserted.start)
        {
            self.insert(i, build(name, is_last(i))?);
        }
        if before_comment {
            for (i, name) in new.iter().enumerate() {
                let Some(original) = self.words[i].original else {
                    continue;
                };
                if (original + 1 == self.original_len) != (i + 1 == new.len()) {
                    self.replace(i, build(name, is_last(i))?);
                }
            }
        }
        Ok(())
    }

    /// Remove the words at `indices`, in increasing order.
    pub(crate) fn remove_all(
        &mut self,
        indices: &[usize],
        old: &[String],
        build: impl Fn(&str, bool) -> Result<Vec<GreenElement>, Error>,
    ) -> Result<(), Error> {
        let new: Vec<String> = old
            .iter()
            .enumerate()
            .filter(|(i, _)| !indices.contains(i))
            .map(|(_, name)| name.clone())
            .collect();
        for &i in indices.iter().rev() {
            self.remove(i);
        }
        if self.ends_before_comment() {
            if let Some(last) = self.words.last() {
                if last.original.is_some_and(|o| o + 1 != self.original_len) {
                    let i = self.words.len() - 1;
                    self.replace(i, build(&new[i], true)?);
                }
            }
        }
        Ok(())
    }

    /// The children of the node holding the list, as edited.
    pub(crate) fn into_pieces(self) -> Vec<Piece> {
        let mut children = self.head;
        let mut separators = self.separators.into_iter();
        for (i, word) in self.words.into_iter().enumerate() {
            if i > 0 {
                children.extend(separators.next().expect("one separator per gap"));
            }
            children.extend(word.elements);
        }
        children.extend(self.tail);
        children
    }
}
