//! Variable references in text that make keeps as is when reading the
//! makefile, such as recipe lines.
//!
//! The lexer reads such text without looking for references. Here the
//! references are found the way make finds them when it expands the text,
//! and each becomes an EXPR node shaped like those of other references:
//! `$`, the opening delimiter, the contents as lexed on an ordinary line
//! (with nested references as EXPR nodes) and the closing delimiter. Only
//! the token boundaries change, so the text of the tree stays the same.

use super::Lang;
use crate::lex::lex_reference_text;
use crate::reference::{bsd_expr_extent_at, UnescapedHash};
use crate::MakefileVariant;
use crate::SyntaxKind::{self, *};
use rowan::Language;
use rowan::{GreenNode, GreenNodeBuilder, GreenNodeData, NodeOrToken};
use std::ops::Range;

#[derive(Debug, PartialEq, Eq)]
enum Shape {
    /// `$$`
    EscapedDollar,
    /// A single-character name, as in `$@` or `$X`.
    Single,
    /// `$(...)` or `${...}`
    Delimited,
}

/// How deeply references are nested at most. Deeper ones are left as text,
/// so that building and dropping the tree does not run out of stack.
const MAX_DEPTH: usize = 256;

#[derive(Debug)]
struct Reference {
    range: Range<usize>,
    shape: Shape,
    nested: Vec<Reference>,
}

/// Add `tokens` to `builder`, with each variable reference in them wrapped
/// in an EXPR node.
///
/// `tokens` are the children of a RECIPE node. An unterminated reference is
/// left as text, like make, which only reports it when expanding the text.
pub(crate) fn emit_with_references(
    builder: &mut GreenNodeBuilder<'_>,
    tokens: &[(SyntaxKind, &str)],
    variant: Option<MakefileVariant>,
) {
    let mut text = String::new();
    let mut starts = Vec::with_capacity(tokens.len() + 1);
    for (_, token) in tokens {
        starts.push(text.len());
        text.push_str(token);
    }
    starts.push(text.len());
    if !text.contains('$') {
        for (kind, token) in tokens {
            builder.token((*kind).into(), token);
        }
        return;
    }
    let references: Vec<_> = searched_regions(tokens, &starts, &text)
        .into_iter()
        .flat_map(|region| {
            Finder::new(&text, region.clone(), variant).find(region.start, region.end, 0)
        })
        .collect();
    let mut emitter = Emitter {
        builder,
        tokens,
        starts: &starts,
        text: &text,
        variant,
    };
    emitter.range(0, text.len(), &references, false);
}

/// Add the children of `node` to `builder` in a `node.kind()` node,
/// structuring references as by [`emit_with_references`] if they are all
/// tokens. Other nodes are added unchanged.
pub(crate) fn emit_node_with_references(
    builder: &mut GreenNodeBuilder<'_>,
    node: &GreenNodeData,
    variant: Option<MakefileVariant>,
) {
    builder.start_node(node.kind());
    let tokens: Option<Vec<(SyntaxKind, &str)>> = node
        .children()
        .map(|child| match child {
            NodeOrToken::Token(token) => Some((Lang::kind_from_raw(token.kind()), token.text())),
            NodeOrToken::Node(_) => None,
        })
        .collect();
    match tokens {
        Some(tokens) => emit_with_references(builder, &tokens, variant),
        None => {
            for child in node.children() {
                replay(builder, child);
            }
        }
    }
    builder.finish_node();
}

fn replay(
    builder: &mut GreenNodeBuilder<'_>,
    element: NodeOrToken<&GreenNodeData, &rowan::GreenTokenData>,
) {
    match element {
        NodeOrToken::Token(token) => builder.token(token.kind(), token.text()),
        NodeOrToken::Node(node) => {
            builder.start_node(node.kind());
            for child in node.children() {
                replay(builder, child);
            }
            builder.finish_node();
        }
    }
}

/// Build a RECIPE node holding `tokens`, with the references in them
/// structured. The variant is not known when editing a tree, so references
/// are found as GNU make finds them.
pub(crate) fn recipe_green(tokens: &[(SyntaxKind, &str)]) -> GreenNode {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(RECIPE.into());
    emit_with_references(&mut builder, tokens, None);
    builder.finish_node();
    builder.finish()
}

/// Whether the newline at `newline` in `text` ends a line continuation: it
/// follows an odd number of backslashes.
fn is_continued(text: &str, newline: usize) -> bool {
    let before = text[..newline]
        .strip_suffix('\r')
        .unwrap_or(&text[..newline]);
    (before.len() - before.trim_end_matches('\\').len()) % 2 == 1
}

/// The byte ranges of `text`, the text of a recipe line, to search for
/// references. A reference lies within one of them: it can only continue on
/// the next line after a line continuation, as GNU make joins those inside
/// references.
fn searched_regions(
    tokens: &[(SyntaxKind, &str)],
    starts: &[usize],
    text: &str,
) -> Vec<Range<usize>> {
    // Only text is searched: not comment lines, nor the `;` before a recipe
    // on the rule line.
    // TODO: make expands the text of a recipe line starting with `#` too,
    // before passing it to the shell; those are kept as COMMENT tokens.
    let mut regions: Vec<Range<usize>> = vec![];
    for ((kind, _), bounds) in tokens.iter().zip(starts.windows(2)) {
        if !matches!(kind, TEXT | NEWLINE | INDENT) {
            continue;
        }
        match regions.last_mut() {
            Some(last) if last.end == bounds[0] => last.end = bounds[1],
            _ => regions.push(bounds[0]..bounds[1]),
        }
    }
    // A reference does not continue past the end of a line, unless it is
    // continued.
    regions
        .into_iter()
        .flat_map(|region| {
            let mut pieces = vec![];
            let mut start = region.start;
            for (i, _) in text[region.clone()].match_indices('\n') {
                let newline = region.start + i;
                if !is_continued(text, newline) {
                    pieces.push(start..newline + 1);
                    start = newline + 1;
                }
            }
            pieces.push(start..region.end);
            pieces
        })
        .collect()
}

/// Finds the references in a region of the text.
struct Finder<'a> {
    text: &'a str,
    variant: Option<MakefileVariant>,
    /// The start of the region.
    base: usize,
    /// For each `(` or `{` in the region, by offset from `base`, the
    /// position of the matching delimiter of the same kind, if any.
    closes: Vec<Option<usize>>,
    /// For BSD make, the region as a line to find expressions in.
    bsd_line: Option<UnescapedHash>,
}

impl<'a> Finder<'a> {
    fn new(text: &'a str, region: Range<usize>, variant: Option<MakefileVariant>) -> Self {
        let mut closes = vec![None; region.len()];
        let (mut parens, mut braces) = (vec![], vec![]);
        for (i, b) in text[region.clone()].bytes().enumerate() {
            match b {
                b'(' => parens.push(i),
                b'{' => braces.push(i),
                b')' => {
                    if let Some(open) = parens.pop() {
                        closes[open] = Some(region.start + i);
                    }
                }
                b'}' => {
                    if let Some(open) = braces.pop() {
                        closes[open] = Some(region.start + i);
                    }
                }
                _ => {}
            }
        }
        let bsd_line = (variant == Some(MakefileVariant::BSDMake))
            .then(|| UnescapedHash::verbatim(&text[region.clone()]));
        Finder {
            text,
            variant,
            base: region.start,
            closes,
            bsd_line,
        }
    }

    /// Find the references in `text[lo..hi]`.
    fn find(&self, lo: usize, hi: usize, depth: usize) -> Vec<Reference> {
        if depth > MAX_DEPTH {
            return vec![];
        }
        let mut references = vec![];
        let mut i = lo;
        while let Some(found) = self.text[i..hi].find('$') {
            let start = i + found;
            i = start + 1;
            let Some(next) = self.text[start + 1..hi].chars().next() else {
                break;
            };
            let reference = match next {
                '$' => Reference {
                    range: start..start + 2,
                    shape: Shape::EscapedDollar,
                    nested: vec![],
                },
                '(' | '{' => {
                    let found = match &self.bsd_line {
                        Some(line) => self.bsd_reference(start, line, depth),
                        None => self.delimited_end(start, hi).map(|end| Reference {
                            range: start..end,
                            shape: Shape::Delimited,
                            nested: self.find(start + 2, end - 1, depth + 1),
                        }),
                    };
                    // Make reports an unterminated reference when expanding
                    // the text. Leave it as text, but look for references
                    // in it.
                    let Some(reference) = found else {
                        continue;
                    };
                    reference
                }
                // Like the parser, leave alone a `$` before a line
                // continuation, a line break or a closing delimiter, and in
                // BSD make, before a `:`.
                '\n' | '\r' | ')' | '}' => continue,
                '\\' if self.text[start + 2..hi].starts_with(['\n', '\r']) => continue,
                ':' if self.bsd_line.is_some() => continue,
                c => Reference {
                    range: start..start + 1 + c.len_utf8(),
                    shape: Shape::Single,
                    nested: vec![],
                },
            };
            i = reference.range.end;
            references.push(reference);
        }
        references
    }

    /// The end of the reference delimited by parentheses or braces at
    /// `start`, if it ends before `hi`. Like GNU make, count only the kind of
    /// delimiter that opens it.
    fn delimited_end(&self, start: usize, hi: usize) -> Option<usize> {
        let contents = start + 2;
        if self.variant == Some(MakefileVariant::NMake)
            && self.text.as_bytes()[start + 1] == b'('
            && self.at_nmake_substitution(contents)
        {
            // nmake's substitution strings can't invoke macros, so the
            // reference ends at the first `)`.
            return self.text[contents..hi].find(')').map(|i| contents + i + 1);
        }
        self.closes[start + 1 - self.base]
            .filter(|&close| close < hi)
            .map(|close| close + 1)
    }

    /// Whether the text at `contents` is an nmake macro substitution,
    /// `name:string1=string2`.
    fn at_nmake_substitution(&self, contents: usize) -> bool {
        let name = self.text[contents..]
            .bytes()
            .take_while(|b| !b"$():= \t\n".contains(b))
            .count();
        name > 0 && self.text[contents + name..].starts_with(':')
    }

    /// The BSD make expression at `start`, found in `line`, the region.
    fn bsd_reference(&self, start: usize, line: &UnescapedHash, depth: usize) -> Option<Reference> {
        let (len, nested) = bsd_expr_extent_at(line, start - self.base)?;
        let nested = nested
            .into_iter()
            .filter_map(|span| {
                let range = start + span.start..start + span.end;
                match self.text[range.start + 1..].chars().next()? {
                    '$' => Some(Reference {
                        range,
                        shape: Shape::EscapedDollar,
                        nested: vec![],
                    }),
                    '(' | '{' => {
                        if depth >= MAX_DEPTH {
                            return None;
                        }
                        let inner = self.bsd_reference(range.start, line, depth + 1)?;
                        (inner.range == range).then_some(inner)
                    }
                    _ => Some(Reference {
                        range,
                        shape: Shape::Single,
                        nested: vec![],
                    }),
                }
            })
            .collect();
        Some(Reference {
            range: start..start + len,
            shape: Shape::Delimited,
            nested,
        })
    }
}

struct Emitter<'a, 'b, 'c> {
    builder: &'a mut GreenNodeBuilder<'b>,
    tokens: &'c [(SyntaxKind, &'c str)],
    starts: &'c [usize],
    text: &'c str,
    variant: Option<MakefileVariant>,
}

impl Emitter<'_, '_, '_> {
    /// Add `text[lo..hi]`, which contains `references`.
    fn range(&mut self, lo: usize, hi: usize, references: &[Reference], inside: bool) {
        let mut pos = lo;
        for reference in references {
            self.plain(pos, reference.range.start, inside);
            self.reference(reference);
            pos = reference.range.end;
        }
        self.plain(pos, hi, inside);
    }

    fn reference(&mut self, reference: &Reference) {
        let Range { start, end } = reference.range;
        self.builder.start_node(EXPR.into());
        self.token(DOLLAR, start, start + 1);
        match reference.shape {
            Shape::EscapedDollar => self.token(DOLLAR, start + 1, end),
            Shape::Single => self.plain(start + 1, end, true),
            Shape::Delimited => {
                let (open, close) = if self.text.as_bytes()[start + 1] == b'(' {
                    (LPAREN, RPAREN)
                } else {
                    (LBRACE, RBRACE)
                };
                self.token(open, start + 1, start + 2);
                self.range(start + 2, end - 1, &reference.nested, true);
                self.token(close, end - 1, end);
            }
        }
        self.builder.finish_node();
    }

    fn token(&mut self, kind: SyntaxKind, start: usize, end: usize) {
        self.builder.token(kind.into(), &self.text[start..end]);
    }

    /// Add `text[lo..hi]`, which contains no references, keeping the
    /// original token boundaries. Inside a reference, the text is lexed as
    /// on an ordinary line, but the line structure tokens stay as they were
    /// and no new ones are added, so that the logical text of the tree does
    /// not change.
    fn plain(&mut self, lo: usize, hi: usize, inside: bool) {
        if lo >= hi {
            return;
        }
        let mut i = self.starts.partition_point(|&s| s <= lo) - 1;
        let mut pos = lo;
        while pos < hi {
            let end = self.starts[i + 1].min(hi);
            let kind = self.tokens[i].0;
            if !inside || matches!(kind, NEWLINE | INDENT | BACKSLASH) {
                self.token(kind, pos, end);
            } else {
                for (kind, text) in lex_reference_text(&self.text[pos..end], self.variant) {
                    let kind = match kind {
                        NEWLINE | INDENT | BACKSLASH | COMMENT => TEXT,
                        kind => kind,
                    };
                    self.builder.token(kind.into(), &text);
                }
            }
            pos = end;
            i += 1;
        }
    }
}
