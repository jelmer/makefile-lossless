use super::bsd::{keyword_range, keyword_token};
use super::makefile::MakefileItem;
use super::{
    line_ending, logical_text, terminate_line_before, text_before, with_recipe_prefix,
    with_trailing_newline, LineSyntax,
};
use crate::bsd_condition::{parse_bsd_condition, BsdCondition, BsdConditionError};
use crate::lossless::{
    invalid_edit, lf_line_endings, line_col_at_offset, remove_with_preceding_comments, Conditional,
    Error, InvalidEditKind, Lang, Recipe, Rule, VariableDefinition,
};
use crate::nmake_condition::{parse_nmake_condition, NmakeCondition, NmakeConditionError};
use crate::MakefileVariant;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::{Direction, GreenNodeBuilder, SyntaxNode};

/// Split `s` at the first top-level comma. A comma is "top-level" when it
/// is not inside a `$(...)` / `${...}` group. Returns `None` if no such
/// comma exists.
fn split_top_level_comma(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    let mut paren = 0usize;
    let mut brace = 0usize;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'$' if i + 1 < bytes.len() => {
                let next = bytes[i + 1];
                if next == b'(' {
                    paren += 1;
                    i += 2;
                    continue;
                }
                if next == b'{' {
                    brace += 1;
                    i += 2;
                    continue;
                }
                // $$ or $X — skip both.
                i += 2;
                continue;
            }
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b',' if paren == 0 && brace == 0 => {
                return Some((&s[..i], &s[i + 1..]));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Extract two quoted strings from `s`, in the form `"a" "b"` or `'a' 'b'`.
/// Returns `None` if fewer than two quoted strings are present. Surrounding
/// quote characters are stripped from each result.
fn quoted_pair(s: &str) -> Option<Vec<String>> {
    let mut out = Vec::new();
    let mut iter = s.chars().peekable();
    while iter.peek().is_some() {
        // Skip leading whitespace between args.
        while let Some(&c) = iter.peek() {
            if c.is_ascii_whitespace() {
                iter.next();
            } else {
                break;
            }
        }
        let opener = match iter.next() {
            Some(c @ ('"' | '\'')) => c,
            _ => break,
        };
        let mut buf = String::new();
        for c in iter.by_ref() {
            if c == opener {
                out.push(buf);
                break;
            }
            buf.push(c);
        }
    }
    if out.len() >= 2 {
        Some(out)
    } else {
        None
    }
}

/// An item in a branch of a [`Conditional`], in the body of a
/// [`Rule`](crate::Rule) or in the body of a [`ForLoop`](crate::ForLoop).
///
/// Conditionals that are part of a rule's recipe can contain recipe lines in
/// addition to ordinary makefile items.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ConditionalItem {
    /// A makefile item, such as a variable, rule or nested conditional
    Item(MakefileItem),
    /// A recipe line
    Recipe(Recipe),
}

impl ConditionalItem {
    pub(crate) fn cast(node: SyntaxNode<Lang>) -> Option<Self> {
        match Recipe::cast(node.clone()) {
            Some(recipe) => Some(Self::Recipe(recipe)),
            None => MakefileItem::cast(node).map(Self::Item),
        }
    }

    /// Get the underlying syntax node
    pub fn syntax(&self) -> &SyntaxNode<Lang> {
        match self {
            Self::Item(item) => item.syntax(),
            Self::Recipe(recipe) => recipe.syntax(),
        }
    }

    /// Get the range of this item in the source text.
    pub fn text_range(&self) -> rowan::TextRange {
        self.syntax().text_range()
    }

    /// The branches of the conditionals this item is in, outermost first;
    /// see [`MakefileItem::enclosing_branches`].
    pub fn enclosing_branches(&self) -> Vec<ConditionalBranch> {
        enclosing_branches(self.syntax())
    }

    /// Get the line number (0-indexed) where this item starts.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef A\nX = 1\n\nY = 2\nendif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let branch = cond.branches().next().unwrap();
    /// let lines: Vec<_> = branch.items().map(|item| item.line()).collect();
    /// assert_eq!(lines, vec![1, 3]);
    /// ```
    pub fn line(&self) -> usize {
        self.line_col().0
    }

    /// Get the column number (0-indexed, in bytes) where this item starts.
    pub fn column(&self) -> usize {
        self.line_col().1
    }

    /// Get both line and column (0-indexed) where this item starts.
    /// Returns (line, column) where column is measured in bytes from the start of the line.
    pub fn line_col(&self) -> (usize, usize) {
        let node = self.syntax();
        line_col_at_offset(node, node.text_range().start())
    }
}

/// A single branch of a [`Conditional`]: the initial `if`, an `else if`
/// (or BSD `.elif`) or the final plain `else`.
///
/// Obtained from [`Conditional::branches`].
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ConditionalBranch {
    /// The CONDITIONAL_IF or CONDITIONAL_ELSE node starting this branch.
    header: SyntaxNode<Lang>,
}

impl ConditionalBranch {
    /// The conditional directive that guards this branch, or `None` for a
    /// plain `else` / `.else`.
    ///
    /// For GNU make this is `ifdef`, `ifndef`, `ifeq` or `ifneq`, also for
    /// an `else ifeq` etc. branch. For BSD make it is the `.if` form of
    /// the directive including the leading dot, so `.elif` gives `.if` and
    /// `.elifdef` gives `.ifdef`, matching [`Conditional::conditional_type`].
    /// For nmake it is likewise the `!IF` form in upper case, so `!elseif`
    /// and `!ELSE IF` give `!IF` and `!ELSEIFDEF` gives `!IFDEF`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = ".if ${A}\n.elifndef B\n.else\n.endif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let types: Vec<_> = cond.branches().map(|b| b.conditional_type()).collect();
    /// assert_eq!(types, vec![Some(".if".to_string()), Some(".ifndef".to_string()), None]);
    ///
    /// let makefile = Makefile::parse_with_variant(
    ///     "!if 1\n!ELSE IFDEF A\n!ELSE\n!ENDIF\n",
    ///     MakefileVariant::NMake,
    /// )
    /// .tree();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let types: Vec<_> = cond.branches().map(|b| b.conditional_type()).collect();
    /// assert_eq!(types, vec![Some("!IF".to_string()), Some("!IFDEF".to_string()), None]);
    /// ```
    pub fn conditional_type(&self) -> Option<String> {
        let (token, keyword) = keyword_token(&self.header)?;
        if let Some(rest) = keyword.strip_prefix(".elif") {
            return Some(format!(".if{}", rest));
        }
        if let Some(rest) = keyword.strip_prefix("!ELSE") {
            if !rest.is_empty() {
                return Some(format!("!{}", rest));
            }
            // In `!ELSE IF ...` the directive is the next identifier.
            let directive = token
                .siblings_with_tokens(Direction::Next)
                .skip(1)
                .filter_map(|it| it.into_token())
                .find(|t| t.kind() != WHITESPACE)
                .filter(|t| t.kind() == IDENTIFIER)?;
            return Some(format!("!{}", directive.text().to_ascii_uppercase()));
        }
        match keyword.as_str() {
            "else" => {
                // In `else ifeq ...` the directive is the second identifier.
                let directive = self
                    .header
                    .children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .filter(|t| t.kind() == IDENTIFIER)
                    .nth(1)?;
                Some(directive.text().to_string())
            }
            ".else" => None,
            _ => Some(keyword),
        }
    }

    /// The source range of the directive keywords starting this branch.
    ///
    /// This covers both words of an `else ifeq` or nmake `!ELSE IF`
    /// header, and any leading dot or `!` with the whitespace after it, as
    /// in `.  elif`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "ifdef A\nelse ifeq (a,b)\nelse\nendif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let ranges: Vec<_> = cond.branches().map(|b| b.keyword_range()).collect();
    /// assert_eq!(
    ///     ranges,
    ///     vec![
    ///         Some(TextRange::new(0.into(), 5.into())),
    ///         Some(TextRange::new(8.into(), 17.into())),
    ///         Some(TextRange::new(24.into(), 28.into())),
    ///     ]
    /// );
    /// ```
    pub fn keyword_range(&self) -> Option<rowan::TextRange> {
        let (token, keyword) = keyword_token(&self.header)?;
        let range = keyword_range(&self.header)?;
        if !matches!(keyword.as_str(), "else" | "!ELSE") {
            return Some(range);
        }
        // The directive after `else`, if any. Other text after it is in an
        // ERROR node.
        let directive = token
            .siblings_with_tokens(Direction::Next)
            .skip(1)
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() != WHITESPACE)
            .filter(|t| t.kind() == IDENTIFIER);
        Some(directive.map_or(range, |t| range.cover(t.text_range())))
    }

    /// Whether this is a plain `else` / `.else` branch, taken when no
    /// earlier branch was.
    pub fn is_else(&self) -> bool {
        self.header.kind() == CONDITIONAL_ELSE && self.conditional_type().is_none()
    }

    /// The raw, unexpanded condition of this branch, or `None` for a plain
    /// `else`.
    ///
    /// For `ifdef` / `ifndef` this is the variable name, which is empty
    /// for a bare `ifdef` (GNU make treats that as undefined). For `ifeq` /
    /// `ifneq` it is the full argument text, e.g. `($(A),b)`; use
    /// [`Self::ifeq_args`] to get the two arguments.
    ///
    /// Line continuations are collapsed as BSD make does for `.if` and
    /// friends, nmake for `!IF` and friends and GNU make otherwise; see
    /// [`Self::condition_for`] for other variants. BSD make also unescapes
    /// `\#`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef A\nelse ifndef $(B)\nendif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let conditions: Vec<_> = cond.branches().map(|b| b.condition()).collect();
    /// assert_eq!(conditions, vec![Some("A".to_string()), Some("$(B)".to_string())]);
    /// ```
    pub fn condition(&self) -> Option<String> {
        let syntax = match keyword_token(&self.header).map(|(_, keyword)| keyword) {
            Some(keyword) if keyword.starts_with('.') => LineSyntax::Bsd,
            Some(keyword) if keyword.starts_with('!') => LineSyntax::NMake,
            _ => LineSyntax::Gnu,
        };
        self.condition_with(syntax)
    }

    /// The raw, unexpanded condition of this branch with line
    /// continuations collapsed as `variant` does, or `None` for a plain
    /// `else`.
    ///
    /// GNU make drops the whitespace before a line continuation, while
    /// POSIX make (and GNU make after `.POSIX:`) and BSD make keep it. This
    /// matters inside variable references, such as in function arguments
    /// or BSD make modifiers. BSD make also unescapes `\#`, which GNU make
    /// keeps in conditionals.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile = Makefile::parse_with_variant(
    ///     ".if ${A:S/a/b/ \\\n\t:S/c/d/} == x\n.endif\n",
    ///     MakefileVariant::BSDMake,
    /// )
    /// .tree();
    /// let branch = makefile.conditionals().next().unwrap().branches().next().unwrap();
    /// assert_eq!(
    ///     branch.condition_for(MakefileVariant::BSDMake),
    ///     Some("${A:S/a/b/  :S/c/d/} == x".to_string())
    /// );
    /// ```
    pub fn condition_for(&self, variant: MakefileVariant) -> Option<String> {
        self.condition_with(variant.into())
    }

    fn condition_with(&self, syntax: LineSyntax) -> Option<String> {
        let expr = self.header.children().find(|it| it.kind() == EXPR)?;
        let tokens = expr
            .descendants_with_tokens()
            .filter_map(|it| it.into_token());
        // GNU make does not unescape `\#` in conditionals.
        let comments = matches!(syntax, LineSyntax::Bsd | LineSyntax::NMake);
        Some(
            logical_text(&expr, tokens, syntax, comments)
                .trim()
                .to_string(),
        )
    }

    /// For an `ifeq` / `ifneq` branch, return the two argument strings
    /// (unexpanded). Supports both the `(a,b)` and `"a" "b"` (or
    /// `'a' 'b'`) syntaxes.
    ///
    /// Returns `None` for other directives (or if the args can't be
    /// recovered). Line continuations are collapsed as GNU make does; see
    /// [`Self::ifeq_args_for`] for other variants.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifeq ($(A),a)\nelse ifneq \"$(A)\" 'b'\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let args: Vec<_> = cond.branches().map(|b| b.ifeq_args()).collect();
    /// assert_eq!(
    ///     args,
    ///     vec![
    ///         Some(("$(A)".to_string(), "a".to_string())),
    ///         Some(("$(A)".to_string(), "b".to_string())),
    ///     ]
    /// );
    /// ```
    pub fn ifeq_args(&self) -> Option<(String, String)> {
        self.ifeq_args_with(LineSyntax::Gnu)
    }

    /// Like [`Self::ifeq_args`], but with line continuations collapsed as
    /// `variant` does; see [`Self::condition_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = "ifeq ($(subst a \\\n  b,c,a  b),c)\nendif\n".parse().unwrap();
    /// let branch = makefile.conditionals().next().unwrap().branches().next().unwrap();
    /// assert_eq!(
    ///     branch.ifeq_args_for(MakefileVariant::POSIXMake),
    ///     Some(("$(subst a  b,c,a  b)".to_string(), "c".to_string()))
    /// );
    /// ```
    pub fn ifeq_args_for(&self, variant: MakefileVariant) -> Option<(String, String)> {
        self.ifeq_args_with(variant.into())
    }

    fn ifeq_args_with(&self, syntax: LineSyntax) -> Option<(String, String)> {
        if !matches!(self.conditional_type()?.as_str(), "ifeq" | "ifneq") {
            return None;
        }
        let text = self.condition_with(syntax)?;
        // Form 1: parenthesised `(a, b)`. Split at the top-level comma,
        // ignoring commas inside nested `$(...)` / `${...}`.
        if let Some(inner) = text
            .strip_prefix('(')
            .and_then(|s| s.trim_end().strip_suffix(')'))
        {
            if let Some((a, b)) = split_top_level_comma(inner) {
                return Some((a.trim().to_string(), b.trim().to_string()));
            }
        }

        // Form 2: quoted `"a" "b"` or `'a' 'b'`.
        let mut parts = quoted_pair(&text)?;
        let b = parts.pop()?;
        let a = parts.pop()?;
        Some((a, b))
    }

    /// For a BSD make branch (`.if`, `.elif`, `.ifdef`, ...), parse its
    /// condition with [`parse_bsd_condition`], after collapsing line
    /// continuations as BSD make does.
    ///
    /// Returns `None` for GNU make conditionals and for a plain `.else`.
    /// How bare words and values in the condition evaluate depends on
    /// [`Self::conditional_type`]; see [`BsdCondition`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{BsdCondition, Makefile};
    /// let makefile: Makefile = ".ifndef A || B\n.elif ${C}\n.else\n.endif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let branches: Vec<_> = cond
    ///     .branches()
    ///     .map(|b| (b.conditional_type(), b.bsd_condition().transpose().unwrap()))
    ///     .collect();
    /// assert_eq!(
    ///     branches,
    ///     vec![
    ///         (
    ///             Some(".ifndef".to_string()),
    ///             Some(BsdCondition::Or(vec![
    ///                 BsdCondition::Bare("A".to_string()),
    ///                 BsdCondition::Bare("B".to_string()),
    ///             ]))
    ///         ),
    ///         (Some(".if".to_string()), Some("${C}".parse().unwrap())),
    ///         (None, None),
    ///     ]
    /// );
    /// ```
    pub fn bsd_condition(&self) -> Option<Result<BsdCondition, BsdConditionError>> {
        if !self.conditional_type()?.starts_with('.') {
            return None;
        }
        let condition = self.condition_with(LineSyntax::Bsd).unwrap_or_default();
        Some(parse_bsd_condition(&condition))
    }

    /// Parse the expression of an nmake `!IF` or `!ELSEIF` branch.
    ///
    /// Returns `None` for other directives, including nmake's `!IFDEF` and
    /// `!IFNDEF`, whose condition is a macro name.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant, NmakeBinaryOp, NmakeCondition};
    /// let makefile = Makefile::parse_with_variant(
    ///     "!IF $(VER) >= 5\n!ELSEIF DEFINED(OLD)\n!ELSE\n!ENDIF\n",
    ///     MakefileVariant::NMake,
    /// )
    /// .tree();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let conditions: Vec<_> = cond
    ///     .branches()
    ///     .map(|b| b.nmake_condition().transpose().unwrap())
    ///     .collect();
    /// assert_eq!(
    ///     conditions,
    ///     vec![
    ///         Some(NmakeCondition::Binary {
    ///             lhs: Box::new(NmakeCondition::Macro("$(VER)".to_string())),
    ///             op: NmakeBinaryOp::GreaterOrEqual,
    ///             rhs: Box::new(NmakeCondition::Integer(5)),
    ///         }),
    ///         Some(NmakeCondition::Defined("OLD".to_string())),
    ///         None,
    ///     ]
    /// );
    /// ```
    pub fn nmake_condition(&self) -> Option<Result<NmakeCondition, NmakeConditionError>> {
        if self.conditional_type()? != "!IF" {
            return None;
        }
        let condition = self.condition_with(LineSyntax::NMake).unwrap_or_default();
        Some(parse_nmake_condition(&condition))
    }

    /// The items in this branch in source order, including recipe lines
    /// and nested conditionals.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{ConditionalItem, Makefile, MakefileItem, RuleItem};
    /// let makefile: Makefile = "all:\nifdef V\n\techo verbose\nelse\n\t@echo quiet\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let Some(RuleItem::Conditional(cond)) = rule.items().next() else { panic!() };
    /// let recipes: Vec<Vec<String>> = cond
    ///     .branches()
    ///     .map(|b| {
    ///         b.items()
    ///             .map(|item| match item {
    ///                 ConditionalItem::Recipe(r) => r.text(),
    ///                 _ => panic!("expected recipe"),
    ///             })
    ///             .collect()
    ///     })
    ///     .collect();
    /// assert_eq!(recipes, vec![vec!["echo verbose"], vec!["@echo quiet"]]);
    /// ```
    pub fn items(&self) -> impl Iterator<Item = ConditionalItem> {
        self.header
            .siblings(Direction::Next)
            .skip(1)
            .take_while(|n| !matches!(n.kind(), CONDITIONAL_ELSE | CONDITIONAL_ENDIF))
            .filter_map(ConditionalItem::cast)
    }

    /// The line number (0-indexed) of the directive starting this branch.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef A\nX = 1\nelse\nX = 2\nendif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let lines: Vec<_> = cond.branches().map(|b| b.line()).collect();
    /// assert_eq!(lines, vec![0, 2]);
    /// ```
    pub fn line(&self) -> usize {
        line_col_at_offset(&self.header, self.header.text_range().start()).0
    }

    /// The conditional this branch belongs to.
    pub fn conditional(&self) -> Conditional {
        self.header
            .parent()
            .and_then(Conditional::cast)
            .expect("branch header is a child of a conditional")
    }

    /// The position of this branch in [`Conditional::branches`]: 0 for the
    /// initial `if`, then 1, 2, ... for each `else` branch.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef A\nelse ifdef B\nelse\nendif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let indexes: Vec<_> = cond.branches().map(|b| b.index()).collect();
    /// assert_eq!(indexes, vec![0, 1, 2]);
    /// ```
    pub fn index(&self) -> usize {
        self.header
            .siblings(Direction::Prev)
            .skip(1)
            .filter(|n| matches!(n.kind(), CONDITIONAL_IF | CONDITIONAL_ELSE))
            .count()
    }

    /// The range of this whole branch: its directive line and its body, up
    /// to the next `else` or `endif` directive.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "ifdef A\nX = 1\nelse\nX = 2\nendif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let ranges: Vec<_> = cond.branches().map(|b| b.text_range()).collect();
    /// assert_eq!(
    ///     ranges,
    ///     vec![TextRange::new(0.into(), 14.into()), TextRange::new(14.into(), 25.into())]
    /// );
    /// ```
    pub fn text_range(&self) -> rowan::TextRange {
        let start = self.header.text_range().start();
        let end = self
            .header
            .siblings_with_tokens(Direction::Next)
            .take_while(|n| {
                n.as_node() == Some(&self.header)
                    || !matches!(n.kind(), CONDITIONAL_ELSE | CONDITIONAL_ENDIF)
            })
            .last()
            .map_or(start, |n| n.text_range().end());
        rowan::TextRange::new(start, end)
    }

    /// The range of the directive line starting this branch, such as
    /// `ifdef A` or `else ifeq ($(B),1)`, without its line ending. A
    /// trailing comment on the line is included.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "ifdef A\nX = 1\nelse\nX = 2\nendif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let ranges: Vec<_> = cond.branches().map(|b| b.directive_range()).collect();
    /// assert_eq!(
    ///     ranges,
    ///     vec![TextRange::new(0.into(), 7.into()), TextRange::new(14.into(), 18.into())]
    /// );
    /// ```
    pub fn directive_range(&self) -> rowan::TextRange {
        let range = self.header.text_range();
        match self.header.last_token() {
            Some(token) if token.kind() == NEWLINE => {
                rowan::TextRange::new(range.start(), token.text_range().start())
            }
            _ => range,
        }
    }

    /// Whether this branch and `other` are different branches of the same
    /// conditional, so that make never takes both.
    ///
    /// Branches of different conditionals are never exclusive, even when
    /// their conditions contradict each other.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef A\na:\nelse\nb:\nendif\nifndef A\nc:\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let branches: Vec<_> = makefile.rules().map(|r| r.enclosing_branches()).collect();
    /// assert!(branches[0][0].is_exclusive_with(&branches[1][0]));
    /// assert!(!branches[0][0].is_exclusive_with(&branches[0][0]));
    /// assert!(!branches[0][0].is_exclusive_with(&branches[2][0]));
    /// ```
    pub fn is_exclusive_with(&self, other: &ConditionalBranch) -> bool {
        self.header != other.header && self.header.parent() == other.header.parent()
    }
}

impl std::fmt::Debug for ConditionalBranch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConditionalBranch")
            .field("index", &self.index())
            .field("range", &self.text_range())
            .finish()
    }
}

/// The branches of the conditionals enclosing `node`, outermost first.
pub(crate) fn enclosing_branches(node: &SyntaxNode<Lang>) -> Vec<ConditionalBranch> {
    let mut branches: Vec<_> = node
        .ancestors()
        .filter(|n| n.parent().is_some_and(|p| p.kind() == CONDITIONAL))
        .filter_map(|child| {
            child
                .siblings(Direction::Prev)
                .find(|n| matches!(n.kind(), CONDITIONAL_IF | CONDITIONAL_ELSE))
                .map(|header| ConditionalBranch { header })
        })
        .collect();
    branches.reverse();
    branches
}

impl Rule {
    /// The conditional branches this rule is in, outermost first; see
    /// [`MakefileItem::enclosing_branches`].
    pub fn enclosing_branches(&self) -> Vec<ConditionalBranch> {
        enclosing_branches(self.syntax())
    }
}

impl VariableDefinition {
    /// The conditional branches this variable definition is in, outermost
    /// first; see [`MakefileItem::enclosing_branches`].
    ///
    /// For a target-specific assignment this includes the branches the rule
    /// is in.
    pub fn enclosing_branches(&self) -> Vec<ConditionalBranch> {
        enclosing_branches(self.syntax())
    }
}

impl Recipe {
    /// The conditional branches this recipe line is in, outermost first;
    /// see [`MakefileItem::enclosing_branches`].
    ///
    /// This includes both conditionals in the rule body around the recipe
    /// line and conditionals around the rule.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef A\nall:\nifdef B\n\techo b\nendif\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let recipe = makefile.rules().next().unwrap().recipe_nodes().next().unwrap();
    /// let conditions: Vec<_> = recipe
    ///     .enclosing_branches()
    ///     .iter()
    ///     .map(|b| b.condition().unwrap())
    ///     .collect();
    /// assert_eq!(conditions, vec!["A", "B"]);
    /// ```
    pub fn enclosing_branches(&self) -> Vec<ConditionalBranch> {
        enclosing_branches(self.syntax())
    }
}

impl Conditional {
    /// Get the parent item of this conditional, if any
    ///
    /// Returns `Some(MakefileItem)` if this conditional has a parent that is a MakefileItem
    /// (e.g., another Conditional for nested conditionals), or `None` if the parent is the root Makefile node.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = r#"ifdef OUTER
    /// ifdef INNER
    /// VAR = value
    /// endif
    /// endif
    /// "#.parse().unwrap();
    ///
    /// let outer = makefile.conditionals().next().unwrap();
    /// let inner = outer.if_items().find_map(|item| {
    ///     if let makefile_lossless::MakefileItem::Conditional(c) = item {
    ///         Some(c)
    ///     } else {
    ///         None
    ///     }
    /// }).unwrap();
    /// // Inner conditional's parent is the outer conditional
    /// assert!(inner.parent().is_some());
    /// ```
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }

    /// The initial `if` branch of this conditional.
    fn if_branch(&self) -> Option<ConditionalBranch> {
        self.syntax()
            .children()
            .find(|it| it.kind() == CONDITIONAL_IF)
            .map(|header| ConditionalBranch { header })
    }

    /// Get the type of conditional (ifdef, ifndef, ifeq, ifneq)
    ///
    /// For BSD make conditionals this includes the leading dot, e.g. `.if`
    /// or `.ifdef`, regardless of any whitespace between the dot and the
    /// keyword. For nmake it is `!IF`, `!IFDEF` or `!IFNDEF`, in upper case
    /// regardless of how the directive is written.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile =
    ///     Makefile::parse_with_variant("!ifdef DEBUG\nX=1\n!endif\n", MakefileVariant::NMake)
    ///         .tree();
    /// let cond = makefile.conditionals().next().unwrap();
    /// assert_eq!(cond.conditional_type(), Some("!IFDEF".to_string()));
    /// assert_eq!(cond.condition(), Some("DEBUG".to_string()));
    /// ```
    pub fn conditional_type(&self) -> Option<String> {
        self.if_branch()?.conditional_type()
    }

    /// Add the tokens of the `else` or `endif` directive `name` to
    /// `builder`, in the style of this conditional: `.else` for BSD make,
    /// `!ELSE` for nmake.
    fn build_keyword(&self, builder: &mut GreenNodeBuilder, name: &str) {
        match self.conditional_type().and_then(|t| t.chars().next()) {
            Some('.') => builder.token(IDENTIFIER.into(), &format!(".{}", name)),
            Some('!') => {
                builder.token(OPERATOR.into(), "!");
                builder.token(IDENTIFIER.into(), &name.to_ascii_uppercase());
            }
            _ => builder.token(IDENTIFIER.into(), name),
        }
    }

    /// Get the condition expression of the initial branch; see
    /// [`ConditionalBranch::condition`].
    pub fn condition(&self) -> Option<String> {
        self.if_branch()?.condition()
    }

    /// Get the condition expression of the initial branch with line
    /// continuations collapsed as `variant` does; see
    /// [`ConditionalBranch::condition_for`].
    pub fn condition_for(&self, variant: MakefileVariant) -> Option<String> {
        self.if_branch()?.condition_for(variant)
    }

    /// For an `ifeq` / `ifneq` conditional, return the two argument
    /// strings (unexpanded). Supports both the `(a,b)` and `"a" "b"`
    /// (or `'a' 'b'`) syntaxes.
    ///
    /// Returns `None` for other conditional types (or if the args can't be
    /// recovered).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mf: Makefile = "ifeq ($(A),$(B))\nX = 1\nendif\n".parse().unwrap();
    /// let c = mf.conditionals().next().unwrap();
    /// assert_eq!(c.ifeq_args(), Some(("$(A)".to_string(), "$(B)".to_string())));
    /// ```
    pub fn ifeq_args(&self) -> Option<(String, String)> {
        self.if_branch()?.ifeq_args()
    }

    /// Like [`Self::ifeq_args`], but with line continuations collapsed as
    /// `variant` does; see [`ConditionalBranch::ifeq_args_for`].
    pub fn ifeq_args_for(&self, variant: MakefileVariant) -> Option<(String, String)> {
        self.if_branch()?.ifeq_args_for(variant)
    }

    /// For a BSD make conditional, parse the condition of its initial
    /// branch; see [`ConditionalBranch::bsd_condition`].
    pub fn bsd_condition(&self) -> Option<Result<BsdCondition, BsdConditionError>> {
        self.if_branch()?.bsd_condition()
    }

    /// The branches of this conditional in source order: the initial `if`,
    /// any `else ifeq`/`else ifdef`/... (or BSD `.elif*`) branches, and
    /// the final plain `else`, if present.
    ///
    /// Unlike [`Self::else_items`], which lumps together the items of all
    /// branches after the first, this gives access to the condition and
    /// items of each branch separately.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = r#"ifeq ($(OS),Linux)
    /// A = linux
    /// else ifdef WINDIR
    /// A = windows
    /// else
    /// A = other
    /// endif
    /// "#.parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let branches: Vec<_> = cond
    ///     .branches()
    ///     .map(|b| (b.conditional_type(), b.condition()))
    ///     .collect();
    /// assert_eq!(
    ///     branches,
    ///     vec![
    ///         (Some("ifeq".to_string()), Some("($(OS),Linux)".to_string())),
    ///         (Some("ifdef".to_string()), Some("WINDIR".to_string())),
    ///         (None, None),
    ///     ]
    /// );
    /// ```
    pub fn branches(&self) -> impl Iterator<Item = ConditionalBranch> + '_ {
        self.syntax()
            .children()
            .filter(|it| matches!(it.kind(), CONDITIONAL_IF | CONDITIONAL_ELSE))
            .map(|header| ConditionalBranch { header })
    }

    /// Whether this conditional is terminated by an `endif` (or `.endif`,
    /// `!ENDIF`). The parser accepts a conditional that runs to the end of
    /// the file without one.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef A\nX = 1\nendif\n".parse().unwrap();
    /// assert!(makefile.conditionals().next().unwrap().has_endif());
    /// let (makefile, _) = Makefile::from_str_relaxed("ifdef A\nX = 1\n");
    /// assert!(!makefile.conditionals().next().unwrap().has_endif());
    /// ```
    pub fn has_endif(&self) -> bool {
        self.syntax()
            .children()
            .any(|it| it.kind() == CONDITIONAL_ENDIF)
    }

    /// Check if this conditional has an else clause
    pub fn has_else(&self) -> bool {
        self.syntax()
            .children()
            .any(|it| it.kind() == CONDITIONAL_ELSE)
    }

    /// Get the body content of the if branch
    pub fn if_body(&self) -> Option<String> {
        let mut body = String::new();
        let mut in_if_body = false;

        for child in self.syntax().children_with_tokens() {
            if child.kind() == CONDITIONAL_IF {
                in_if_body = true;
                continue;
            }
            if child.kind() == CONDITIONAL_ELSE || child.kind() == CONDITIONAL_ENDIF {
                break;
            }
            if in_if_body {
                body.push_str(&lf_line_endings(&child.to_string()));
            }
        }

        if body.is_empty() {
            None
        } else {
            Some(body)
        }
    }

    /// The source range of the `endif` keyword closing this conditional,
    /// or `None` if it has none.
    ///
    /// Like [`ConditionalBranch::keyword_range`], this includes any leading
    /// dot or `!` with the whitespace after it, as in `.  endif`, but not
    /// a comment after the keyword.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "ifdef A\nendif # A\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// assert_eq!(cond.endif_range(), Some(TextRange::new(8.into(), 13.into())));
    /// ```
    pub fn endif_range(&self) -> Option<rowan::TextRange> {
        let endif = self
            .syntax()
            .children()
            .find(|it| it.kind() == CONDITIONAL_ENDIF)?;
        keyword_range(&endif)
    }

    /// Get the body content of the else branch (if it exists)
    pub fn else_body(&self) -> Option<String> {
        if !self.has_else() {
            return None;
        }

        let mut body = String::new();
        let mut in_else_body = false;

        for child in self.syntax().children_with_tokens() {
            if child.kind() == CONDITIONAL_ELSE {
                in_else_body = true;
                continue;
            }
            if child.kind() == CONDITIONAL_ENDIF {
                break;
            }
            if in_else_body {
                body.push_str(&lf_line_endings(&child.to_string()));
            }
        }

        if body.is_empty() {
            None
        } else {
            Some(body)
        }
    }

    /// Remove this conditional from the makefile
    ///
    /// This also removes the comment lines directly above it, with no blank line in between, as
    /// they document it. If that leaves a blank line above where it was
    /// followed by another blank line or the end of the file, the blank line
    /// above is removed too.
    pub fn remove(&mut self) -> Result<(), Error> {
        let Some(parent) = self.syntax().parent() else {
            return Err(invalid_edit(
                InvalidEditKind::Unsupported,
                "Conditional::remove",
                "Cannot remove conditional: no parent node",
            ));
        };

        remove_with_preceding_comments(self.syntax(), &parent);

        Ok(())
    }

    /// Remove the conditional directives (ifdef/endif) but keep the body content
    ///
    /// The conditional is replaced by the items of its if branch.
    /// Returns an error if the conditional has an else clause.
    ///
    /// # Errors
    ///
    /// Returns an [`Error::InvalidEdit`] of kind
    /// [`InvalidEditKind::Unsupported`] if the conditional has an else clause
    /// or is not part of a makefile.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = r#"ifdef DEBUG
    /// VAR = debug
    /// endif
    /// "#.parse().unwrap();
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// cond.replace_with_body().unwrap();
    /// // Now makefile contains just "VAR = debug\n"
    /// assert!(makefile.to_string().contains("VAR = debug"));
    /// assert!(!makefile.to_string().contains("ifdef"));
    /// ```
    pub fn replace_with_body(&mut self) -> Result<(), Error> {
        // Check if there's an else clause
        if self.has_else() {
            return Err(invalid_edit(
                InvalidEditKind::Unsupported,
                "Conditional::replace_with_body",
                "Cannot unwrap conditional with else clause",
            ));
        }

        let Some(parent) = self.syntax().parent() else {
            return Err(invalid_edit(
                InvalidEditKind::Unsupported,
                "Conditional::replace_with_body",
                "Cannot unwrap conditional: no parent node",
            ));
        };

        // Collect the body items (everything between CONDITIONAL_IF and CONDITIONAL_ENDIF)
        let body_nodes: Vec<_> = self
            .syntax()
            .children_with_tokens()
            .skip_while(|n| n.kind() != CONDITIONAL_IF)
            .skip(1) // Skip CONDITIONAL_IF itself
            .take_while(|n| n.kind() != CONDITIONAL_ENDIF)
            .collect();

        // Find the position of this conditional in parent
        let conditional_index = self.syntax().index();

        // Replace the entire conditional with just its body items
        parent.splice_children(conditional_index..conditional_index + 1, body_nodes);

        Ok(())
    }

    /// Remove the conditional directives (ifdef/endif) but keep the body content
    #[deprecated(since = "0.4.2", note = "use `replace_with_body` instead")]
    pub fn unwrap(&mut self) -> Result<(), Error> {
        self.replace_with_body()
    }

    /// Get all items (rules, variables, includes, nested conditionals) in the if branch
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = r#"ifdef DEBUG
    /// VAR = debug
    /// rule:
    /// 	command
    /// endif
    /// "#.parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let items: Vec<_> = cond.if_items().collect();
    /// assert_eq!(items.len(), 2); // One variable, one rule
    /// ```
    pub fn if_items(&self) -> impl Iterator<Item = MakefileItem> + '_ {
        self.syntax()
            .children()
            .skip_while(|n| n.kind() != CONDITIONAL_IF)
            .skip(1) // Skip the CONDITIONAL_IF itself
            .take_while(|n| n.kind() != CONDITIONAL_ELSE && n.kind() != CONDITIONAL_ENDIF)
            .filter_map(MakefileItem::cast)
    }

    /// Get all items (rules, variables, includes, nested conditionals) in the else branch
    ///
    /// For an `else ifeq ...` chain this includes the items of all branches
    /// after the first; use [`Self::branches`] to tell them apart.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = r#"ifdef DEBUG
    /// VAR = debug
    /// else
    /// VAR = release
    /// endif
    /// "#.parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let items: Vec<_> = cond.else_items().collect();
    /// assert_eq!(items.len(), 1); // One variable in else branch
    /// ```
    pub fn else_items(&self) -> impl Iterator<Item = MakefileItem> + '_ {
        self.syntax()
            .children()
            .skip_while(|n| n.kind() != CONDITIONAL_ELSE)
            .skip(1) // Skip the CONDITIONAL_ELSE itself
            .take_while(|n| n.kind() != CONDITIONAL_ENDIF)
            .filter_map(MakefileItem::cast)
    }

    /// Add an item to the if branch of the conditional
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let mut makefile: Makefile = "ifdef DEBUG\nendif\n".parse().unwrap();
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// let temp: Makefile = "CFLAGS = -g\n".parse().unwrap();
    /// let var = temp.variable_definitions().next().unwrap();
    /// cond.add_if_item(MakefileItem::Variable(var));
    /// assert!(makefile.to_string().contains("CFLAGS = -g"));
    /// ```
    pub fn add_if_item(&mut self, item: MakefileItem) {
        // Find position after CONDITIONAL_IF
        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|n| n.kind() == CONDITIONAL_IF)
            .map(|p| p + 1)
            .unwrap_or(0);

        let insert_pos =
            terminate_line_before(self.syntax(), insert_pos, &line_ending(self.syntax()));
        let item_node = with_recipe_prefix(item.syntax(), &text_before(self.syntax(), insert_pos));
        let item_node = with_trailing_newline(&item_node, &line_ending(self.syntax()));
        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![item_node.into()]);
    }

    /// Add an item to the start of the final plain `else` branch of the
    /// conditional
    ///
    /// If the conditional has no plain `else`, one is created before the
    /// `endif`; this includes an `else ifdef ...` chain that ends without
    /// one, since the items of an `else if` branch are conditional on that
    /// branch's condition.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let mut makefile: Makefile = "ifdef DEBUG\nVAR=1\nendif\n".parse().unwrap();
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// let temp: Makefile = "CFLAGS = -O2\n".parse().unwrap();
    /// let var = temp.variable_definitions().next().unwrap();
    /// cond.add_else_item(MakefileItem::Variable(var));
    /// assert!(makefile.to_string().contains("else"));
    /// assert!(makefile.to_string().contains("CFLAGS = -O2"));
    /// ```
    pub fn add_else_item(&mut self, item: MakefileItem) {
        let else_node = self.plain_else().unwrap_or_else(|| self.add_else_clause());
        let insert_pos = terminate_line_before(
            self.syntax(),
            else_node.index() + 1,
            &line_ending(self.syntax()),
        );
        let item_node = with_recipe_prefix(item.syntax(), &text_before(self.syntax(), insert_pos));
        let item_node = with_trailing_newline(&item_node, &line_ending(self.syntax()));
        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![item_node.into()]);
    }

    /// Add a matching `endif` to close this conditional, if it doesn't already
    /// have one.
    ///
    /// Returns `Ok(true)` if a CONDITIONAL_ENDIF was inserted, `Ok(false)` if
    /// the conditional was already terminated. Returns an error if the
    /// conditional has no recognized opener (e.g. a bare `else`/`endif` that
    /// the parser wrapped in a CONDITIONAL node).
    ///
    /// If the existing body does not end with a newline, one is inserted
    /// before the `endif` so it lands on its own line.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let (makefile, _) = Makefile::from_str_relaxed("ifdef DEBUG\nVAR = 1\n");
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// assert!(cond.add_endif().unwrap());
    /// assert_eq!(makefile.to_string(), "ifdef DEBUG\nVAR = 1\nendif\n");
    /// ```
    pub fn add_endif(&mut self) -> Result<bool, Error> {
        if self.conditional_type().is_none() {
            return Err(invalid_edit(
                InvalidEditKind::Unsupported,
                "Conditional::add_endif",
                "Cannot add endif to conditional with no opener",
            ));
        }
        if self.has_endif() {
            return Ok(false);
        }

        let eol = line_ending(self.syntax());
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(CONDITIONAL_ENDIF.into());
        self.build_keyword(&mut builder, "endif");
        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();

        let endif = SyntaxNode::new_root_mut(builder.finish());
        let count = terminate_line_before(
            self.syntax(),
            self.syntax().children_with_tokens().count(),
            &eol,
        );
        self.syntax()
            .splice_children(count..count, vec![endif.into()]);

        Ok(true)
    }

    /// The header of the final plain `else` branch, if the conditional has
    /// one.
    fn plain_else(&self) -> Option<SyntaxNode<Lang>> {
        let last = self
            .syntax()
            .children()
            .filter(|it| it.kind() == CONDITIONAL_ELSE)
            .last()?;
        ConditionalBranch {
            header: last.clone(),
        }
        .conditional_type()
        .is_none()
        .then_some(last)
    }

    /// Add a plain `else` before the `endif` and return its header.
    fn add_else_clause(&mut self) -> SyntaxNode<Lang> {
        let eol = line_ending(self.syntax());
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(CONDITIONAL_ELSE.into());
        self.build_keyword(&mut builder, "else");
        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        // Find position before CONDITIONAL_ENDIF
        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|n| n.kind() == CONDITIONAL_ENDIF)
            .unwrap_or(self.syntax().children_with_tokens().count());

        let insert_pos = terminate_line_before(self.syntax(), insert_pos, &eol);
        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![syntax.into()]);
        self.syntax()
            .children_with_tokens()
            .nth(insert_pos)
            .and_then(|it| it.into_node())
            .expect("else clause was just inserted")
    }
}

#[cfg(test)]
mod tests {

    use super::{ConditionalBranch, ConditionalItem};
    use crate::lossless::Makefile;
    use crate::test_util::{assert_matches_reparse, item_without_newline};
    use crate::{
        BsdComparisonOp, BsdCondition, BsdConditionError, BsdConditionErrorKind, BsdFunction,
        BsdOperand, MakefileItem, MakefileVariant, ParseErrorKind, RuleItem,
    };
    use rowan::ast::AstNode;

    #[test]
    fn test_nmake_condition() {
        let text = concat!(
            "!if \"$(CFG)\" == \"Debug\" || 1 ^^ \\\n  2\n",
            "!ELSE IF EXIST(a.c) # c\n",
            "!ELSEIFDEF X\n",
            "!ELSEIF (1\n",
            "!ENDIF\n",
        );
        let makefile = Makefile::parse_with_variant(text, MakefileVariant::NMake).tree();
        let cond = makefile.conditionals().next().unwrap();
        let conditions: Vec<_> = cond.branches().map(|b| b.nmake_condition()).collect();
        let [Some(Ok(first)), Some(Ok(second)), None, Some(Err(error))] = &conditions[..] else {
            panic!("{conditions:?}");
        };
        assert_eq!(
            first,
            &crate::parse_nmake_condition("\"$(CFG)\" == \"Debug\" || 1 ^ 2").unwrap()
        );
        assert_eq!(second, &crate::NmakeCondition::Exist("a.c".to_string()));
        assert_eq!(
            error.kind(),
            crate::NmakeConditionErrorKind::UnclosedParenthesis
        );

        let makefile: Makefile = ".if 1\n.endif\n".parse().unwrap();
        let branch = makefile.conditionals().next().unwrap().branches().next();
        assert_eq!(branch.unwrap().nmake_condition(), None);
    }

    #[test]
    fn test_conditional_item_line_col() {
        let text = "ifdef X\nVAR = 1\nall:\n\techo\n  ifdef Y\n  endif\nendif\n";
        let makefile: Makefile = text.parse().unwrap();
        assert_eq!(makefile.to_string(), text);
        let cond = makefile.conditionals().next().unwrap();
        let branch = cond.branches().next().unwrap();
        let items: Vec<_> = branch
            .items()
            .map(|item| {
                let kind = match item {
                    ConditionalItem::Item(MakefileItem::Variable(_)) => "variable",
                    ConditionalItem::Item(MakefileItem::Rule(_)) => "rule",
                    ConditionalItem::Item(MakefileItem::Conditional(_)) => "conditional",
                    ConditionalItem::Recipe(_) => "recipe",
                    _ => "other",
                };
                (kind, item.line(), item.column(), item.line_col())
            })
            .collect();
        assert_eq!(
            items,
            vec![
                ("variable", 1, 0, (1, 0)),
                ("rule", 2, 0, (2, 0)),
                ("conditional", 4, 2, (4, 2)),
            ]
        );
    }

    #[test]
    fn test_conditional_item_recipe_line_col() {
        let text = "all:\nifdef X\n\techo x\nendif\n";
        let makefile: Makefile = text.parse().unwrap();
        assert_eq!(makefile.to_string(), text);
        let rule = makefile.rules().next().unwrap();
        let Some(RuleItem::Conditional(cond)) = rule.items().next() else {
            panic!("expected conditional");
        };
        let branch = cond.branches().next().unwrap();
        let items: Vec<_> = branch
            .items()
            .map(|item| (matches!(item, ConditionalItem::Recipe(_)), item.line_col()))
            .collect();
        assert_eq!(items, vec![(true, (2, 0))]);
    }

    fn describe_item(item: ConditionalItem) -> String {
        match item {
            ConditionalItem::Recipe(r) => format!("recipe {}", r.text()),
            ConditionalItem::Item(MakefileItem::Variable(v)) => {
                format!("var {}={}", v.name().unwrap(), v.raw_value().unwrap())
            }
            ConditionalItem::Item(MakefileItem::Rule(r)) => {
                format!("rule {}", r.targets().collect::<Vec<_>>().join(" "))
            }
            ConditionalItem::Item(MakefileItem::Conditional(c)) => {
                format!("conditional {}", c.conditional_type().unwrap())
            }
            ConditionalItem::Item(_) => "other".to_string(),
        }
    }

    type BranchDescription = (Option<String>, Option<String>, usize, Vec<String>);

    fn describe(branch: ConditionalBranch) -> BranchDescription {
        (
            branch.conditional_type(),
            branch.condition(),
            branch.line(),
            branch.items().map(describe_item).collect(),
        )
    }

    fn branch(
        kind: Option<&str>,
        condition: Option<&str>,
        line: usize,
        items: &[&str],
    ) -> BranchDescription {
        (
            kind.map(str::to_string),
            condition.map(str::to_string),
            line,
            items.iter().map(|s| s.to_string()).collect(),
        )
    }

    fn rule_conditional(makefile: &Makefile) -> crate::Conditional {
        let rule = makefile.rules().next().unwrap();
        let cond = rule.items().find_map(|item| match item {
            RuleItem::Conditional(c) => Some(c),
            RuleItem::Recipe(_) => None,
        });
        cond.unwrap()
    }

    #[test]
    fn test_branches_single() {
        let makefile: Makefile = "ifdef A\nX = 1\nendif\n".parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![branch(Some("ifdef"), Some("A"), 0, &["var X=1"])]
        );
    }

    #[test]
    fn test_branches_else_ifdef_chain() {
        let makefile: Makefile =
            "ifdef A\nX = 1\nelse ifndef $(B)\nX = 2\nelse ifdef C\nelse\nX = 3\nY = 4\nendif\n"
                .parse()
                .unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some("ifdef"), Some("A"), 0, &["var X=1"]),
                branch(Some("ifndef"), Some("$(B)"), 2, &["var X=2"]),
                branch(Some("ifdef"), Some("C"), 4, &[]),
                branch(None, None, 5, &["var X=3", "var Y=4"]),
            ]
        );
        assert_eq!(
            cond.branches().map(|b| b.is_else()).collect::<Vec<_>>(),
            vec![false, false, false, true]
        );
    }

    #[test]
    fn test_branches_else_ifeq_chain() {
        let makefile: Makefile = "ifeq ($(A),a)\nX = 1\nelse ifneq ($(A), $(call f,b))\nX = 2\nelse ifeq \"$(A)\" 'c'\nX = 3\nendif\n"
            .parse()
            .unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some("ifeq"), Some("($(A),a)"), 0, &["var X=1"]),
                branch(Some("ifneq"), Some("($(A), $(call f,b))"), 2, &["var X=2"]),
                branch(Some("ifeq"), Some("\"$(A)\" 'c'"), 4, &["var X=3"]),
            ]
        );
        assert_eq!(
            cond.branches().map(|b| b.ifeq_args()).collect::<Vec<_>>(),
            vec![
                Some(("$(A)".to_string(), "a".to_string())),
                Some(("$(A)".to_string(), "$(call f,b)".to_string())),
                Some(("$(A)".to_string(), "c".to_string())),
            ]
        );
    }

    #[test]
    fn test_branches_crlf() {
        let src = "ifeq ($(A),\\\r\n  a)\r\nX = 1\r\nelse ifneq \"$(A)\" 'b'\r\nX = 2\r\nelse ifdef C\r\nelse\r\nX = 3\r\nendif\r\n";
        let makefile: Makefile = src.parse().unwrap();
        assert_eq!(makefile.to_string(), src);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some("ifeq"), Some("($(A), a)"), 0, &["var X=1"]),
                branch(Some("ifneq"), Some("\"$(A)\" 'b'"), 3, &["var X=2"]),
                branch(Some("ifdef"), Some("C"), 5, &[]),
                branch(None, None, 6, &["var X=3"]),
            ]
        );
        assert_eq!(
            cond.branches().map(|b| b.ifeq_args()).collect::<Vec<_>>(),
            vec![
                Some(("$(A)".to_string(), "a".to_string())),
                Some(("$(A)".to_string(), "b".to_string())),
                None,
                None,
            ]
        );
        assert_eq!(cond.condition(), Some("($(A), a)".to_string()));
    }

    #[test]
    fn test_branches_header_comments() {
        let code = "ifdef A # c\nX = 1\nelse ifeq (a,b) # c\nX = 2\nelse ifneq \"a\" 'b'# c\nX = 3\nelse # c\nX = 4\nendif # c\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some("ifdef"), Some("A"), 0, &["var X=1"]),
                branch(Some("ifeq"), Some("(a,b)"), 2, &["var X=2"]),
                branch(Some("ifneq"), Some("\"a\" 'b'"), 4, &["var X=3"]),
                branch(None, None, 6, &["var X=4"]),
            ]
        );
        assert_eq!(
            cond.branches().map(|b| b.ifeq_args()).collect::<Vec<_>>(),
            vec![
                None,
                Some(("a".to_string(), "b".to_string())),
                Some(("a".to_string(), "b".to_string())),
                None,
            ]
        );
    }

    #[test]
    fn test_ifeq_args_header_comment() {
        let code = "ifeq ($(A),a) # c\nX = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("($(A),a)".to_string()));
        assert_eq!(
            cond.ifeq_args(),
            Some(("$(A)".to_string(), "a".to_string()))
        );
    }

    #[test]
    fn test_ifdef_only_comment() {
        let code = "ifdef # c\nX = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![branch(Some("ifdef"), Some(""), 0, &["var X=1"])]
        );
    }

    fn error_summary(code: &str) -> Vec<(ParseErrorKind, usize, String)> {
        let parsed = Makefile::parse(code);
        assert_eq!(parsed.tree().to_string(), code);
        parsed
            .errors()
            .iter()
            .map(|e| (e.kind(), e.line, e.message.clone()))
            .collect()
    }

    #[test]
    fn test_ifdef_extra_words() {
        let msg = "invalid syntax in conditional: expected a single variable name".to_string();
        assert_eq!(
            error_summary("ifdef FOO bar\nX = 1\nendif\n"),
            vec![(ParseErrorKind::InvalidConditional, 1, msg.clone())]
        );
        assert_eq!(
            error_summary("ifndef FOO\tbar # c\nendif\n"),
            vec![(ParseErrorKind::InvalidConditional, 1, msg.clone())]
        );
        // Reported on the physical line of the extra word.
        assert_eq!(
            error_summary("ifdef FOO \\\n  bar\nendif\n"),
            vec![(ParseErrorKind::InvalidConditional, 2, msg.clone())]
        );
        // Even if A expands to nothing, make sees " b" and rejects it.
        assert_eq!(
            error_summary("ifdef $(A) b\nendif\n"),
            vec![(ParseErrorKind::InvalidConditional, 1, msg.clone())]
        );
        assert_eq!(
            error_summary("ifeq (a,b)\nelse ifdef FOO bar\nendif\n"),
            vec![(ParseErrorKind::InvalidConditional, 2, msg)]
        );
    }

    #[test]
    fn test_ifdef_extra_words_condition() {
        let makefile = Makefile::parse("ifdef FOO bar\nX = 1\nendif\n").tree();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![branch(Some("ifdef"), Some("FOO bar"), 0, &["var X=1"])]
        );
    }

    #[test]
    fn test_ifdef_single_word() {
        // Whether these are valid depends on what the references expand
        // to, which is for the evaluator to check.
        for code in [
            "ifdef FOO   \nendif\n",
            "ifdef FOO # c\nendif\n",
            "ifdef $(A)\nendif\n",
            "ifdef $(A)b\nendif\n",
            "ifdef FOO $(B)\nendif\n",
            "ifdef $(A) ${B}\nendif\n",
            "ifdef FOO \\\n\nendif\n",
        ] {
            assert_eq!(error_summary(code), vec![], "{code:?}");
        }
    }

    #[test]
    fn test_bsd_ifdef_expression() {
        let code = ".ifdef A && B\nX = 1\n.endif\n";
        let parsed = Makefile::parse_with_variant(code, MakefileVariant::BSDMake);
        assert_eq!(parsed.errors(), &[]);
        assert_eq!(parsed.tree().to_string(), code);
    }

    #[test]
    fn test_empty_ifdef() {
        let code = "ifdef\nX = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("".to_string()));
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![branch(Some("ifdef"), Some(""), 0, &["var X=1"])]
        );
    }

    #[test]
    fn test_empty_ifndef() {
        let code = "ifndef \nX = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![branch(Some("ifndef"), Some(""), 0, &["var X=1"])]
        );
    }

    #[test]
    fn test_empty_else_ifdef() {
        let code = "ifdef A\nX = 1\nelse ifdef\nX = 2\nelse ifndef # c\nX = 3\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some("ifdef"), Some("A"), 0, &["var X=1"]),
                branch(Some("ifdef"), Some(""), 2, &["var X=2"]),
                branch(Some("ifndef"), Some(""), 4, &["var X=3"]),
            ]
        );
    }

    #[test]
    fn test_bsd_branches_header_comments() {
        let code = ".if A # c\nX = 1\n.elif ${B} == b # c\nX = 2\n.else # c\nX = 3\n.endif # c\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some(".if"), Some("A"), 0, &["var X=1"]),
                branch(Some(".if"), Some("${B} == b"), 2, &["var X=2"]),
                branch(None, None, 4, &["var X=3"]),
            ]
        );
        assert_eq!(
            cond.branches()
                .map(|b| b.bsd_condition())
                .collect::<Vec<_>>(),
            vec![
                Some(Ok(BsdCondition::Bare("A".to_string()))),
                Some(Ok(BsdCondition::Compare {
                    lhs: BsdOperand::VariableReference("${B}".to_string()),
                    op: BsdComparisonOp::Equal,
                    rhs: BsdOperand::Word("b".to_string()),
                })),
                None,
            ]
        );
    }

    #[test]
    fn test_branch_ifeq_args_other_directives() {
        let makefile: Makefile = "ifdef A\nelse\nendif\n".parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(|b| b.ifeq_args()).collect::<Vec<_>>(),
            vec![None, None]
        );
    }

    #[test]
    fn test_ifeq_args_bsd_conditional() {
        let makefile: Makefile = ".if \"a\" == \"b\"\n.endif\n".parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.ifeq_args(), None);
    }

    #[test]
    fn test_bsd_condition() {
        let makefile: Makefile = ".if defined(A) && \\\n    ${B} == \"b\" # comment\n.elifmake install\n.elif ${C} ==\n.else\n.endif\n"
            .parse()
            .unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches()
                .map(|b| b.bsd_condition())
                .collect::<Vec<_>>(),
            vec![
                Some(Ok(BsdCondition::And(vec![
                    BsdCondition::Call {
                        function: BsdFunction::Defined,
                        argument: "A".to_string(),
                    },
                    BsdCondition::Compare {
                        lhs: BsdOperand::VariableReference("${B}".to_string()),
                        op: BsdComparisonOp::Equal,
                        rhs: BsdOperand::String("b".to_string()),
                    },
                ]))),
                Some(Ok(BsdCondition::Bare("install".to_string()))),
                Some(Err(BsdConditionError {
                    message: "missing right-hand side of operator \"==\"".to_string(),
                    offset: 7,
                    kind: BsdConditionErrorKind::MissingRightHandSide,
                })),
                None,
            ]
        );
        assert_eq!(
            cond.bsd_condition(),
            cond.branches().next().unwrap().bsd_condition()
        );
    }

    #[test]
    fn test_bsd_condition_gnu_conditional() {
        let makefile: Makefile = "ifdef A\nelse ifeq ($(B),b)\nelse\nendif\n"
            .parse()
            .unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.bsd_condition(), None);
        assert_eq!(
            cond.branches()
                .map(|b| b.bsd_condition())
                .collect::<Vec<_>>(),
            vec![None, None, None]
        );
    }

    #[test]
    fn test_bsd_condition_missing() {
        let parsed = Makefile::parse(".if\n.endif\n");
        let cond = parsed.tree().conditionals().next().unwrap();
        assert_eq!(
            cond.bsd_condition(),
            Some(Err(BsdConditionError {
                message: "missing operand".to_string(),
                offset: 0,
                kind: BsdConditionErrorKind::MissingOperand,
            }))
        );
    }

    #[test]
    fn test_branches_nested() {
        let makefile: Makefile =
            "ifdef A\nifeq ($(B),b)\nX = 1\nelse\nX = 2\nendif\nY = 3\nelse ifdef C\nZ = 4\nendif\n"
                .parse()
                .unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(
                    Some("ifdef"),
                    Some("A"),
                    0,
                    &["conditional ifeq", "var Y=3"]
                ),
                branch(Some("ifdef"), Some("C"), 7, &["var Z=4"]),
            ]
        );
        let Some(ConditionalItem::Item(MakefileItem::Conditional(inner))) =
            cond.branches().next().unwrap().items().next()
        else {
            panic!("expected nested conditional");
        };
        assert_eq!(
            inner.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some("ifeq"), Some("($(B),b)"), 1, &["var X=1"]),
                branch(None, None, 3, &["var X=2"]),
            ]
        );
    }

    #[test]
    fn test_branches_recipes_in_rule() {
        let makefile: Makefile =
            "all:\n\techo start\nifdef V\n\techo verbose\nelse ifeq ($(Q),1)\nelse\n\t@echo quiet\n\t@true\nendif\n\techo end\n"
                .parse()
                .unwrap();
        let cond = rule_conditional(&makefile);
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some("ifdef"), Some("V"), 2, &["recipe echo verbose"]),
                branch(Some("ifeq"), Some("($(Q),1)"), 4, &[]),
                branch(None, None, 5, &["recipe @echo quiet", "recipe @true"]),
            ]
        );
    }

    #[test]
    fn test_branches_nested_recipes_in_rule() {
        let makefile: Makefile = "all:\nifdef A\nifdef B\n\techo ab\nendif\n\techo a\nendif\n"
            .parse()
            .unwrap();
        let cond = rule_conditional(&makefile);
        let items: Vec<_> = cond.branches().next().unwrap().items().collect();
        assert_eq!(
            items.iter().cloned().map(describe_item).collect::<Vec<_>>(),
            vec!["conditional ifdef", "recipe echo a"]
        );
        let ConditionalItem::Item(MakefileItem::Conditional(inner)) = &items[0] else {
            panic!("expected nested conditional");
        };
        assert_eq!(
            inner.branches().map(describe).collect::<Vec<_>>(),
            vec![branch(Some("ifdef"), Some("B"), 2, &["recipe echo ab"])]
        );
    }

    #[test]
    fn test_branches_mixing_recipes_and_variables_after_rule() {
        let makefile: Makefile = "t:\n\techo a\nifdef X\n\techo b\nQ = 1\nelse\nR = 2\nendif\n"
            .parse()
            .unwrap();
        let cond = rule_conditional(&makefile);
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some("ifdef"), Some("X"), 2, &["recipe echo b", "var Q=1"]),
                branch(None, None, 5, &["var R=2"]),
            ]
        );
    }

    #[test]
    fn test_branches_bsd() {
        let parsed = Makefile::parse_with_variant(
            ".if ${A} == \"a\" # comment\nX=1\n.elif defined(B)\nX=2\n.  elifndef C\n.  if 1\n.  endif\n.elifmake all\n.else\nX=3\n.endif\n",
            MakefileVariant::BSDMake,
        );
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some(".if"), Some("${A} == \"a\""), 0, &["var X=1"]),
                branch(Some(".if"), Some("defined(B)"), 2, &["var X=2"]),
                branch(Some(".ifndef"), Some("C"), 4, &["conditional .if"]),
                branch(Some(".ifmake"), Some("all"), 7, &[]),
                branch(None, None, 8, &["var X=3"]),
            ]
        );
        assert_eq!(
            cond.branches().map(|b| b.is_else()).collect::<Vec<_>>(),
            vec![false, false, false, false, true]
        );
    }

    #[test]
    fn test_branches_bsd_recipes_in_rule() {
        let parsed = Makefile::parse_with_variant(
            "t:\n.if defined(A)\n\techo a\n.elif defined(B)\n\techo b\n.else\n\techo c\n.endif\n",
            MakefileVariant::BSDMake,
        );
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        let cond = rule_conditional(&makefile);
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![
                branch(Some(".if"), Some("defined(A)"), 1, &["recipe echo a"]),
                branch(Some(".if"), Some("defined(B)"), 3, &["recipe echo b"]),
                branch(None, None, 5, &["recipe echo c"]),
            ]
        );
    }

    #[test]
    fn test_conditional_parent() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
endif
"#
        .parse()
        .unwrap();

        let cond = makefile.conditionals().next().unwrap();
        let parent = cond.parent();
        // Parent is ROOT node which doesn't cast to MakefileItem
        assert!(parent.is_none());
    }

    #[test]
    fn test_add_endif_to_unterminated() {
        let (makefile, _) = Makefile::from_str_relaxed("ifdef DEBUG\nVAR = 1\n");
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.to_string(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_already_terminated_noop() {
        let makefile: Makefile = "ifdef DEBUG\nVAR = 1\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(!cond.add_endif().unwrap());
        assert_eq!(makefile.to_string(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_no_trailing_newline() {
        // Source with no final newline produces a parse error, but the tree
        // is still usable for mutations.
        let parsed = Makefile::parse("ifdef DEBUG\nVAR = 1");
        let makefile = parsed.tree();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.to_string(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_with_else() {
        let (makefile, _) = Makefile::from_str_relaxed("ifdef DEBUG\nA = 1\nelse\nA = 2\n");
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(
            makefile.to_string(),
            "ifdef DEBUG\nA = 1\nelse\nA = 2\nendif\n"
        );
    }

    #[test]
    fn test_add_endif_rejects_bare_else() {
        // A bare `else`/`endif` is wrapped in a Conditional node with no
        // CONDITIONAL_IF, so conditional_type() is None. We refuse to add
        // an `endif` to it — the parser already complains.
        let parsed = Makefile::parse("else\nVAR = 1\n");
        let makefile = parsed.tree();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.conditional_type().is_none());
        assert!(cond.add_endif().is_err());
    }

    #[test]
    fn test_add_endif_preserves_existing_body() {
        let (makefile, _) = Makefile::from_str_relaxed("ifeq ($(X),y)\nA = 1\nB = 2\n");
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.to_string(), "ifeq ($(X),y)\nA = 1\nB = 2\nendif\n");
    }

    #[test]
    fn test_ifdef_line_continuation() {
        let code = "ifdef \\\n  X\nA = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        assert_eq!(makefile.rules().count(), 0);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("X".to_string()));
        assert_eq!(cond.if_items().count(), 1);
    }

    #[test]
    fn test_ifeq_quoted_line_continuation() {
        let code = "ifeq \"a\" \\\n  \"b\"\nA = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("\"a\" \"b\"".to_string()));
        assert_eq!(cond.ifeq_args(), Some(("a".to_string(), "b".to_string())));
        assert_eq!(cond.if_items().count(), 1);
    }

    #[test]
    fn test_ifeq_line_continuation_in_quotes() {
        let code = "ifeq \"a \\\n   b\" \"a b\"\nA = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("\"a b\" \"a b\"".to_string()));
        assert_eq!(
            cond.ifeq_args(),
            Some(("a b".to_string(), "a b".to_string()))
        );
    }

    #[test]
    fn test_ifeq_quoted_reference() {
        let code = "ifeq \"$(A)\" '${B}'\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.ifeq_args(),
            Some(("$(A)".to_string(), "${B}".to_string()))
        );
        let names: Vec<_> = makefile
            .variable_references()
            .filter_map(|r| r.name())
            .collect();
        assert_eq!(names, vec!["A".to_string(), "B".to_string()]);
    }

    #[test]
    fn test_ifeq_quote_inside_reference() {
        // GNU make finds the closing quote before expanding the argument,
        // so a quote inside a reference ends it, leaving the reference
        // unterminated.
        use crate::ParseErrorKind::{ExtraneousText, InvalidConditional, UnclosedReference};
        for (code, errors) in [
            (
                "ifeq \"$(subst \",x,a)\" \"a\"\nendif\n",
                vec![UnclosedReference, InvalidConditional],
            ),
            (
                "ifeq '$(subst ',x,a)' 'a'\nendif\n",
                vec![UnclosedReference, InvalidConditional],
            ),
            (
                "ifeq \"${X\"}\" \"a\"\nendif\n",
                vec![UnclosedReference, InvalidConditional],
            ),
            ("ifeq \"a\" \"$(X\"\nendif\n", vec![UnclosedReference]),
            (
                "ifeq \"a\" \"$(f $(X \")\"\nendif\n",
                vec![UnclosedReference, UnclosedReference, ExtraneousText],
            ),
        ] {
            let parsed = Makefile::parse(code);
            assert_eq!(parsed.tree().to_string(), code);
            assert_eq!(
                parsed.errors().iter().map(|e| e.kind()).collect::<Vec<_>>(),
                errors,
                "{code:?}"
            );
        }
        let makefile = Makefile::parse("ifeq \"a\" \"$(X\"\nendif\n").tree();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.ifeq_args(), Some(("a".to_string(), "$(X".to_string())));
        // A quote of the other kind does not end the argument.
        let code = "ifeq \"$(X')\" 'a'\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.ifeq_args(),
            Some(("$(X')".to_string(), "a".to_string()))
        );
        // Nor is `$\"` a reference to a variable named `"`.
        let code = "ifeq \"a$\" \"a\"\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.ifeq_args(), Some(("a$".to_string(), "a".to_string())));
    }

    #[test]
    fn test_ifeq_quoted_other_quote_and_backslash() {
        // A backslash does not escape the closing quote.
        for (code, args) in [
            ("ifeq 'a\"b' \"a'b\"\nendif\n", ("a\"b", "a'b")),
            ("ifeq \"a\\\" \"a\\\"\nendif\n", ("a\\", "a\\")),
        ] {
            assert_eq!(error_summary(code), vec![], "{code:?}");
            let makefile = Makefile::parse(code).tree();
            let cond = makefile.conditionals().next().unwrap();
            assert_eq!(
                cond.ifeq_args(),
                Some((args.0.to_string(), args.1.to_string()))
            );
        }
    }

    #[test]
    fn test_ifeq_quoted_comment() {
        // GNU make strips the comment before looking at the quotes, so the
        // first argument is not closed.
        let code = "ifeq \"a#b\" \"a\"\nendif\n";
        assert_eq!(
            error_summary(code),
            vec![(
                ParseErrorKind::InvalidConditional,
                1,
                "invalid syntax in conditional: unterminated quoted argument".to_string()
            )]
        );
        let makefile = Makefile::parse(code).tree();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("\"a".to_string()));
        assert_eq!(cond.ifeq_args(), None);
    }

    #[test]
    fn test_ifeq_parenthesized_line_continuation() {
        let code = "ifeq ($(A),\\\n  b)\nA = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("($(A), b)".to_string()));
        assert_eq!(
            cond.ifeq_args(),
            Some(("$(A)".to_string(), "b".to_string()))
        );
    }

    #[test]
    fn test_condition_for_variant() {
        let makefile: Makefile = "ifeq ($(subst a \\\n  b,c,a  b), \\\n  c)\nendif\n"
            .parse()
            .unwrap();
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.condition(),
            Some("($(subst a b,c,a  b), c)".to_string())
        );
        assert_eq!(
            cond.condition_for(MakefileVariant::GNUMake),
            Some("($(subst a b,c,a  b), c)".to_string())
        );
        assert_eq!(
            cond.condition_for(MakefileVariant::POSIXMake),
            Some("($(subst a  b,c,a  b),  c)".to_string())
        );
        assert_eq!(
            cond.ifeq_args(),
            Some(("$(subst a b,c,a  b)".to_string(), "c".to_string()))
        );
        assert_eq!(
            cond.ifeq_args_for(MakefileVariant::POSIXMake),
            Some(("$(subst a  b,c,a  b)".to_string(), "c".to_string()))
        );
        let branch = cond.branches().next().unwrap();
        assert_eq!(
            branch.condition_for(MakefileVariant::POSIXMake),
            Some("($(subst a  b,c,a  b),  c)".to_string())
        );
        assert_eq!(
            branch.ifeq_args_for(MakefileVariant::GNUMake),
            Some(("$(subst a b,c,a  b)".to_string(), "c".to_string()))
        );
    }

    #[test]
    fn test_condition_for_bsd() {
        let parsed = Makefile::parse_with_variant(
            ".if ${A:S/a/b/ \\\n\t:S/c/d/} == x\n.endif\n",
            MakefileVariant::BSDMake,
        );
        assert!(parsed.ok(), "{:?}", parsed.errors());
        let cond = parsed.tree().conditionals().next().unwrap();
        assert_eq!(
            cond.condition_for(MakefileVariant::GNUMake),
            Some("${A:S/a/b/ :S/c/d/} == x".to_string())
        );
        assert_eq!(
            cond.condition(),
            Some("${A:S/a/b/  :S/c/d/} == x".to_string())
        );
        assert_eq!(
            cond.condition_for(MakefileVariant::BSDMake),
            Some("${A:S/a/b/  :S/c/d/} == x".to_string())
        );
        let branch = cond.branches().next().unwrap();
        assert_eq!(
            branch.bsd_condition(),
            Some(crate::parse_bsd_condition("${A:S/a/b/  :S/c/d/} == x"))
        );
    }

    #[test]
    fn test_conditionals_iterator() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
endif

ifndef RELEASE
OTHER = dev
endif
"#
        .parse()
        .unwrap();

        let conditionals: Vec<_> = makefile.conditionals().collect();
        assert_eq!(conditionals.len(), 2);

        assert_eq!(
            conditionals[0].conditional_type(),
            Some("ifdef".to_string())
        );
        assert_eq!(
            conditionals[1].conditional_type(),
            Some("ifndef".to_string())
        );
    }

    #[test]
    fn test_conditional_type_and_condition() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
endif
"#
        .parse()
        .unwrap();

        let conditional = makefile.conditionals().next().unwrap();
        assert_eq!(conditional.conditional_type(), Some("ifdef".to_string()));
        assert_eq!(conditional.condition(), Some("DEBUG".to_string()));
    }

    #[test]
    fn test_conditional_has_else() {
        let makefile_with_else: Makefile = r#"ifdef DEBUG
VAR = debug
else
VAR = release
endif
"#
        .parse()
        .unwrap();

        let conditional = makefile_with_else.conditionals().next().unwrap();
        assert!(conditional.has_else());

        let makefile_without_else: Makefile = r#"ifdef DEBUG
VAR = debug
endif
"#
        .parse()
        .unwrap();

        let conditional = makefile_without_else.conditionals().next().unwrap();
        assert!(!conditional.has_else());
    }

    #[test]
    fn test_conditional_if_body() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
endif
"#
        .parse()
        .unwrap();

        let conditional = makefile.conditionals().next().unwrap();
        let if_body = conditional.if_body();
        assert!(if_body.is_some());
        assert!(if_body.unwrap().contains("VAR = debug"));
    }

    #[test]
    fn test_conditional_else_body() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
else
VAR = release
endif
"#
        .parse()
        .unwrap();

        let conditional = makefile.conditionals().next().unwrap();
        let else_body = conditional.else_body();
        assert!(else_body.is_some());
        assert!(else_body.unwrap().contains("VAR = release"));
    }

    #[test]
    fn test_add_else_item_to_unterminated_conditional() {
        let (makefile, _) = Makefile::from_str_relaxed("ifdef X\nY = 1");
        let item = "Y = 2\n"
            .parse::<Makefile>()
            .unwrap()
            .items()
            .next()
            .unwrap();
        makefile.conditionals().next().unwrap().add_else_item(item);
        assert_eq!(makefile.to_string(), "ifdef X\nY = 1\nelse\nY = 2\n");
    }

    #[test]
    fn test_add_endif_after_unterminated_line() {
        let (makefile, _) = Makefile::from_str_relaxed("ifdef X\nY = 1");
        assert!(makefile.conditionals().next().unwrap().add_endif().unwrap());
        assert_eq!(makefile.to_string(), "ifdef X\nY = 1\nendif\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_endif_after_unterminated_rule() {
        let (makefile, _) = Makefile::from_str_relaxed("ifdef X\na:");
        assert!(makefile.conditionals().next().unwrap().add_endif().unwrap());
        assert_eq!(makefile.to_string(), "ifdef X\na:\nendif\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_conditional_api_integration() {
        // Create a makefile with a rule and a variable
        let mut makefile: Makefile = r#"VAR1 = value1

rule1:
	command1
"#
        .parse()
        .unwrap();

        // Add a conditional
        makefile
            .add_conditional("ifdef", "DEBUG", "CFLAGS += -g\n", Some("CFLAGS += -O2\n"))
            .unwrap();

        // Verify the conditional was added
        assert_eq!(makefile.conditionals().count(), 1);
        let conditional = makefile.conditionals().next().unwrap();
        assert_eq!(conditional.conditional_type(), Some("ifdef".to_string()));
        assert_eq!(conditional.condition(), Some("DEBUG".to_string()));
        assert!(conditional.has_else());

        // The original variable and the two in the conditional
        assert_eq!(makefile.variable_definitions().count(), 3);
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_conditional_if_items() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
rule:
	command
endif
"#
        .parse()
        .unwrap();

        let cond = makefile.conditionals().next().unwrap();
        let items: Vec<_> = cond.if_items().collect();
        assert_eq!(items.len(), 2); // One variable, one rule

        match &items[0] {
            MakefileItem::Variable(v) => {
                assert_eq!(v.name(), Some("VAR".to_string()));
            }
            _ => panic!("Expected variable"),
        }

        match &items[1] {
            MakefileItem::Rule(r) => {
                assert!(r.targets().any(|t| t == "rule"));
            }
            _ => panic!("Expected rule"),
        }
    }

    #[test]
    fn test_conditional_else_items() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
else
VAR2 = release
rule2:
	command
endif
"#
        .parse()
        .unwrap();

        let cond = makefile.conditionals().next().unwrap();
        let items: Vec<_> = cond.else_items().collect();
        assert_eq!(items.len(), 2); // One variable, one rule

        match &items[0] {
            MakefileItem::Variable(v) => {
                assert_eq!(v.name(), Some("VAR2".to_string()));
            }
            _ => panic!("Expected variable"),
        }

        match &items[1] {
            MakefileItem::Rule(r) => {
                assert!(r.targets().any(|t| t == "rule2"));
            }
            _ => panic!("Expected rule"),
        }
    }

    #[test]
    fn test_conditional_add_if_item() {
        let makefile: Makefile = "ifdef DEBUG\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();

        // Parse a variable from a temporary makefile
        let temp: Makefile = "CFLAGS = -g\n".parse().unwrap();
        let var = temp.variable_definitions().next().unwrap();
        cond.add_if_item(MakefileItem::Variable(var));

        let code = makefile.to_string();
        assert!(code.contains("CFLAGS = -g"));

        // Verify it's in the if branch
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.if_items().count(), 1);
    }

    #[test]
    fn test_conditional_add_else_item() {
        let makefile: Makefile = "ifdef DEBUG\nVAR=1\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();

        // Parse a variable from a temporary makefile
        let temp: Makefile = "CFLAGS = -O2\n".parse().unwrap();
        let var = temp.variable_definitions().next().unwrap();
        cond.add_else_item(MakefileItem::Variable(var));

        let code = makefile.to_string();
        assert!(code.contains("else"));
        assert!(code.contains("CFLAGS = -O2"));

        // Verify it's in the else branch
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.else_items().count(), 1);
    }

    #[test]
    fn test_conditional_add_if_item_without_newline() {
        let makefile: Makefile = "ifdef X\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_if_item(item_without_newline("Y = 2"));
        assert_eq!(makefile.to_string(), "ifdef X\nY = 2\nendif\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_conditional_add_else_item_without_newline() {
        let makefile: Makefile = "ifdef X\nY = 1\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_else_item(item_without_newline("Y = 2"));
        assert_eq!(makefile.to_string(), "ifdef X\nY = 1\nelse\nY = 2\nendif\n");
    }

    #[test]
    fn test_add_else_item_to_plain_else() {
        let makefile: Makefile = "ifdef X\nA = 1\nelse\nA = 3\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_else_item(item_without_newline("B = 4"));
        assert_eq!(
            makefile.to_string(),
            "ifdef X\nA = 1\nelse\nB = 4\nA = 3\nendif\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_else_item_to_else_if_chain() {
        let makefile: Makefile = "ifdef X\nA = 1\nelse ifdef Y\nA = 2\nelse\nA = 3\nendif\n"
            .parse()
            .unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_else_item(item_without_newline("B = 4"));
        assert_eq!(
            makefile.to_string(),
            "ifdef X\nA = 1\nelse ifdef Y\nA = 2\nelse\nB = 4\nA = 3\nendif\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_else_item_to_else_if_chain_without_else() {
        let makefile: Makefile = "ifdef X\nA = 1\nelse ifdef Y\nA = 2\nendif\n"
            .parse()
            .unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_else_item(item_without_newline("B = 4"));
        assert_eq!(
            makefile.to_string(),
            "ifdef X\nA = 1\nelse ifdef Y\nA = 2\nelse\nB = 4\nendif\n"
        );
        let branches: Vec<_> = cond
            .branches()
            .map(|b| {
                (
                    b.conditional_type(),
                    b.items()
                        .map(|i| i.syntax().to_string())
                        .collect::<Vec<_>>(),
                )
            })
            .collect();
        assert_eq!(
            branches,
            vec![
                (Some("ifdef".to_string()), vec!["A = 1\n".to_string()]),
                (Some("ifdef".to_string()), vec!["A = 2\n".to_string()]),
                (None, vec!["B = 4\n".to_string()]),
            ]
        );
    }

    #[test]
    fn test_add_else_item_to_bsd_elif_chain_without_else() {
        let makefile: Makefile = ".if ${X}\nA = 1\n.elifdef Y\nA = 2\n.endif\n"
            .parse()
            .unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_else_item(item_without_newline("B = 4"));
        assert_eq!(
            makefile.to_string(),
            ".if ${X}\nA = 1\n.elifdef Y\nA = 2\n.else\nB = 4\n.endif\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_conditional_add_if_item_rule_without_newline() {
        let makefile: Makefile = "ifdef X\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_if_item(item_without_newline("a:\n\tcmd"));
        assert_eq!(makefile.to_string(), "ifdef X\na:\n\tcmd\nendif\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_conditional_add_if_item_conditional_without_newline() {
        let makefile: Makefile = "ifdef X\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_if_item(item_without_newline("ifdef Y\nZ = 1\nendif"));
        assert_eq!(
            makefile.to_string(),
            "ifdef X\nifdef Y\nZ = 1\nendif\nendif\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_conditional_add_if_item_with_newline() {
        let makefile: Makefile = "ifdef X\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        let item = "Y = 2\n"
            .parse::<Makefile>()
            .unwrap()
            .items()
            .next()
            .unwrap();
        cond.add_if_item(item);
        assert_eq!(makefile.to_string(), "ifdef X\nY = 2\nendif\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_conditional_items_with_nested_conditional() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
ifdef VERBOSE
	VAR2 = verbose
endif
endif
"#
        .parse()
        .unwrap();

        let cond = makefile.conditionals().next().unwrap();
        let items: Vec<_> = cond.if_items().collect();
        assert_eq!(items.len(), 2); // One variable, one nested conditional

        match &items[0] {
            MakefileItem::Variable(v) => {
                assert_eq!(v.name(), Some("VAR".to_string()));
            }
            _ => panic!("Expected variable"),
        }

        match &items[1] {
            MakefileItem::Conditional(c) => {
                assert_eq!(c.conditional_type(), Some("ifdef".to_string()));
            }
            _ => panic!("Expected conditional"),
        }
    }

    #[test]
    fn test_conditional_items_with_include() {
        let makefile: Makefile = r#"ifdef DEBUG
include debug.mk
VAR = debug
endif
"#
        .parse()
        .unwrap();

        let cond = makefile.conditionals().next().unwrap();
        let items: Vec<_> = cond.if_items().collect();
        assert_eq!(items.len(), 2); // One include, one variable

        match &items[0] {
            MakefileItem::Include(i) => {
                assert_eq!(i.path(), Some("debug.mk".to_string()));
            }
            _ => panic!("Expected include"),
        }

        match &items[1] {
            MakefileItem::Variable(v) => {
                assert_eq!(v.name(), Some("VAR".to_string()));
            }
            _ => panic!("Expected variable"),
        }
    }

    #[test]
    fn test_conditional_unwrap() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
rule:
	command
endif
"#
        .parse()
        .unwrap();

        let mut cond = makefile.conditionals().next().unwrap();
        cond.replace_with_body().unwrap();

        let code = makefile.to_string();
        let expected = "VAR = debug\nrule:\n\tcommand\n";
        assert_eq!(code, expected);

        // Should have no conditionals now
        assert_eq!(makefile.conditionals().count(), 0);

        // Should still have the variable and rule
        assert_eq!(makefile.variable_definitions().count(), 1);
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_conditional_unwrap_with_else_fails() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
else
VAR = release
endif
"#
        .parse()
        .unwrap();

        let mut cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            crate::test_util::expect_invalid_edit(cond.replace_with_body()),
            crate::InvalidEdit::new(
                crate::InvalidEditKind::Unsupported,
                "Conditional::replace_with_body",
                "Cannot unwrap conditional with else clause"
            )
        );
    }

    #[test]
    fn test_conditional_unwrap_nested() {
        let makefile: Makefile = r#"ifdef OUTER
VAR = outer
ifdef INNER
VAR2 = inner
endif
endif
"#
        .parse()
        .unwrap();

        // Unwrap the outer conditional
        let mut outer_cond = makefile.conditionals().next().unwrap();
        outer_cond.replace_with_body().unwrap();

        let code = makefile.to_string();
        let expected = "VAR = outer\nifdef INNER\nVAR2 = inner\nendif\n";
        assert_eq!(code, expected);
    }

    #[test]
    fn test_conditional_unwrap_empty() {
        let makefile: Makefile = r#"ifdef DEBUG
endif
"#
        .parse()
        .unwrap();

        let mut cond = makefile.conditionals().next().unwrap();
        cond.replace_with_body().unwrap();

        let code = makefile.to_string();
        assert_eq!(code, "");
    }

    fn branch_keywords(makefile: &Makefile) -> Vec<Vec<Option<String>>> {
        let text = makefile.to_string();
        makefile
            .conditionals()
            .map(|cond| {
                cond.branches()
                    .map(|b| b.keyword_range())
                    .chain(std::iter::once(cond.endif_range()))
                    .map(|r| r.map(|r| text[r].to_string()))
                    .collect()
            })
            .collect()
    }

    fn strings(v: &[&[Option<&str>]]) -> Vec<Vec<Option<String>>> {
        v.iter()
            .map(|b| b.iter().map(|s| s.map(str::to_string)).collect())
            .collect()
    }

    #[test]
    fn test_keyword_ranges_gnu() {
        let (makefile, _) = Makefile::from_str_relaxed(
            "ifdef A\nelse ifeq (a,b)\nelse  ifndef B # c\nelse # d\nendif # e\nifeq (x,y)\n",
        );
        assert_eq!(
            branch_keywords(&makefile),
            strings(&[
                &[
                    Some("ifdef"),
                    Some("else ifeq"),
                    Some("else  ifndef"),
                    Some("else"),
                    Some("endif"),
                ],
                &[Some("ifeq"), None],
            ])
        );
    }

    #[test]
    fn test_keyword_ranges_indented_crlf() {
        let text = "  ifdef A\r\nX = 1\r\n  else\r\n  endif\r\n";
        let makefile: Makefile = text.parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        let ranges: Vec<_> = cond
            .branches()
            .map(|b| b.keyword_range())
            .chain(std::iter::once(cond.endif_range()))
            .collect();
        assert_eq!(
            ranges,
            vec![
                Some(rowan::TextRange::new(2.into(), 7.into())),
                Some(rowan::TextRange::new(20.into(), 24.into())),
                Some(rowan::TextRange::new(28.into(), 33.into())),
            ]
        );
    }

    #[test]
    fn test_keyword_ranges_bsd() {
        let makefile = Makefile::parse_with_variant(
            ".if 1\n.  elif 2\n.else\n.  endif\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        assert_eq!(
            branch_keywords(&makefile),
            strings(&[&[
                Some(".if"),
                Some(".  elif"),
                Some(".else"),
                Some(".  endif")
            ]])
        );
    }

    #[test]
    fn test_keyword_ranges_nmake() {
        let makefile = Makefile::parse_with_variant(
            "!  if 1\n!ELSE IF 2\n!ELSEIFDEF A\n! else\n!ENDIF\n",
            MakefileVariant::NMake,
        )
        .tree();
        assert_eq!(
            branch_keywords(&makefile),
            strings(&[&[
                Some("!  if"),
                Some("!ELSE IF"),
                Some("!ELSEIFDEF"),
                Some("! else"),
                Some("!ENDIF"),
            ]])
        );
    }

    /// (condition, index) of a branch.
    type BranchKey = (Option<String>, usize);

    /// The keys of the branches enclosing each variable definition.
    fn variable_branches(makefile: &Makefile) -> Vec<(String, Vec<BranchKey>)> {
        makefile
            .variable_definitions()
            .map(|v| {
                let branches = v
                    .enclosing_branches()
                    .iter()
                    .map(|b| (b.condition(), b.index()))
                    .collect();
                (v.name().unwrap(), branches)
            })
            .collect()
    }

    fn s(text: &str) -> Option<String> {
        Some(text.to_string())
    }

    #[test]
    fn test_enclosing_branches_nested_else_if() {
        let makefile: Makefile = "A = 0\nifdef X\nB = 1\nifeq ($(Y),1)\nC = 2\nelse\nD = 3\nendif\nelse ifdef Z\nE = 4\nelse\nF = 5\nendif\nG = 6\n"
            .parse()
            .unwrap();
        assert_eq!(
            variable_branches(&makefile),
            vec![
                ("A".to_string(), vec![]),
                ("B".to_string(), vec![(s("X"), 0)]),
                ("C".to_string(), vec![(s("X"), 0), (s("($(Y),1)"), 0)]),
                ("D".to_string(), vec![(s("X"), 0), (None, 1)]),
                ("E".to_string(), vec![(s("Z"), 1)]),
                ("F".to_string(), vec![(None, 2)]),
                ("G".to_string(), vec![]),
            ]
        );
    }

    #[test]
    fn test_enclosing_branches_bsd() {
        let makefile = Makefile::parse_with_variant(
            ".if ${A}\nX=1\n.elif ${B}\n.for f in a b\nY=2\n.endfor\n.else\n.ifdef C\nZ=3\n.endif\n.endif\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        assert_eq!(
            variable_branches(&makefile),
            vec![
                ("X".to_string(), vec![(s("${A}"), 0)]),
                ("Y".to_string(), vec![(s("${B}"), 1)]),
                ("Z".to_string(), vec![(None, 2), (s("C"), 0)]),
            ]
        );
    }

    #[test]
    fn test_enclosing_branches_nmake() {
        let makefile = Makefile::parse_with_variant(
            "!IF 1\nX=1\n!ELSE IFDEF B\nY=2\n!ELSE\nZ=3\n!ENDIF\n",
            MakefileVariant::NMake,
        )
        .tree();
        assert_eq!(
            variable_branches(&makefile),
            vec![
                ("X".to_string(), vec![(s("1"), 0)]),
                ("Y".to_string(), vec![(s("B"), 1)]),
                ("Z".to_string(), vec![(None, 2)]),
            ]
        );
    }

    #[test]
    fn test_enclosing_branches_in_rules() {
        let makefile: Makefile = "ifdef A\nall: X = 1\nall:\n\techo all\nifdef B\n\techo b\nelse\n\techo not b\nendif\nendif\n"
            .parse()
            .unwrap();
        let conditions = |branches: Vec<ConditionalBranch>| -> Vec<BranchKey> {
            branches
                .iter()
                .map(|b| (b.condition(), b.index()))
                .collect()
        };
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 2);
        assert_eq!(conditions(rules[0].enclosing_branches()), vec![(s("A"), 0)]);
        assert_eq!(conditions(rules[1].enclosing_branches()), vec![(s("A"), 0)]);
        let scoped = rules[0].scoped_assignment().unwrap();
        assert_eq!(conditions(scoped.enclosing_branches()), vec![(s("A"), 0)]);
        let recipes: Vec<_> = rules[1]
            .recipe_nodes()
            .map(|r| (r.text(), conditions(r.enclosing_branches())))
            .collect();
        assert_eq!(
            recipes,
            vec![
                ("echo all".to_string(), vec![(s("A"), 0)]),
                ("echo b".to_string(), vec![(s("A"), 0), (s("B"), 0)]),
                ("echo not b".to_string(), vec![(s("A"), 0), (None, 1)]),
            ]
        );
        let items: Vec<_> = makefile.items().collect();
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].enclosing_branches(), vec![]);
        let MakefileItem::Conditional(cond) = &items[0] else {
            panic!("expected conditional");
        };
        let branch = cond.branches().next().unwrap();
        let inner: Vec<_> = branch
            .items()
            .map(|item| conditions(item.enclosing_branches()))
            .collect();
        assert_eq!(inner, vec![vec![(s("A"), 0)], vec![(s("A"), 0)]]);
    }

    #[test]
    fn test_enclosing_branches_recipe_after_conditional() {
        let makefile: Makefile = "ifdef X\na:\nelse\nb:\nendif\n\techo hi\n".parse().unwrap();
        let Some(MakefileItem::Recipe(recipe)) = makefile.items().nth(1) else {
            panic!("expected recipe");
        };
        assert_eq!(recipe.enclosing_branches(), vec![]);
    }

    /// The ancestor walk makefile-lsp used before enclosing_branches existed.
    fn branches_by_ancestors(
        node: &rowan::SyntaxNode<crate::lossless::Lang>,
    ) -> Vec<(rowan::TextRange, usize)> {
        node.ancestors()
            .zip(node.ancestors().skip(1))
            .filter(|(_, parent)| parent.kind() == crate::SyntaxKind::CONDITIONAL)
            .map(|(child, conditional)| {
                let branch = conditional
                    .children()
                    .take_while(|c| c != &child)
                    .filter(|c| c.kind() == crate::SyntaxKind::CONDITIONAL_ELSE)
                    .count();
                (conditional.text_range(), branch)
            })
            .collect()
    }

    #[test]
    fn test_enclosing_branches_matches_ancestor_walk() {
        let texts = [
            "ifdef X\na:\nelse\nb:\nendif\nc:\n",
            "ifdef X\nifdef Y\na:\nelse ifdef Z\nb:\nelse\nc:\nendif\nendif\nd:\n",
            "all:\nifdef X\n\techo a\nelse\n\techo b\nendif\n\techo\n",
            "ifdef X\nall:\nifdef Y\n\techo a\nelse ifdef Z\n\techo b\nendif\nendif\n",
            "ifdef X\r\nA = 1\r\nelse\r\nB = 2\r\nendif\r\n",
            "ifeq ($(A),\\\n  1)\nA = 1\nelse\nB = 2\nendif\n",
        ];
        for text in texts {
            let makefile: Makefile = text.parse().unwrap();
            let mut nodes: Vec<rowan::SyntaxNode<crate::lossless::Lang>> = Vec::new();
            nodes.extend(makefile.rules().map(|r| r.syntax().clone()));
            nodes.extend(makefile.variable_definitions().map(|v| v.syntax().clone()));
            nodes.extend(makefile.rules().flat_map(|r| {
                r.recipe_nodes()
                    .map(|n| n.syntax().clone())
                    .collect::<Vec<_>>()
            }));
            assert!(!nodes.is_empty(), "{:?}", text);
            for node in nodes {
                let mut expected = branches_by_ancestors(&node);
                expected.reverse();
                let actual: Vec<_> = super::enclosing_branches(&node)
                    .iter()
                    .map(|b| (b.conditional().syntax().text_range(), b.index()))
                    .collect();
                assert_eq!(actual, expected, "{:?}", text);
            }
        }
    }

    #[test]
    fn test_branch_conditional() {
        let makefile: Makefile = "ifdef A\nifdef B\nX = 1\nendif\nendif\n".parse().unwrap();
        let outer = makefile.conditionals().next().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        let branches = var.enclosing_branches();
        assert_eq!(branches.len(), 2);
        assert!(branches[0].conditional() == outer);
        assert_eq!(branches[1].conditional().condition(), s("B"));
        assert!(branches[1].conditional().parent().is_some());
        assert_eq!(branches[0], outer.branches().next().unwrap());
    }

    #[test]
    fn test_is_exclusive_with() {
        let makefile: Makefile = "ifdef A\nX = 1\nifdef B\nY = 1\nelse\nY = 2\nendif\nelse ifdef C\nX = 2\nelse\nX = 3\nendif\nifdef A\nZ = 1\nendif\n"
            .parse()
            .unwrap();
        let branches: Vec<Vec<ConditionalBranch>> = makefile
            .variable_definitions()
            .map(|v| v.enclosing_branches())
            .collect();
        let exclusive = |a: usize, b: usize| {
            branches[a]
                .iter()
                .any(|x| branches[b].iter().any(|y| x.is_exclusive_with(y)))
        };
        // X=1, Y=1, Y=2, X=2, X=3, Z=1
        assert!(!exclusive(0, 0));
        assert!(!exclusive(0, 1));
        assert!(exclusive(1, 2));
        assert!(exclusive(2, 1));
        assert!(exclusive(0, 3));
        assert!(exclusive(1, 3));
        assert!(exclusive(3, 4));
        assert!(exclusive(0, 4));
        assert!(!exclusive(0, 5));
        assert!(!exclusive(4, 5));
    }

    #[test]
    fn test_branch_ranges() {
        let text = "ifdef A\nX = 1\nelse ifeq ($(B),1) # c\nX = 2\n\nelse\nendif\n";
        let makefile: Makefile = text.parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        let ranges: Vec<_> = cond
            .branches()
            .map(|b| {
                (
                    &text[b.text_range().start().into()..b.text_range().end().into()],
                    &text[b.directive_range().start().into()..b.directive_range().end().into()],
                )
            })
            .collect();
        assert_eq!(
            ranges,
            vec![
                ("ifdef A\nX = 1\n", "ifdef A"),
                (
                    "else ifeq ($(B),1) # c\nX = 2\n\n",
                    "else ifeq ($(B),1) # c"
                ),
                ("else\n", "else"),
            ]
        );
    }

    #[test]
    fn test_branch_ranges_crlf_and_continuation() {
        let text = "ifeq ($(A),\\\r\n  1)\r\nX = 1\r\nelse\r\nX = 2\r\nendif\r\n";
        let makefile: Makefile = text.parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        let ranges: Vec<_> = cond
            .branches()
            .map(|b| {
                (
                    &text[b.text_range().start().into()..b.text_range().end().into()],
                    &text[b.directive_range().start().into()..b.directive_range().end().into()],
                )
            })
            .collect();
        assert_eq!(
            ranges,
            vec![
                (
                    "ifeq ($(A),\\\r\n  1)\r\nX = 1\r\n",
                    "ifeq ($(A),\\\r\n  1)"
                ),
                ("else\r\nX = 2\r\n", "else"),
            ]
        );
    }

    #[test]
    fn test_branch_ranges_bsd_unterminated() {
        let text = ".if ${A}\nX=1\n.elif ${B}\nY=2\n";
        let (makefile, _) = Makefile::from_str_relaxed(text);
        let cond = makefile.conditionals().next().unwrap();
        assert!(!cond.has_endif());
        let ranges: Vec<_> = cond
            .branches()
            .map(|b| {
                (
                    u32::from(b.text_range().start()),
                    u32::from(b.text_range().end()),
                )
            })
            .collect();
        assert_eq!(ranges, vec![(0, 13), (13, 28)]);
    }

    #[test]
    fn test_has_endif() {
        let makefile: Makefile = "ifdef A\nendif\n".parse().unwrap();
        assert!(makefile.conditionals().next().unwrap().has_endif());

        let makefile =
            Makefile::parse_with_variant(".if 1\n.endif\n", MakefileVariant::BSDMake).tree();
        assert!(makefile.conditionals().next().unwrap().has_endif());

        let makefile =
            Makefile::parse_with_variant("!IF 1\n!ENDIF\n", MakefileVariant::NMake).tree();
        assert!(makefile.conditionals().next().unwrap().has_endif());

        // The only endif closes the inner conditional.
        let (makefile, _) = Makefile::from_str_relaxed("ifdef A\nifdef B\nendif\n");
        let outer = makefile.conditionals().next().unwrap();
        assert!(!outer.has_endif());
        let Some(MakefileItem::Conditional(inner)) = outer.if_items().next() else {
            panic!("expected nested conditional");
        };
        assert!(inner.has_endif());
    }

    #[test]
    fn test_branch_debug() {
        let makefile: Makefile = "ifdef A\nX = 1\nelse\nendif\n".parse().unwrap();
        let cond = makefile.conditionals().next().unwrap();
        let debug: Vec<_> = cond.branches().map(|b| format!("{:?}", b)).collect();
        assert_eq!(
            debug,
            vec![
                "ConditionalBranch { index: 0, range: 0..14 }",
                "ConditionalBranch { index: 1, range: 14..19 }",
            ]
        );
    }

    fn parsed_item(src: &str) -> MakefileItem {
        let temp: Makefile = src.parse().unwrap();
        let item = temp.items().next().unwrap();
        item
    }

    #[test]
    fn test_add_else_item_to_existing_else() {
        let makefile: Makefile = "ifdef X\nelse\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_else_item(parsed_item("b:\n"));
        assert_eq!(makefile.to_string(), "ifdef X\nelse\nb:\nendif\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_else_item_after_else_comment() {
        let makefile: Makefile = "ifdef X\nelse # c\nA = 1\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_else_item(parsed_item("b:\n"));
        assert_eq!(
            makefile.to_string(),
            "ifdef X\nelse # c\nb:\nA = 1\nendif\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_else_item_to_else_if() {
        let makefile: Makefile = "ifdef X\nelse ifdef Y\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_else_item(parsed_item("b:\n"));
        assert_eq!(
            makefile.to_string(),
            "ifdef X\nelse ifdef Y\nelse\nb:\nendif\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_if_item_to_existing_conditional() {
        let makefile: Makefile = "ifeq (a,b)\nelse\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        cond.add_if_item(parsed_item("b:\n"));
        cond.add_else_item(parsed_item("c:\n"));
        assert_eq!(makefile.to_string(), "ifeq (a,b)\nb:\nelse\nc:\nendif\n");
        assert_matches_reparse(&makefile);
    }
}
