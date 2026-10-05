use super::bsd::keyword_token;
use super::collapse_continuations;
use super::makefile::MakefileItem;
use crate::bsd_condition::{parse_bsd_condition, BsdCondition, BsdConditionError};
use crate::lossless::{
    lf_line_endings, line_col_at_offset, remove_with_preceding_comments, Conditional, Error,
    ErrorInfo, Lang, ParseError, Recipe,
};
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
                buf = String::new();
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
#[derive(Clone)]
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
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".if ${A}\n.elifndef B\n.else\n.endif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let types: Vec<_> = cond.branches().map(|b| b.conditional_type()).collect();
    /// assert_eq!(types, vec![Some(".if".to_string()), Some(".ifndef".to_string()), None]);
    /// ```
    pub fn conditional_type(&self) -> Option<String> {
        let (_, keyword) = keyword_token(&self.header)?;
        if let Some(rest) = keyword.strip_prefix(".elif") {
            return Some(format!(".if{}", rest));
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
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "ifdef A\nelse ifndef $(B)\nendif\n".parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let conditions: Vec<_> = cond.branches().map(|b| b.condition()).collect();
    /// assert_eq!(conditions, vec![Some("A".to_string()), Some("$(B)".to_string())]);
    /// ```
    pub fn condition(&self) -> Option<String> {
        let expr = self.header.children().find(|it| it.kind() == EXPR)?;
        Some(collapse_continuations(&expr).trim().to_string())
    }

    /// For an `ifeq` / `ifneq` branch, return the two argument strings
    /// (unexpanded). Supports both the `(a,b)` and `"a" "b"` (or
    /// `'a' 'b'`) syntaxes.
    ///
    /// Returns `None` for other directives (or if the args can't be
    /// recovered).
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
        if !matches!(self.conditional_type()?.as_str(), "ifeq" | "ifneq") {
            return None;
        }
        let text = self.condition()?;
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
    /// condition with [`parse_bsd_condition`].
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
        Some(parse_bsd_condition(&self.condition().unwrap_or_default()))
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
    ///                 ConditionalItem::Item(_) => panic!("expected recipe"),
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
    /// keyword.
    pub fn conditional_type(&self) -> Option<String> {
        self.if_branch()?.conditional_type()
    }

    /// Whether this is a BSD make conditional (`.if` ... `.endif`).
    fn is_bsd(&self) -> bool {
        self.conditional_type().is_some_and(|t| t.starts_with('.'))
    }

    /// Get the condition expression
    pub fn condition(&self) -> Option<String> {
        self.if_branch()?.condition()
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
    pub fn remove(&mut self) -> Result<(), Error> {
        let Some(parent) = self.syntax().parent() else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: "Cannot remove conditional: no parent node".to_string(),
                    line: 1,
                    context: "conditional_remove".to_string(),
                }],
            }));
        };

        remove_with_preceding_comments(self.syntax(), &parent);

        Ok(())
    }

    /// Remove the conditional directives (ifdef/endif) but keep the body content
    ///
    /// This "unwraps" the conditional, keeping only the if branch content.
    /// Returns an error if the conditional has an else clause.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = r#"ifdef DEBUG
    /// VAR = debug
    /// endif
    /// "#.parse().unwrap();
    /// let mut cond = makefile.conditionals().next().unwrap();
    /// cond.unwrap().unwrap();
    /// // Now makefile contains just "VAR = debug\n"
    /// assert!(makefile.to_string().contains("VAR = debug"));
    /// assert!(!makefile.to_string().contains("ifdef"));
    /// ```
    pub fn unwrap(&mut self) -> Result<(), Error> {
        // Check if there's an else clause
        if self.has_else() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: "Cannot unwrap conditional with else clause".to_string(),
                    line: 1,
                    context: "conditional_unwrap".to_string(),
                }],
            }));
        }

        let Some(parent) = self.syntax().parent() else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: "Cannot unwrap conditional: no parent node".to_string(),
                    line: 1,
                    context: "conditional_unwrap".to_string(),
                }],
            }));
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
        let item_node = item.syntax().clone();

        // Find position after CONDITIONAL_IF
        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|n| n.kind() == CONDITIONAL_IF)
            .map(|p| p + 1)
            .unwrap_or(0);

        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![item_node.into()]);
    }

    /// Add an item to the else branch of the conditional
    ///
    /// If the conditional doesn't have an else branch, this will create one.
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
        // Ensure there's an else clause
        if !self.has_else() {
            self.add_else_clause();
        }

        let item_node = item.syntax().clone();

        // Find position after CONDITIONAL_ELSE
        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|n| n.kind() == CONDITIONAL_ELSE)
            .map(|p| p + 1)
            .unwrap_or(0);

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
    /// assert_eq!(makefile.code(), "ifdef DEBUG\nVAR = 1\nendif\n");
    /// ```
    pub fn add_endif(&mut self) -> Result<bool, Error> {
        if self.conditional_type().is_none() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: "Cannot add endif to conditional with no opener".to_string(),
                    line: 1,
                    context: "conditional_add_endif".to_string(),
                }],
            }));
        }
        if self
            .syntax()
            .children_with_tokens()
            .any(|c| c.kind() == CONDITIONAL_ENDIF)
        {
            return Ok(false);
        }

        // Need a newline before `endif` if the current tail doesn't already end
        // with one.
        let needs_newline = self
            .syntax()
            .last_token()
            .is_none_or(|t| t.kind() != NEWLINE);

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(CONDITIONAL_ENDIF.into());
        if needs_newline {
            builder.token(NEWLINE.into(), "\n");
        }
        builder.token(
            IDENTIFIER.into(),
            if self.is_bsd() { ".endif" } else { "endif" },
        );
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let endif = SyntaxNode::new_root_mut(builder.finish());
        let count = self.syntax().children_with_tokens().count();
        self.syntax()
            .splice_children(count..count, vec![endif.into()]);

        Ok(true)
    }

    /// Add an else clause to the conditional if it doesn't already have one
    fn add_else_clause(&mut self) {
        if self.has_else() {
            return;
        }

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(CONDITIONAL_ELSE.into());
        builder.token(
            IDENTIFIER.into(),
            if self.is_bsd() { ".else" } else { "else" },
        );
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        // Find position before CONDITIONAL_ENDIF
        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|n| n.kind() == CONDITIONAL_ENDIF)
            .unwrap_or(self.syntax().children_with_tokens().count());

        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![syntax.into()]);
    }
}

#[cfg(test)]
mod tests {

    use super::{ConditionalBranch, ConditionalItem};
    use crate::lossless::Makefile;
    use crate::{
        BsdComparisonOp, BsdCondition, BsdConditionError, BsdFunction, BsdOperand, MakefileItem,
        MakefileVariant, RuleItem,
    };

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
        assert_eq!(makefile.code(), code);
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
        assert_eq!(makefile.code(), code);
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
        assert_eq!(makefile.code(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(
            cond.branches().map(describe).collect::<Vec<_>>(),
            vec![branch(Some("ifdef"), Some(""), 0, &["var X=1"])]
        );
    }

    #[test]
    fn test_empty_ifdef() {
        let code = "ifdef\nX = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.code(), code);
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
        assert_eq!(makefile.code(), code);
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
        assert_eq!(makefile.code(), code);
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
        assert_eq!(makefile.code(), code);
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
        assert_eq!(makefile.code(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_already_terminated_noop() {
        let makefile: Makefile = "ifdef DEBUG\nVAR = 1\nendif\n".parse().unwrap();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(!cond.add_endif().unwrap());
        assert_eq!(makefile.code(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_no_trailing_newline() {
        // Source with no final newline produces a parse error, but the tree
        // is still usable for mutations.
        let parsed = Makefile::parse("ifdef DEBUG\nVAR = 1");
        let makefile = parsed.tree();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.code(), "ifdef DEBUG\nVAR = 1\nendif\n");
    }

    #[test]
    fn test_add_endif_with_else() {
        let (makefile, _) = Makefile::from_str_relaxed("ifdef DEBUG\nA = 1\nelse\nA = 2\n");
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.code(), "ifdef DEBUG\nA = 1\nelse\nA = 2\nendif\n");
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
        assert_eq!(makefile.code(), "ifeq ($(X),y)\nA = 1\nB = 2\nendif\n");
    }

    #[test]
    fn test_ifdef_line_continuation() {
        let code = "ifdef \\\n  X\nA = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.code(), code);
        assert_eq!(makefile.rules().count(), 0);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("X".to_string()));
        assert_eq!(cond.if_items().count(), 1);
    }

    #[test]
    fn test_ifeq_quoted_line_continuation() {
        let code = "ifeq \"a\" \\\n  \"b\"\nA = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.code(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("\"a\" \"b\"".to_string()));
        assert_eq!(cond.ifeq_args(), Some(("a".to_string(), "b".to_string())));
        assert_eq!(cond.if_items().count(), 1);
    }

    #[test]
    fn test_ifeq_parenthesized_line_continuation() {
        let code = "ifeq ($(A),\\\n  b)\nA = 1\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.code(), code);
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("($(A), b)".to_string()));
        assert_eq!(
            cond.ifeq_args(),
            Some(("$(A)".to_string(), "b".to_string()))
        );
    }
}
