use super::rule::build_targets_node;
use super::{
    detach_tokens, doc_comment_lines, index_before_doc_comment, line_ending, lines_above,
    terminate_line_before, text_before, with_recipe_prefix, with_trailing_newline,
};
use crate::lossless::{
    line_col_at_offset, parse, Conditional, Directive, Error, ErrorInfo, ExpressionStatement,
    ForLoop, Include, Load, Makefile, ParseError, Recipe, Rule, SyntaxNode, VariableDefinition,
    VariableReference, Vpath,
};
use crate::pattern::matches_pattern;
use crate::MakefileVariant;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::GreenNodeBuilder;
use std::collections::VecDeque;

/// The `else` and `endif` keywords for a conditional of the given type,
/// which may be a GNU make (`ifdef`) or BSD make (`.ifdef`) conditional.
fn conditional_keywords(conditional_type: &str) -> Option<(&'static str, &'static str)> {
    match conditional_type {
        "ifdef" | "ifndef" | "ifeq" | "ifneq" => Some(("else", "endif")),
        ".if" | ".ifdef" | ".ifndef" | ".ifmake" | ".ifnmake" => Some((".else", ".endif")),
        _ => None,
    }
}

/// The first line of a conditional, without a space after the keyword if
/// the condition is empty.
fn conditional_if_line(conditional_type: &str, condition: &str) -> String {
    if condition.is_empty() {
        conditional_type.to_string()
    } else {
        format!("{conditional_type} {condition}")
    }
}

/// Check that a conditional of `conditional_type` with `condition` and the
/// given bodies reads back as a single conditional, without errors and with
/// an else branch only if there is an `else_body`. Make rejects e.g.
/// `ifeq ()`, and an `else` line in a body would start another branch.
fn check_conditional(
    (conditional_type, else_keyword, endif_keyword): (&str, &str, &str),
    condition: &str,
    if_body: &str,
    else_body: Option<&str>,
    context: &str,
) -> Result<(), Error> {
    let error = |message: String| {
        Error::Parse(ParseError {
            errors: vec![ErrorInfo {
                kind: crate::ParseErrorKind::Other,
                message,
                line: 1,
                context: context.to_string(),
            }],
        })
    };
    let if_line = conditional_if_line(conditional_type, condition);
    let mut lines = vec![if_line.as_str()];
    lines.extend(if_body.lines());
    if let Some(else_body) = else_body {
        lines.push(else_keyword);
        lines.extend(else_body.lines());
    }
    lines.push(endif_keyword);
    let text: String = lines.iter().flat_map(|line| [*line, "\n"]).collect();

    let parsed = parse(&text, None);
    if !parsed.errors.is_empty() {
        return Err(Error::Parse(ParseError {
            errors: parsed.errors,
        }));
    }
    let root = parsed.root();
    let mut items = root.syntax().children();
    let conditional = items
        .next()
        .and_then(Conditional::cast)
        .filter(|_| items.next().is_none())
        .ok_or_else(|| error(format!("{text:?} does not parse as a single conditional")))?;
    let else_branches = conditional
        .syntax()
        .children()
        .filter(|n| n.kind() == CONDITIONAL_ELSE)
        .count();
    if else_branches != usize::from(else_body.is_some()) {
        return Err(error(format!(
            "A body of {text:?} starts another branch of the conditional"
        )));
    }
    // The parser accepts these, but make reports "invalid syntax in
    // conditional".
    if matches!(conditional_type, "ifeq" | "ifneq") && conditional.ifeq_args().is_none() {
        return Err(error(format!(
            "Invalid condition for {conditional_type}: {condition:?}"
        )));
    }
    Ok(())
}

/// Whether an item appended to `root` needs a blank line before it, i.e.
/// the makefile is neither empty nor already ends in a blank line. The
/// text must end in a line ending unless empty; see
/// [`terminate_line_before`].
fn needs_blank_line_at_end(root: &SyntaxNode) -> bool {
    needs_blank_line_before(root, root.children_with_tokens().count())
}

/// Like [`needs_blank_line_at_end`], for an item inserted before the
/// child at `index` of `root`.
fn needs_blank_line_before(root: &SyntaxNode, index: usize) -> bool {
    let text: String = root
        .children_with_tokens()
        .take(index)
        .map(|it| it.to_string())
        .collect();
    let Some(body) = text.strip_suffix('\n') else {
        return false;
    };
    let last_line = body.rsplit('\n').next().unwrap_or(body);
    !last_line.trim().is_empty()
}

/// Whether the parser puts the blank lines after `node` in it: a rule's
/// recipe continues after blank lines, unless the rule is a target-specific
/// assignment.
// TODO: BSD make target-local assignments, as in `a: X=1`, can be followed
// by commands, so the parser puts blank lines after them in the rule too,
// but the tree doesn't say which make it was parsed for.
fn takes_blank_lines(node: &SyntaxNode) -> bool {
    node.kind() == RULE
        && node
            .last_child_or_token()
            .is_none_or(|it| it.kind() != VARIABLE)
}

/// Insert `elements` before child `index` of `parent`. A BLANK_LINE node
/// directly after a rule goes in the rule instead, where the parser puts
/// it.
fn insert_items(parent: &SyntaxNode, index: usize, elements: Vec<crate::lossless::SyntaxElement>) {
    let mut index = index;
    let mut prev = index
        .checked_sub(1)
        .and_then(|i| parent.children_with_tokens().nth(i))
        .and_then(|it| it.into_node());
    for element in elements {
        if let (Some(rule), Some(blank)) = (
            prev.as_ref().filter(|n| takes_blank_lines(n)),
            element.as_node().filter(|n| n.kind() == BLANK_LINE),
        ) {
            let tokens: Vec<_> = blank.children_with_tokens().collect();
            for token in &tokens {
                token.detach();
            }
            let len = rule.children_with_tokens().count();
            rule.splice_children(len..len, tokens);
            continue;
        }
        prev = element.as_node().cloned();
        parent.splice_children(index..index, vec![element]);
        index += 1;
    }
}

/// Append `node` to the end of `root`, terminating any unterminated last
/// line and separating it from preceding content by a blank line as
/// described by [`needs_blank_line_at_end`].
fn append_with_blank_line(root: &SyntaxNode, node: SyntaxNode, eol: &str) {
    let pos = terminate_line_before(root, root.children_with_tokens().count(), eol);
    let node = with_recipe_prefix(&node, &text_before(root, pos));
    let mut nodes = Vec::new();
    if needs_blank_line_at_end(root) {
        let mut bl_builder = GreenNodeBuilder::new();
        bl_builder.start_node(BLANK_LINE.into());
        bl_builder.token(NEWLINE.into(), eol);
        bl_builder.finish_node();
        nodes.push(SyntaxNode::new_root_mut(bl_builder.finish()).into());
    }
    nodes.push(node.into());
    insert_items(root, pos, nodes);
}

/// Build a conditional by parsing its text, so that the tree is the same
/// as when the makefile is parsed again. Each body line is ended with
/// `eol`. Returns an error if the text does not parse as a single
/// conditional, such as when a body contains an unmatched `endif`.
fn build_conditional(
    if_line: &str,
    if_body: &str,
    else_branch: Option<(&str, &str)>,
    endif_keyword: &str,
    eol: &str,
    context: &str,
) -> Result<SyntaxNode, Error> {
    let mut lines = vec![if_line];
    lines.extend(if_body.lines());
    if let Some((else_keyword, else_body)) = else_branch {
        lines.push(else_keyword);
        lines.extend(else_body.lines());
    }
    lines.push(endif_keyword);
    let text: String = lines.iter().flat_map(|line| [*line, eol]).collect();

    let parsed = parse(&text, None);
    if !parsed.errors.is_empty() {
        return Err(Error::Parse(ParseError {
            errors: parsed.errors,
        }));
    }
    let root = parsed.root();
    let mut children = root.syntax().children_with_tokens();
    match (children.next(), children.next()) {
        (Some(rowan::NodeOrToken::Node(node)), None) if node.kind() == CONDITIONAL => {
            Ok(SyntaxNode::new_root_mut(node.green().into_owned()))
        }
        _ => Err(Error::Parse(ParseError {
            errors: vec![ErrorInfo {
                kind: crate::ParseErrorKind::Other,
                message: format!("{text:?} does not parse as a single conditional"),
                line: 1,
                context: context.to_string(),
            }],
        })),
    }
}

/// Represents different types of items that can appear in a Makefile
#[derive(Clone)]
#[non_exhaustive]
pub enum MakefileItem {
    /// A rule definition (e.g., "target: prerequisites")
    Rule(Rule),
    /// A variable definition (e.g., "VAR = value")
    Variable(VariableDefinition),
    /// An include directive (e.g., "include foo.mk")
    Include(Include),
    /// A conditional block (e.g., "ifdef DEBUG ... endif")
    Conditional(Conditional),
    /// A `vpath` directive (e.g., `vpath %.c src`)
    Vpath(Vpath),
    /// A BSD make `.for` loop
    ForLoop(ForLoop),
    /// A BSD make single-line directive (e.g., `.undef FOO`)
    Directive(Directive),
    /// A line of only references or function calls (e.g., `$(eval $(call f,x))`)
    ExpressionStatement(ExpressionStatement),
    /// A GNU make `load` directive (e.g., `load foo.so`)
    Load(Load),
    /// A recipe line after a conditional whose branches all end in rule
    /// context, as in `ifdef X\na:\nelse\nb:\nendif\n\techo hi\n`. It
    /// belongs to the rule that ends the branch make takes. Inside a
    /// conditional branch, such lines are returned as
    /// [`ConditionalItem::Recipe`](crate::ConditionalItem::Recipe) instead.
    Recipe(Recipe),
}

impl MakefileItem {
    /// Try to cast a syntax node to a MakefileItem
    pub(crate) fn cast(node: SyntaxNode) -> Option<Self> {
        if let Some(rule) = Rule::cast(node.clone()) {
            Some(MakefileItem::Rule(rule))
        } else if let Some(var) = VariableDefinition::cast(node.clone()) {
            Some(MakefileItem::Variable(var))
        } else if let Some(inc) = Include::cast(node.clone()) {
            Some(MakefileItem::Include(inc))
        } else if let Some(vp) = Vpath::cast(node.clone()) {
            Some(MakefileItem::Vpath(vp))
        } else if let Some(f) = ForLoop::cast(node.clone()) {
            Some(MakefileItem::ForLoop(f))
        } else if let Some(d) = Directive::cast(node.clone()) {
            Some(MakefileItem::Directive(d))
        } else if let Some(stmt) = ExpressionStatement::cast(node.clone()) {
            Some(MakefileItem::ExpressionStatement(stmt))
        } else if let Some(load) = Load::cast(node.clone()) {
            Some(MakefileItem::Load(load))
        } else if let Some(recipe) = Recipe::cast(node.clone()) {
            Some(MakefileItem::Recipe(recipe))
        } else {
            Conditional::cast(node).map(MakefileItem::Conditional)
        }
    }

    /// Get the underlying syntax node
    pub fn syntax(&self) -> &SyntaxNode {
        match self {
            MakefileItem::Rule(r) => r.syntax(),
            MakefileItem::Variable(v) => v.syntax(),
            MakefileItem::Include(i) => i.syntax(),
            MakefileItem::Conditional(c) => c.syntax(),
            MakefileItem::Vpath(v) => v.syntax(),
            MakefileItem::ForLoop(f) => f.syntax(),
            MakefileItem::Directive(d) => d.syntax(),
            MakefileItem::ExpressionStatement(e) => e.syntax(),
            MakefileItem::Load(l) => l.syntax(),
            MakefileItem::Recipe(r) => r.syntax(),
        }
    }

    /// Get the range of this item in the source text.
    ///
    /// This is cheap, unlike computing the line number.
    pub fn text_range(&self) -> rowan::TextRange {
        self.syntax().text_range()
    }

    /// The branches of the conditionals this item is in, outermost first.
    ///
    /// This covers conditionals at any depth, including conditionals in a
    /// rule body and BSD make `.elif` chains. Two items can never both take
    /// effect if any of their branches are exclusive, as checked by
    /// [`ConditionalBranch::is_exclusive_with`](crate::ConditionalBranch::is_exclusive_with).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile =
    ///     "ifdef A\nifdef B\nX = 1\nendif\nelse\nX = 2\nendif\nX = 3\n".parse().unwrap();
    /// let branches: Vec<_> = makefile
    ///     .variable_definitions()
    ///     .map(|v| v.enclosing_branches())
    ///     .collect();
    /// let indexes: Vec<Vec<usize>> = branches
    ///     .iter()
    ///     .map(|b| b.iter().map(|b| b.index()).collect())
    ///     .collect();
    /// assert_eq!(indexes, vec![vec![0, 0], vec![1], vec![]]);
    ///
    /// let exclusive = |a: &[_], b: &[_]| {
    ///     a.iter().any(|x: &makefile_lossless::ConditionalBranch| {
    ///         b.iter().any(|y| x.is_exclusive_with(y))
    ///     })
    /// };
    /// assert!(exclusive(&branches[0], &branches[1]));
    /// assert!(!exclusive(&branches[0], &branches[2]));
    /// ```
    pub fn enclosing_branches(&self) -> Vec<crate::ConditionalBranch> {
        super::conditional::enclosing_branches(self.syntax())
    }

    /// Get the line number (0-indexed) where this item starts.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "VAR = 1\n\nall:\n\techo\n".parse().unwrap();
    /// let lines: Vec<_> = makefile.items().map(|item| item.line()).collect();
    /// assert_eq!(lines, vec![0, 2]);
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

    /// Helper to get parent node or return an appropriate error
    fn get_parent_or_error(&self, action: &str, method: &str) -> Result<SyntaxNode, Error> {
        self.syntax().parent().ok_or_else(|| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: format!("Cannot {} item without parent", action),
                    line: 1,
                    context: format!("MakefileItem::{}", method),
                }],
            })
        })
    }

    /// Extract comment text from a comment token, removing '#' prefix
    fn extract_comment_text(token: &rowan::SyntaxToken<crate::lossless::Lang>) -> String {
        let text = token.text();
        text.strip_prefix("# ")
            .or_else(|| text.strip_prefix('#'))
            .unwrap_or(text)
            .to_string()
    }

    /// The comment tokens above this item, nearest first, going past blank
    /// lines.
    fn preceding_comment_tokens(&self) -> Vec<rowan::SyntaxToken<crate::lossless::Lang>> {
        lines_above(self.syntax())
            .into_iter()
            .filter_map(|line| line.comment)
            .collect()
    }

    /// Helper to parse comment text and extract properly formatted comment tokens
    ///
    /// Returns an error if `comment_text` can not be written as a single
    /// comment line, such as text containing a newline or ending in a
    /// backslash that would continue the comment onto the next line.
    fn parse_comment_tokens(
        comment_text: &str,
        eol: &str,
        context: &str,
    ) -> Result<
        (
            rowan::SyntaxToken<crate::lossless::Lang>,
            rowan::SyntaxToken<crate::lossless::Lang>,
        ),
        Error,
    > {
        let comment = format!("# {}", comment_text);
        let parsed = crate::lossless::parse(&format!("{comment}{eol}X = 1{eol}"), None);
        let root = parsed.root();
        let children: Vec<_> = root.syntax().children_with_tokens().collect();
        match children.as_slice() {
            [rowan::NodeOrToken::Token(c), rowan::NodeOrToken::Token(n), rowan::NodeOrToken::Node(v)]
                if c.kind() == COMMENT
                    && c.text() == comment
                    && n.kind() == NEWLINE
                    && v.kind() == VARIABLE
                    && parsed.errors.is_empty() =>
            {
                Ok((c.clone(), n.clone()))
            }
            _ => Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: format!("Cannot write {comment_text:?} as a single comment line"),
                    line: 1,
                    context: format!("MakefileItem::{context}"),
                }],
            })),
        }
    }

    /// Replace this MakefileItem with another MakefileItem
    ///
    /// This preserves the position of the original item but replaces its content
    /// with the new item. Preceding comments are preserved.
    ///
    /// Returns an error if the new item can not go there, as described for
    /// [`Self::insert_before`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let mut makefile: Makefile = "VAR1 = old\nrule:\n\tcommand\n".parse().unwrap();
    /// let temp: Makefile = "VAR2 = new\n".parse().unwrap();
    /// let new_var = temp.variable_definitions().next().unwrap();
    /// let mut first_item = makefile.items().next().unwrap();
    /// first_item.replace(MakefileItem::Variable(new_var)).unwrap();
    /// assert!(makefile.to_string().contains("VAR2 = new"));
    /// assert!(!makefile.to_string().contains("VAR1"));
    /// ```
    pub fn replace(&mut self, new_item: MakefileItem) -> Result<(), Error> {
        let parent = self.get_parent_or_error("replace", "replace")?;
        check_position(
            new_item.syntax(),
            self.syntax().prev_sibling(),
            self.syntax().next_sibling(),
            Some(self.syntax()),
            "replace",
        )?;
        let current_index = self.syntax().index();
        let new_node = with_trailing_newline(new_item.syntax(), &line_ending(&parent));
        let new_node = with_recipe_prefix(&new_node, &text_before(&parent, current_index));

        // Replace the current node with the new item's syntax
        parent.splice_children(
            current_index..current_index + 1,
            vec![new_node.clone().into()],
        );

        // Update self to point to the new item
        *self = MakefileItem::cast(new_node).expect("new node has the same kind as new_item");

        Ok(())
    }

    /// Add a comment before this MakefileItem
    ///
    /// The comment text should not include the leading '#' character.
    /// Multiple comment lines can be added by calling this method multiple times.
    /// Returns an error if the text can not be written as a single comment
    /// line, e.g. because it contains a newline.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "VAR = value\n".parse().unwrap();
    /// let mut item = makefile.items().next().unwrap();
    /// item.add_comment("This is a variable").unwrap();
    /// assert!(makefile.to_string().contains("# This is a variable"));
    /// ```
    pub fn add_comment(&mut self, comment_text: &str) -> Result<(), Error> {
        let parent = self.get_parent_or_error("add comment to", "add_comment")?;
        let current_index = self.syntax().index();

        // Get properly formatted comment tokens
        let (comment_token, newline_token) =
            Self::parse_comment_tokens(comment_text, &line_ending(self.syntax()), "add_comment")?;

        let elements = vec![
            rowan::NodeOrToken::Token(comment_token),
            rowan::NodeOrToken::Token(newline_token),
        ];

        // Insert comment and newline before the current item
        parent.splice_children(current_index..current_index, elements);

        Ok(())
    }

    /// Get all preceding comments for this MakefileItem
    ///
    /// Returns an iterator of comment strings (without the leading '#' and whitespace).
    ///
    /// These are the whole-line comments above the item, going past blank
    /// lines, up to a line with anything else on it or a shebang line.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "# Comment 1\n# Comment 2\nVAR = value\n".parse().unwrap();
    /// let item = makefile.items().next().unwrap();
    /// let comments: Vec<_> = item.preceding_comments().collect();
    /// assert_eq!(comments.len(), 2);
    /// assert_eq!(comments[0], "Comment 1");
    /// assert_eq!(comments[1], "Comment 2");
    /// ```
    pub fn preceding_comments(&self) -> impl Iterator<Item = String> {
        let mut comments: Vec<_> = self
            .preceding_comment_tokens()
            .iter()
            .map(Self::extract_comment_text)
            .collect();
        comments.reverse();
        comments.into_iter()
    }

    /// Get the doc comment of this item: the whole-line `#` comments directly
    /// above it, in source order.
    ///
    /// Unlike [`Self::preceding_comments`], this stops at a blank line, so
    /// a comment separated from the item by an empty line is not part of
    /// its doc comment. It also stops at a shebang (`#!`) line and at a line
    /// with anything but a comment on it, so trailing comments such as the
    /// one in `FOO = 1 # x` and comments continuing a previous line with a
    /// backslash are not included. Indented comment lines are included.
    ///
    /// Each line is returned without its leading `#` characters, one space
    /// following them and trailing whitespace.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "# Not this\n\n## Build it\n#   indented\nall:\n".parse().unwrap();
    /// let item = makefile.items().next().unwrap();
    /// assert_eq!(item.doc_comments().collect::<Vec<_>>(), vec!["Build it", "  indented"]);
    /// assert_eq!(
    ///     item.preceding_comments().collect::<Vec<_>>(),
    ///     vec!["Not this", "# Build it", "  indented"]
    /// );
    /// ```
    pub fn doc_comments(&self) -> impl Iterator<Item = String> {
        let mut lines: Vec<_> = doc_comment_lines(self.syntax())
            .into_iter()
            .filter_map(|line| line.comment)
            .map(|comment| {
                let text = comment.text().trim_start_matches('#');
                text.strip_prefix(' ')
                    .unwrap_or(text)
                    .trim_end()
                    .to_string()
            })
            .collect();
        lines.reverse();
        lines.into_iter()
    }

    /// Remove all preceding comments for this MakefileItem
    ///
    /// The comment lines found by [`Self::preceding_comments`] are removed;
    /// blank lines between them are kept. Returns the number of comments
    /// removed.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "# Comment 1\n# Comment 2\nVAR = value\n".parse().unwrap();
    /// let mut item = makefile.items().next().unwrap();
    /// let count = item.remove_comments().unwrap();
    /// assert_eq!(count, 2);
    /// assert!(!makefile.to_string().contains("# Comment"));
    /// ```
    pub fn remove_comments(&mut self) -> Result<usize, Error> {
        self.get_parent_or_error("remove comments from", "remove_comments")?;
        let lines: Vec<_> = lines_above(self.syntax())
            .into_iter()
            .filter(|line| line.comment.is_some())
            .collect();
        let count = lines.len();
        detach_tokens(lines.into_iter().flat_map(|line| line.tokens));
        Ok(count)
    }

    /// Modify the first preceding comment for this MakefileItem
    ///
    /// Returns `true` if a comment was found and modified, `false` if no comment exists.
    /// The comment text should not include the leading '#' character.
    /// Returns an error if the text can not be written as a single comment
    /// line, e.g. because it contains a newline.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "# Old comment\nVAR = value\n".parse().unwrap();
    /// let mut item = makefile.items().next().unwrap();
    /// let modified = item.modify_comment("New comment").unwrap();
    /// assert!(modified);
    /// assert!(makefile.to_string().contains("# New comment"));
    /// assert!(!makefile.to_string().contains("# Old comment"));
    /// ```
    pub fn modify_comment(&mut self, new_comment_text: &str) -> Result<bool, Error> {
        self.get_parent_or_error("modify comment for", "modify_comment")?;
        let (new_comment_token, _) = Self::parse_comment_tokens(
            new_comment_text,
            &line_ending(self.syntax()),
            "modify_comment",
        )?;

        // The comment closest to the item
        let Some(comment) = self.preceding_comment_tokens().into_iter().next() else {
            return Ok(false);
        };
        let parent = comment.parent().expect("comment has a parent");
        let idx = comment.index();
        parent.splice_children(
            idx..idx + 1,
            vec![rowan::NodeOrToken::Token(new_comment_token)],
        );
        Ok(true)
    }

    /// Insert a new MakefileItem before this item
    ///
    /// This inserts the new item immediately before the current item in the makefile.
    /// The new item is inserted at the same level as the current item. If
    /// the current item has comment lines directly above it, with no blank
    /// line in between, the new item is inserted before them, since they
    /// document the current item.
    ///
    /// Returns an error if the item would separate a [`MakefileItem::Recipe`]
    /// from the rule it belongs to, or if the new item is a
    /// [`MakefileItem::Recipe`] that would not be next to another one.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let mut makefile: Makefile = "VAR1 = first\nVAR2 = second\n".parse().unwrap();
    /// let temp: Makefile = "VAR_NEW = inserted\n".parse().unwrap();
    /// let new_var = temp.variable_definitions().next().unwrap();
    /// let mut second_item = makefile.items().nth(1).unwrap();
    /// second_item.insert_before(MakefileItem::Variable(new_var)).unwrap();
    /// let result = makefile.to_string();
    /// assert!(result.contains("VAR1 = first\nVAR_NEW = inserted\nVAR2 = second"));
    /// ```
    pub fn insert_before(&mut self, new_item: MakefileItem) -> Result<(), Error> {
        let parent = self.get_parent_or_error("insert before", "insert_before")?;
        check_position(
            new_item.syntax(),
            self.syntax().prev_sibling(),
            Some(self.syntax().clone()),
            None,
            "insert_before",
        )?;
        let current_index = index_before_doc_comment(self.syntax());
        let new_node = with_trailing_newline(new_item.syntax(), &line_ending(&parent));
        let new_node = with_recipe_prefix(&new_node, &text_before(&parent, current_index));

        parent.splice_children(current_index..current_index, vec![new_node.into()]);

        Ok(())
    }

    /// Insert a new MakefileItem after this item
    ///
    /// This inserts the new item immediately after the current item in the makefile.
    /// The new item is inserted at the same level as the current item, and
    /// before any comment lines documenting the next item.
    ///
    /// Returns an error if the new item can not go there, as described for
    /// [`Self::insert_before`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let mut makefile: Makefile = "VAR1 = first\nVAR2 = second\n".parse().unwrap();
    /// let temp: Makefile = "VAR_NEW = inserted\n".parse().unwrap();
    /// let new_var = temp.variable_definitions().next().unwrap();
    /// let mut first_item = makefile.items().next().unwrap();
    /// first_item.insert_after(MakefileItem::Variable(new_var)).unwrap();
    /// let result = makefile.to_string();
    /// assert!(result.contains("VAR1 = first\nVAR_NEW = inserted\nVAR2 = second"));
    /// ```
    pub fn insert_after(&mut self, new_item: MakefileItem) -> Result<(), Error> {
        let parent = self.get_parent_or_error("insert after", "insert_after")?;
        check_position(
            new_item.syntax(),
            Some(self.syntax().clone()),
            self.syntax().next_sibling(),
            None,
            "insert_after",
        )?;
        let eol = line_ending(&parent);
        let new_node = with_trailing_newline(new_item.syntax(), &eol);
        let index = terminate_line_before(&parent, index_after(self.syntax()), &eol);
        let new_node = with_recipe_prefix(&new_node, &text_before(&parent, index));

        // Insert the new item after the current item
        parent.splice_children(index..index, vec![new_node.into()]);

        Ok(())
    }
}

/// Check that `new` can go between the items `prev` and `next`, in place of
/// `replaced` if given.
///
/// A recipe line outside a rule belongs to the rule before it, so a new one
/// has to go next to another such recipe line, and anything else put before
/// one would separate it from its rule.
fn check_position(
    new: &SyntaxNode,
    prev: Option<SyntaxNode>,
    next: Option<SyntaxNode>,
    replaced: Option<&SyntaxNode>,
    method: &str,
) -> Result<(), Error> {
    let is_recipe = |node: Option<&SyntaxNode>| node.is_some_and(|n| n.kind() == RECIPE);
    let message = if new.kind() == RECIPE {
        if is_recipe(prev.as_ref()) || is_recipe(next.as_ref()) || is_recipe(replaced) {
            return Ok(());
        }
        "A recipe line can only go next to another recipe line"
    } else if is_recipe(next.as_ref()) {
        "Cannot put an item before a recipe line, which would no longer belong to its rule"
    } else {
        return Ok(());
    };
    Err(Error::Parse(ParseError {
        errors: vec![ErrorInfo {
            kind: crate::ParseErrorKind::Other,
            message: message.to_string(),
            line: 1,
            context: format!("MakefileItem::{method}"),
        }],
    }))
}

/// The index in the parent of `node` just after it. A comment that the
/// parser put at the end of `node` but that documents the next item is moved
/// out of `node` first, so that it stays with that item.
fn index_after(node: &SyntaxNode) -> usize {
    if let Some(next) = node.next_sibling() {
        index_before_doc_comment(&next);
    }
    node.index() + 1
}

// Internal trait for extracting specific item types from MakefileItem
trait ExtractFromItem: Sized {
    fn extract(item: MakefileItem) -> Option<Self>;
}

impl ExtractFromItem for Rule {
    fn extract(item: MakefileItem) -> Option<Self> {
        match item {
            MakefileItem::Rule(r) => Some(r),
            _ => None,
        }
    }
}

impl ExtractFromItem for VariableDefinition {
    fn extract(item: MakefileItem) -> Option<Self> {
        match item {
            MakefileItem::Variable(v) => Some(v),
            _ => None,
        }
    }
}

impl ExtractFromItem for Include {
    fn extract(item: MakefileItem) -> Option<Self> {
        match item {
            MakefileItem::Include(i) => Some(i),
            _ => None,
        }
    }
}

impl ExtractFromItem for Conditional {
    fn extract(item: MakefileItem) -> Option<Self> {
        match item {
            MakefileItem::Conditional(c) => Some(c),
            _ => None,
        }
    }
}

impl ExtractFromItem for Recipe {
    fn extract(item: MakefileItem) -> Option<Self> {
        match item {
            MakefileItem::Recipe(r) => Some(r),
            _ => None,
        }
    }
}

impl ExtractFromItem for Vpath {
    fn extract(item: MakefileItem) -> Option<Self> {
        match item {
            MakefileItem::Vpath(v) => Some(v),
            _ => None,
        }
    }
}

impl ExtractFromItem for ExpressionStatement {
    fn extract(item: MakefileItem) -> Option<Self> {
        match item {
            MakefileItem::ExpressionStatement(e) => Some(e),
            _ => None,
        }
    }
}

// Internal stack-based iterator for recursively collecting items from conditionals
struct RecursiveItemsIter<T> {
    stack: VecDeque<MakefileItem>,
    _phantom: std::marker::PhantomData<T>,
}

impl<T> RecursiveItemsIter<T> {
    fn new(items: impl Iterator<Item = MakefileItem>) -> Self {
        Self {
            stack: items.collect(),
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T: ExtractFromItem> Iterator for RecursiveItemsIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.stack.pop_front() {
            let children: Vec<_> = match item {
                MakefileItem::Conditional(ref cond) => {
                    cond.if_items().chain(cond.else_items()).collect()
                }
                MakefileItem::ForLoop(ref f) => f.items().collect(),
                // Conditionals and loops in a rule's recipe can also contain
                // non-recipe items, such as variables or other rules.
                MakefileItem::Rule(ref rule) => rule
                    .syntax()
                    .children()
                    .filter_map(MakefileItem::cast)
                    .collect(),
                _ => Vec::new(),
            };
            // Prepend the nested items so they are yielded before any items
            // following their parent, preserving document order
            for child in children.into_iter().rev() {
                self.stack.push_front(child);
            }
            if let Some(extracted) = T::extract(item) {
                return Some(extracted);
            }
        }
        None
    }
}

/// Iterator over blocks of consecutive comment lines in a makefile.
struct CommentBlockIter {
    elements: Vec<rowan::NodeOrToken<SyntaxNode, rowan::SyntaxToken<crate::lossless::Lang>>>,
    pos: usize,
}

impl CommentBlockIter {
    fn new(root: &SyntaxNode) -> Self {
        Self {
            elements: root.children_with_tokens().collect(),
            pos: 0,
        }
    }
}

impl Iterator for CommentBlockIter {
    type Item = rowan::TextRange;

    fn next(&mut self) -> Option<Self::Item> {
        // Find the start of the next comment
        while self.pos < self.elements.len() {
            if let Some(token) = self.elements[self.pos].as_token() {
                if token.kind() == COMMENT {
                    break;
                }
            }
            self.pos += 1;
        }

        if self.pos >= self.elements.len() {
            return None;
        }

        let block_start = self.elements[self.pos]
            .as_token()
            .unwrap()
            .text_range()
            .start();
        let mut block_end = self.elements[self.pos]
            .as_token()
            .unwrap()
            .text_range()
            .end();
        let mut comment_count = 1;
        self.pos += 1;

        // Extend the block through consecutive comments (with whitespace/newlines/blank lines between)
        while self.pos < self.elements.len() {
            match &self.elements[self.pos] {
                rowan::NodeOrToken::Token(token)
                    if token.kind() == NEWLINE || token.kind() == WHITESPACE =>
                {
                    self.pos += 1;
                }
                rowan::NodeOrToken::Node(node) if node.kind() == BLANK_LINE => {
                    self.pos += 1;
                }
                rowan::NodeOrToken::Token(token) if token.kind() == COMMENT => {
                    block_end = token.text_range().end();
                    comment_count += 1;
                    self.pos += 1;
                }
                _ => break,
            }
        }

        // Only return blocks with 2+ comment lines
        if comment_count >= 2 {
            Some(rowan::TextRange::new(block_start, block_end))
        } else {
            // Single comment line — skip it and try next
            self.next()
        }
    }
}

impl Makefile {
    /// Create a new empty makefile
    pub fn new() -> Makefile {
        let mut builder = GreenNodeBuilder::new();

        builder.start_node(ROOT.into());
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        Makefile::cast(syntax).unwrap()
    }

    /// Parse makefile text, returning a Parse result
    ///
    /// Both GNU make and BSD make syntax are accepted. Use
    /// [`Self::parse_with_variant`] to restrict parsing to a single variant.
    ///
    /// Variable references end where they do in GNU make, at the matching
    /// closing parenthesis or brace. BSD make instead ends them where their
    /// modifiers end, so that `${X:S,},x,}` is a single reference and the
    /// `$` in `${X:S/$/x/}` does not start a nested reference; parse with
    /// [`MakefileVariant::BSDMake`] to get those boundaries.
    pub fn parse(text: &str) -> crate::Parse<Makefile> {
        crate::Parse::<Makefile>::parse_makefile(text)
    }

    /// Parse makefile text written for a specific make variant
    ///
    /// Directives of other variants are not recognized; for example, with
    /// [`MakefileVariant::BSDMake`] a line starting with `ifdef` is not a
    /// conditional.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let parsed = Makefile::parse_with_variant(
    ///     ".if defined(DEBUG)\nCFLAGS+= -g\n.endif\n",
    ///     MakefileVariant::BSDMake,
    /// );
    /// assert!(parsed.ok());
    /// let makefile = parsed.tree();
    /// let cond = makefile.conditionals().next().unwrap();
    /// assert_eq!(cond.conditional_type(), Some(".if".to_string()));
    /// ```
    pub fn parse_with_variant(text: &str, variant: MakefileVariant) -> crate::Parse<Makefile> {
        crate::Parse::<Makefile>::parse_makefile_with_variant(text, variant)
    }

    /// Get the text content of the makefile
    pub fn code(&self) -> String {
        self.syntax().text().to_string()
    }

    /// Check if this node is the root of a makefile
    pub fn is_root(&self) -> bool {
        self.syntax().kind() == ROOT
    }

    /// Read a makefile from a reader
    pub fn read<R: std::io::Read>(mut r: R) -> Result<Makefile, Error> {
        let mut buf = String::new();
        r.read_to_string(&mut buf)?;
        buf.parse()
    }

    /// Read makefile from a reader, but allow syntax errors
    pub fn read_relaxed<R: std::io::Read>(mut r: R) -> Result<Makefile, Error> {
        let mut buf = String::new();
        r.read_to_string(&mut buf)?;

        let parsed = parse(&buf, None);
        Ok(parsed.root())
    }

    /// Parse a makefile from a string, allowing syntax errors.
    ///
    /// Returns the parsed makefile and a list of errors. The makefile tree is
    /// always returned, even if there are parse errors, enabling error-resilient
    /// tooling that can work with partial or invalid input.
    pub fn from_str_relaxed(s: &str) -> (Self, Vec<ErrorInfo>) {
        let parsed = parse(s, None);
        (parsed.root(), parsed.errors)
    }

    /// Read a makefile from a file path, allowing syntax errors.
    ///
    /// Returns the parsed makefile and a list of errors.
    pub fn from_file_relaxed(
        path: impl AsRef<std::path::Path>,
    ) -> Result<(Self, Vec<ErrorInfo>), std::io::Error> {
        let text = std::fs::read_to_string(path)?;
        Ok(Self::from_str_relaxed(&text))
    }

    /// Retrieve the rules in the makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "rule: dependency\n\tcommand\n".parse().unwrap();
    /// assert_eq!(makefile.rules().count(), 1);
    /// ```
    pub fn rules(&self) -> impl Iterator<Item = Rule> + '_ {
        RecursiveItemsIter::new(self.items())
    }

    /// Get all rules that have a specific target
    pub fn rules_by_target<'a>(&'a self, target: &'a str) -> impl Iterator<Item = Rule> + 'a {
        self.rules()
            .filter(move |rule| rule.targets().any(|t| t == target))
    }

    /// Get all variable definitions in the makefile
    pub fn variable_definitions(&self) -> impl Iterator<Item = VariableDefinition> + '_ {
        RecursiveItemsIter::new(self.items())
    }

    /// Get all conditionals in the makefile (top-level only)
    ///
    /// Use [`Makefile::all_conditionals`] to also get nested conditionals
    /// and conditionals in rule bodies.
    pub fn conditionals(&self) -> impl Iterator<Item = Conditional> + '_ {
        self.items().filter_map(|item| match item {
            MakefileItem::Conditional(c) => Some(c),
            _ => None,
        })
    }

    /// Get all conditionals in the makefile at any depth, in source order.
    ///
    /// Unlike [`Makefile::conditionals`], this includes conditionals nested
    /// in other conditionals or BSD make `.for` loops, and conditionals in
    /// rule bodies. An outer conditional comes before the conditionals
    /// nested in it.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile =
    ///     "ifdef A\nifdef B\nX = 1\nendif\nendif\nall:\nifdef C\n\techo c\nendif\n"
    ///         .parse()
    ///         .unwrap();
    /// assert_eq!(makefile.conditionals().count(), 1);
    /// let conditions: Vec<_> = makefile
    ///     .all_conditionals()
    ///     .map(|c| c.condition().unwrap())
    ///     .collect();
    /// assert_eq!(conditions, vec!["A", "B", "C"]);
    /// ```
    pub fn all_conditionals(&self) -> impl Iterator<Item = Conditional> + '_ {
        RecursiveItemsIter::new(self.items())
    }

    /// Get all recipe lines in the makefile, in source order.
    ///
    /// Like [`Rule::recipe_nodes`], this includes recipe lines in
    /// conditionals and BSD make `.for` loops in rule bodies. It also
    /// includes recipe lines that are not part of any rule: indented lines
    /// before the first rule (a parse error) and lines returned as
    /// [`MakefileItem::Recipe`], such as a recipe line after a conditional
    /// whose branches all end in rule context.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "a:\n\techo a\nifdef X\nb:\n\techo b\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let texts: Vec<_> = makefile.recipe_nodes().map(|r| r.text()).collect();
    /// assert_eq!(texts, vec!["echo a", "echo b"]);
    /// ```
    pub fn recipe_nodes(&self) -> impl Iterator<Item = Recipe> + '_ {
        RecursiveItemsIter::new(self.items())
    }

    /// Get all `vpath` directives in the makefile, including those in
    /// conditionals, in source order.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "vpath %.c src\nifdef X\nvpath %.h include\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let patterns: Vec<_> = makefile.vpaths().map(|v| v.pattern()).collect();
    /// assert_eq!(patterns, vec![Some("%.c".to_string()), Some("%.h".to_string())]);
    /// ```
    pub fn vpaths(&self) -> impl Iterator<Item = Vpath> + '_ {
        RecursiveItemsIter::new(self.items())
    }

    /// Get all expression statements (lines of only references or function
    /// calls, such as `$(eval ...)`) in the makefile, including those in
    /// conditionals, in source order.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "$(info a)\nifdef X\n$(eval $(call f,x))\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let exprs: Vec<_> = makefile.expression_statements().map(|e| e.expression()).collect();
    /// assert_eq!(exprs, vec!["$(info a)", "$(eval $(call f,x))"]);
    /// ```
    pub fn expression_statements(&self) -> impl Iterator<Item = ExpressionStatement> + '_ {
        RecursiveItemsIter::new(self.items())
    }

    /// Get all top-level items (rules, variables, includes, conditionals) in the makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let makefile: Makefile = r#"VAR = value
    /// ifdef DEBUG
    /// CFLAGS = -g
    /// endif
    /// rule:
    /// 	command
    /// "#.parse().unwrap();
    /// let items: Vec<_> = makefile.items().collect();
    /// assert_eq!(items.len(), 3); // VAR, conditional, rule
    /// ```
    pub fn items(&self) -> impl Iterator<Item = MakefileItem> + '_ {
        self.syntax().children().filter_map(MakefileItem::cast)
    }

    /// Find all variables by name
    ///
    /// Returns an iterator over all variable definitions with the given name.
    /// Makefiles can have multiple definitions of the same variable.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "VAR1 = value1\nVAR2 = value2\nVAR1 = value3\n".parse().unwrap();
    /// let vars: Vec<_> = makefile.find_variable("VAR1").collect();
    /// assert_eq!(vars.len(), 2);
    /// assert_eq!(vars[0].raw_value(), Some("value1".to_string()));
    /// assert_eq!(vars[1].raw_value(), Some("value3".to_string()));
    /// ```
    pub fn find_variable<'a>(
        &'a self,
        name: &'a str,
    ) -> impl Iterator<Item = VariableDefinition> + 'a {
        self.variable_definitions()
            .filter(move |var| var.name().as_deref() == Some(name))
    }

    /// Get all variable references in the makefile.
    ///
    /// Walks the entire syntax tree to find all references, such as `$(VAR)`,
    /// `${VAR}`, `$@` and function calls, in variable values including
    /// `define` bodies, prerequisites, targets and recipes. References nested
    /// in others are included, after the one containing them. A `$$` is not
    /// a reference.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "CFLAGS = $(BASE_FLAGS) -Wall\nall: $(TARGETS)\n".parse().unwrap();
    /// let refs: Vec<_> = makefile.variable_references().collect();
    /// let names: Vec<_> = refs.iter().filter_map(|r| r.name()).collect();
    /// assert!(names.contains(&"BASE_FLAGS".to_string()));
    /// assert!(names.contains(&"TARGETS".to_string()));
    /// ```
    pub fn variable_references(&self) -> impl Iterator<Item = VariableReference> + '_ {
        self.syntax()
            .descendants()
            .filter_map(VariableReference::cast)
    }

    /// Get all top-level items that overlap with the given text range.
    ///
    /// Since items are stored in document order, this skips items entirely
    /// before the range and stops once past it.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "CC = gcc\nall: build\n\techo done\n".parse().unwrap();
    /// let range = TextRange::new(0.into(), 8.into());
    /// let items: Vec<_> = makefile.items_in_range(range).collect();
    /// assert_eq!(items.len(), 1);
    /// ```
    pub fn items_in_range(
        &self,
        range: rowan::TextRange,
    ) -> impl Iterator<Item = MakefileItem> + '_ {
        self.items()
            .skip_while(move |item| item.syntax().text_range().end() <= range.start())
            .take_while(move |item| item.syntax().text_range().start() < range.end())
    }

    /// Get all variable references that overlap with the given text range.
    ///
    /// Only walks descendants of top-level items that overlap the range,
    /// rather than scanning the entire tree.
    pub fn variable_references_in_range(
        &self,
        range: rowan::TextRange,
    ) -> impl Iterator<Item = VariableReference> + '_ {
        self.items_in_range(range).flat_map(|item| {
            item.syntax()
                .descendants()
                .filter_map(VariableReference::cast)
                .collect::<Vec<_>>()
        })
    }

    /// Get all rules that overlap with the given text range.
    pub fn rules_in_range(&self, range: rowan::TextRange) -> impl Iterator<Item = Rule> + '_ {
        self.items_in_range(range).filter_map(|item| match item {
            MakefileItem::Rule(r) => Some(r),
            _ => None,
        })
    }

    /// Get all variable definitions that overlap with the given text range.
    pub fn variable_definitions_in_range(
        &self,
        range: rowan::TextRange,
    ) -> impl Iterator<Item = VariableDefinition> + '_ {
        self.items_in_range(range).filter_map(|item| match item {
            MakefileItem::Variable(v) => Some(v),
            _ => None,
        })
    }

    /// Get all blocks of consecutive comment lines in the makefile.
    ///
    /// Returns the text range of each block. A comment block is two or more
    /// consecutive comment lines (separated only by whitespace or blank lines).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "# line 1\n# line 2\n# line 3\nall:\n\techo done\n".parse().unwrap();
    /// let blocks: Vec<_> = makefile.comment_blocks().collect();
    /// assert_eq!(blocks.len(), 1);
    /// ```
    pub fn comment_blocks(&self) -> impl Iterator<Item = rowan::TextRange> + '_ {
        CommentBlockIter::new(self.syntax())
    }

    /// Get the ranges of all comments in the makefile, in source order.
    ///
    /// This includes whole-line comments, trailing comments such as the one
    /// in `FOO = 1 # x`, comments in conditional directive lines and a
    /// shebang line. It also includes recipe lines and lines in `define`
    /// bodies that start with `#`, although GNU make expands those and
    /// passes them on rather than treating them as comments; a range covers
    /// the references in such a line. A `#` elsewhere in a recipe
    /// line, as in `echo # x`, is not included. Each range starts at the
    /// `#` and ends before the line ending, after any lines the comment is
    /// continued onto with a backslash.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "# a\nFOO = 1 # b\nall:\n\techo # c\n".parse().unwrap();
    /// let ranges: Vec<_> = makefile.comment_ranges().collect();
    /// assert_eq!(
    ///     ranges,
    ///     vec![TextRange::new(0.into(), 3.into()), TextRange::new(12.into(), 15.into())]
    /// );
    /// ```
    pub fn comment_ranges(&self) -> impl Iterator<Item = rowan::TextRange> + '_ {
        self.syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == COMMENT)
            .filter_map(|t| crate::lossless::comment_elements(&t))
            .filter_map(|elements| {
                let first = elements.first()?.text_range();
                Some(first.cover(elements.last()?.text_range()))
            })
    }

    /// Add a new rule to the makefile
    ///
    /// The target is escaped as by [`Rule::set_targets`]. The rule is
    /// separated from any preceding content by a blank line, unless the
    /// makefile already ends in one.
    ///
    /// # Panics
    ///
    /// Panics if `target` can not be written as a single target that reads
    /// back the same. Use [`Makefile::try_add_rule`] to get an error instead.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile = Makefile::new();
    /// makefile.add_rule("rule");
    /// assert_eq!(makefile.to_string(), "rule:\n");
    /// ```
    pub fn add_rule(&mut self, target: &str) -> Rule {
        self.try_add_rule(target)
            .unwrap_or_else(|e| panic!("invalid target: {e}"))
    }

    /// Add a new rule to the makefile, like [`Makefile::add_rule`]
    ///
    /// Returns an error, leaving the makefile unchanged, if `target` can
    /// not be written as a single target that reads back the same, such as
    /// one containing whitespace or a `:`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile = Makefile::new();
    /// makefile.try_add_rule("a#b").unwrap();
    /// assert!(makefile.try_add_rule("a b").is_err());
    /// assert_eq!(makefile.to_string(), "a\\#b:\n");
    /// ```
    pub fn try_add_rule(&mut self, target: &str) -> Result<Rule, Error> {
        let eol = line_ending(self.syntax());
        let targets = build_targets_node(&[target.to_string()], "add_rule")?;
        let syntax = SyntaxNode::new_root_mut(rowan::GreenNode::new(
            RULE.into(),
            [
                targets.green().into_owned().into(),
                rowan::GreenToken::new(OPERATOR.into(), ":").into(),
                rowan::GreenNode::new(PREREQUISITES.into(), []).into(),
                rowan::GreenToken::new(NEWLINE.into(), &eol).into(),
            ],
        ));
        append_with_blank_line(self.syntax(), syntax, &eol);

        // Use children().count() - 1 to get the last added child node
        // (not children_with_tokens().count() which includes tokens)
        Ok(Rule::cast(self.syntax().children().last().unwrap()).unwrap())
    }

    /// Add a new conditional to the makefile
    ///
    /// The conditional is separated from any preceding content by a blank
    /// line, unless the makefile already ends in one. The bodies are parsed
    /// as makefile text.
    ///
    /// Returns an error if the condition is invalid, as in `ifeq ()`, or if
    /// a body does not read back as part of its branch, for example because
    /// it contains an `else` or `endif` line. The condition is checked as
    /// the make the conditional type belongs to would: GNU make accepts
    /// `ifdef` and `ifndef` without a variable name, testing a variable
    /// with an empty name that is never defined, while BSD make rejects an
    /// empty condition for each of its conditional types.
    ///
    /// # Arguments
    /// * `conditional_type` - The type of conditional: "ifdef", "ifndef", "ifeq", or "ifneq",
    ///   or for BSD make ".if", ".ifdef", ".ifndef", ".ifmake" or ".ifnmake"
    /// * `condition` - The condition expression (e.g., "DEBUG" for ifdef/ifndef, or "(a,b)" for ifeq/ifneq)
    /// * `if_body` - The content of the if branch
    /// * `else_body` - Optional content for the else branch
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile = Makefile::new();
    /// makefile.add_conditional("ifdef", "DEBUG", "VAR = debug\n", None);
    /// assert!(makefile.to_string().contains("ifdef DEBUG"));
    /// ```
    pub fn add_conditional(
        &mut self,
        conditional_type: &str,
        condition: &str,
        if_body: &str,
        else_body: Option<&str>,
    ) -> Result<Conditional, Error> {
        // Validate conditional type
        let Some((else_keyword, endif_keyword)) = conditional_keywords(conditional_type) else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
 kind: crate::ParseErrorKind::Other,
                    message: format!(
                        "Invalid conditional type: {}. Must be one of: ifdef, ifndef, ifeq, ifneq, .if, .ifdef, .ifndef, .ifmake, .ifnmake",
                        conditional_type
                    ),
                    line: 1,
                    context: "add_conditional".to_string(),
                }],
            }));
        };
        check_conditional(
            (conditional_type, else_keyword, endif_keyword),
            condition,
            if_body,
            else_body,
            "add_conditional",
        )?;

        let eol = line_ending(self.syntax());
        let syntax = build_conditional(
            &conditional_if_line(conditional_type, condition),
            if_body,
            else_body.map(|body| (else_keyword, body)),
            endif_keyword,
            &eol,
            "add_conditional",
        )?;
        append_with_blank_line(self.syntax(), syntax, &eol);

        Ok(Conditional::cast(self.syntax().children().last().unwrap()).unwrap())
    }

    /// Add a new conditional to the makefile with typed items
    ///
    /// This is a more type-safe alternative to `add_conditional` that accepts iterators of
    /// `MakefileItem` instead of raw strings. Blank lines and errors are
    /// handled as by [`Makefile::add_conditional`].
    ///
    /// # Arguments
    /// * `conditional_type` - The type of conditional: "ifdef", "ifndef", "ifeq", or "ifneq",
    ///   or for BSD make ".if", ".ifdef", ".ifndef", ".ifmake" or ".ifnmake"
    /// * `condition` - The condition expression (e.g., "DEBUG" for ifdef/ifndef, or "(a,b)" for ifeq/ifneq)
    /// * `if_items` - Items for the if branch
    /// * `else_items` - Optional items for the else branch
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let mut makefile = Makefile::new();
    /// let temp1: Makefile = "CFLAGS = -g\n".parse().unwrap();
    /// let var1 = temp1.variable_definitions().next().unwrap();
    /// let temp2: Makefile = "CFLAGS = -O2\n".parse().unwrap();
    /// let var2 = temp2.variable_definitions().next().unwrap();
    /// makefile.add_conditional_with_items(
    ///     "ifdef",
    ///     "DEBUG",
    ///     vec![MakefileItem::Variable(var1)],
    ///     Some(vec![MakefileItem::Variable(var2)])
    /// ).unwrap();
    /// assert!(makefile.to_string().contains("ifdef DEBUG"));
    /// assert!(makefile.to_string().contains("CFLAGS = -g"));
    /// assert!(makefile.to_string().contains("CFLAGS = -O2"));
    /// ```
    pub fn add_conditional_with_items<I1, I2>(
        &mut self,
        conditional_type: &str,
        condition: &str,
        if_items: I1,
        else_items: Option<I2>,
    ) -> Result<Conditional, Error>
    where
        I1: IntoIterator<Item = MakefileItem>,
        I2: IntoIterator<Item = MakefileItem>,
    {
        // Validate conditional type
        let Some((else_keyword, endif_keyword)) = conditional_keywords(conditional_type) else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
 kind: crate::ParseErrorKind::Other,
                    message: format!(
                        "Invalid conditional type: {}. Must be one of: ifdef, ifndef, ifeq, ifneq, .if, .ifdef, .ifndef, .ifmake, .ifnmake",
                        conditional_type
                    ),
                    line: 1,
                    context: "add_conditional_with_items".to_string(),
                }],
            }));
        };
        // Items can't start another branch, so only the condition needs
        // checking.
        check_conditional(
            (conditional_type, else_keyword, endif_keyword),
            condition,
            "",
            else_items.as_ref().map(|_| ""),
            "add_conditional_with_items",
        )?;

        let eol = line_ending(self.syntax());
        // Each item on its own lines, even one without a final newline
        let item_text = |item: MakefileItem| {
            // The body is parsed on its own, where recipe lines start with
            // a tab; they get the prefix of the makefile when it is added.
            with_recipe_prefix(&with_trailing_newline(item.syntax(), "\n"), "").to_string()
        };
        let if_text: String = if_items.into_iter().map(item_text).collect();
        let else_text: Option<String> =
            else_items.map(|items| items.into_iter().map(item_text).collect());
        let syntax = build_conditional(
            &conditional_if_line(conditional_type, condition),
            &if_text,
            else_text.as_deref().map(|text| (else_keyword, text)),
            endif_keyword,
            &eol,
            "add_conditional_with_items",
        )?;
        append_with_blank_line(self.syntax(), syntax, &eol);

        Ok(Conditional::cast(self.syntax().children().last().unwrap()).unwrap())
    }

    /// Read the makefile
    pub fn from_reader<R: std::io::Read>(mut r: R) -> Result<Makefile, Error> {
        let mut buf = String::new();
        r.read_to_string(&mut buf)?;

        let parsed = parse(&buf, None);
        if !parsed.errors.is_empty() {
            Err(Error::Parse(ParseError {
                errors: parsed.errors,
            }))
        } else {
            Ok(parsed.root())
        }
    }

    /// Replace rule at given index with a new rule
    ///
    /// `index` is a position in [`Makefile::rules`], so it can refer to a
    /// rule inside a conditional or loop.
    ///
    /// Comments above the rule are kept.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
    /// let new_rule: makefile_lossless::Rule = "new_rule:\n\tnew_command\n".parse().unwrap();
    /// makefile.replace_rule(0, new_rule).unwrap();
    /// assert!(makefile.rules().any(|r| r.targets().any(|t| t == "new_rule")));
    /// ```
    pub fn replace_rule(&mut self, index: usize, new_rule: Rule) -> Result<(), Error> {
        let rules: Vec<_> = self.rules().map(|r| r.syntax().clone()).collect();

        if rules.is_empty() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: "Cannot replace rule in empty makefile".to_string(),
                    line: 1,
                    context: "replace_rule".to_string(),
                }],
            }));
        }

        if index >= rules.len() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: format!(
                        "Rule index {} out of bounds (max {})",
                        index,
                        rules.len() - 1
                    ),
                    line: 1,
                    context: "replace_rule".to_string(),
                }],
            }));
        }

        let target_node = &rules[index];
        let target_index = target_node.index();
        let parent = target_node.parent().unwrap();

        let new_node = with_trailing_newline(new_rule.syntax(), &line_ending(self.syntax()));
        let new_node = with_recipe_prefix(&new_node, &text_before(&parent, target_index));

        parent.splice_children(target_index..target_index + 1, vec![new_node.into()]);
        Ok(())
    }

    /// Remove rule at given index
    ///
    /// `index` is a position in [`Makefile::rules`], so it can refer to a
    /// rule inside a conditional or loop.
    ///
    /// Comments above the rule are kept; [`Rule::remove`] removes them too.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
    /// let removed = makefile.remove_rule(0).unwrap();
    /// assert_eq!(removed.targets().collect::<Vec<_>>(), vec!["rule1"]);
    /// assert_eq!(makefile.rules().count(), 1);
    /// ```
    pub fn remove_rule(&mut self, index: usize) -> Result<Rule, Error> {
        let rules: Vec<_> = self.rules().map(|r| r.syntax().clone()).collect();

        if rules.is_empty() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: "Cannot remove rule from empty makefile".to_string(),
                    line: 1,
                    context: "remove_rule".to_string(),
                }],
            }));
        }

        if index >= rules.len() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: format!(
                        "Rule index {} out of bounds (max {})",
                        index,
                        rules.len() - 1
                    ),
                    line: 1,
                    context: "remove_rule".to_string(),
                }],
            }));
        }

        let target_node = rules[index].clone();
        let target_index = target_node.index();

        target_node
            .parent()
            .unwrap()
            .splice_children(target_index..target_index + 1, vec![]);
        Ok(Rule::cast(target_node).unwrap())
    }

    /// Insert rule at given position
    ///
    /// `index` is a position in [`Makefile::rules`], which includes rules
    /// inside conditionals and loops. The new rule is inserted directly
    /// before the rule at `index`, in the same conditional branch or loop
    /// body if that rule is in one, so that it applies under the same
    /// conditions. If `index` is `rules().count()`, the new rule is
    /// appended to the end of the makefile.
    ///
    /// If the rule at `index` has comment lines directly above it, with no
    /// blank line in between, the new rule is inserted before them, since
    /// they document the existing rule.
    ///
    /// The new rule is separated from any preceding content by a blank
    /// line, unless that content already ends in one or is the start of a
    /// conditional branch or loop body, and from the following rule by a
    /// blank line, unless the new rule already ends in one.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
    /// let new_rule: makefile_lossless::Rule = "inserted_rule:\n\tinserted_command\n".parse().unwrap();
    /// makefile.insert_rule(1, new_rule).unwrap();
    /// let targets: Vec<_> = makefile.rules().flat_map(|r| r.targets().collect::<Vec<_>>()).collect();
    /// assert_eq!(targets, vec!["rule1", "inserted_rule", "rule2"]);
    /// ```
    pub fn insert_rule(&mut self, index: usize, new_rule: Rule) -> Result<(), Error> {
        let rules: Vec<_> = self.rules().map(|r| r.syntax().clone()).collect();

        if index > rules.len() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: format!("Rule index {} out of bounds (max {})", index, rules.len()),
                    line: 1,
                    context: "insert_rule".to_string(),
                }],
            }));
        }

        let (parent, target_index) = match rules.get(index) {
            // Insert before the rule at the given index, and any comment
            // documenting it
            Some(rule) => (rule.parent().unwrap(), index_before_doc_comment(rule)),
            None => (
                self.syntax().clone(),
                self.syntax().children_with_tokens().count(),
            ),
        };

        // No blank line directly after a conditional or loop header
        let at_block_start = rules.get(index).is_some_and(|rule| {
            rule.prev_sibling()
                .is_some_and(|n| matches!(n.kind(), CONDITIONAL_IF | CONDITIONAL_ELSE | FOR_HEADER))
        });

        let eol = line_ending(self.syntax());
        let new_node = with_trailing_newline(new_rule.syntax(), &eol);
        let target_index = terminate_line_before(&parent, target_index, &eol);
        let new_node = with_recipe_prefix(&new_node, &text_before(&parent, target_index));

        let blank_line = || {
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), &eol);
            bl_builder.finish_node();
            SyntaxNode::new_root_mut(bl_builder.finish()).into()
        };
        let mut nodes_to_insert = Vec::new();
        if !at_block_start && needs_blank_line_before(&parent, target_index) {
            nodes_to_insert.push(blank_line());
        }
        let needs_blank_after = index < rules.len() && needs_blank_line_at_end(&new_node);
        nodes_to_insert.push(new_node.into());
        if needs_blank_after {
            nodes_to_insert.push(blank_line());
        }

        insert_items(&parent, target_index, nodes_to_insert);
        Ok(())
    }

    /// Get all include directives in the makefile, including those inside
    /// conditionals and loops
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include config.mk\nifdef DEBUG\n-include .env\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let includes = makefile.includes().collect::<Vec<_>>();
    /// assert_eq!(includes.len(), 2);
    /// ```
    pub fn includes(&self) -> impl Iterator<Item = Include> {
        RecursiveItemsIter::new(self.items())
    }

    /// Get the file paths of all include directives, as returned by
    /// [`Makefile::includes`]
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include config.mk\n-include .env\n".parse().unwrap();
    /// let paths = makefile.included_files().collect::<Vec<_>>();
    /// assert_eq!(paths, vec!["config.mk", ".env"]);
    /// ```
    pub fn included_files(&self) -> impl Iterator<Item = String> + '_ {
        // Skip includes without file names, such as a bare `include`.
        self.includes()
            .filter_map(|include| include.path())
            .filter(|path| !path.is_empty())
    }

    /// Find the first rule with a specific target name
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
    /// let rule = makefile.find_rule_by_target("rule2");
    /// assert!(rule.is_some());
    /// assert_eq!(rule.unwrap().targets().collect::<Vec<_>>(), vec!["rule2"]);
    /// ```
    pub fn find_rule_by_target(&self, target: &str) -> Option<Rule> {
        self.rules()
            .find(|rule| rule.targets().any(|t| t == target))
    }

    /// Find all rules with a specific target name
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "rule1:\n\tcommand1\nrule1:\n\tcommand2\nrule2:\n\tcommand3\n".parse().unwrap();
    /// let rules: Vec<_> = makefile.find_rules_by_target("rule1").collect();
    /// assert_eq!(rules.len(), 2);
    /// ```
    pub fn find_rules_by_target<'a>(&'a self, target: &'a str) -> impl Iterator<Item = Rule> + 'a {
        self.rules_by_target(target)
    }

    /// Find the first rule whose target matches the given pattern
    ///
    /// Supports make-style pattern matching where `%` in a rule's target acts as a wildcard.
    /// For example, a rule with target `%.o` will match `foo.o`, `bar.o`, etc.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
    /// let rule = makefile.find_rule_by_target_pattern("foo.o");
    /// assert!(rule.is_some());
    /// ```
    pub fn find_rule_by_target_pattern(&self, target: &str) -> Option<Rule> {
        self.rules()
            .find(|rule| rule.targets().any(|t| matches_pattern(&t, target)))
    }

    /// Find all rules whose targets match the given pattern
    ///
    /// Supports make-style pattern matching where `%` in a rule's target acts as a wildcard.
    /// For example, a rule with target `%.o` will match `foo.o`, `bar.o`, etc.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n%.o: %.s\n\t$(AS) -o $@ $<\n".parse().unwrap();
    /// let rules: Vec<_> = makefile.find_rules_by_target_pattern("foo.o").collect();
    /// assert_eq!(rules.len(), 2);
    /// ```
    pub fn find_rules_by_target_pattern<'a>(
        &'a self,
        target: &'a str,
    ) -> impl Iterator<Item = Rule> + 'a {
        self.rules()
            .filter(move |rule| rule.targets().any(|t| matches_pattern(&t, target)))
    }

    /// Add a target to .PHONY (creates .PHONY rule if it doesn't exist)
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile = Makefile::new();
    /// makefile.add_phony_target("clean").unwrap();
    /// assert!(makefile.is_phony("clean"));
    /// ```
    pub fn add_phony_target(&mut self, target: &str) -> Result<(), Error> {
        // Find existing .PHONY rule
        if let Some(mut phony_rule) = self.find_rule_by_target(".PHONY") {
            // Check if target is already in prerequisites
            if !phony_rule.prerequisites().any(|p| p == target) {
                phony_rule.add_prerequisite(target)?;
            }
        } else {
            // Create new .PHONY rule
            let mut phony_rule = self.add_rule(".PHONY");
            phony_rule.add_prerequisite(target)?;
        }
        Ok(())
    }

    /// Remove a target from .PHONY (removes .PHONY rule if it becomes empty)
    ///
    /// Returns `true` if the target was found and removed, `false` if it wasn't in .PHONY.
    /// If there are multiple .PHONY rules, it removes the target from the first rule that contains it.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = ".PHONY: clean test\n".parse().unwrap();
    /// assert!(makefile.remove_phony_target("clean").unwrap());
    /// assert!(!makefile.is_phony("clean"));
    /// assert!(makefile.is_phony("test"));
    /// ```
    pub fn remove_phony_target(&mut self, target: &str) -> Result<bool, Error> {
        // Find the first .PHONY rule that contains the target
        let mut phony_rule = None;
        for rule in self.rules_by_target(".PHONY") {
            if rule.prerequisites().any(|p| p == target) {
                phony_rule = Some(rule);
                break;
            }
        }

        let mut phony_rule = match phony_rule {
            Some(rule) => rule,
            None => return Ok(false),
        };

        // Count prerequisites before removal
        let prereq_count = phony_rule.prerequisites().count();

        // Remove the prerequisite
        phony_rule.remove_prerequisite(target)?;

        // Check if .PHONY has no more prerequisites, if so remove the rule
        if prereq_count == 1 {
            // We just removed the last prerequisite, so remove the entire rule
            phony_rule.remove()?;
        }

        Ok(true)
    }

    /// Check if a target is marked as phony
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".PHONY: clean test\n".parse().unwrap();
    /// assert!(makefile.is_phony("clean"));
    /// assert!(makefile.is_phony("test"));
    /// assert!(!makefile.is_phony("build"));
    /// ```
    pub fn is_phony(&self, target: &str) -> bool {
        // Check all .PHONY rules since there can be multiple
        self.rules_by_target(".PHONY")
            .any(|rule| rule.prerequisites().any(|p| p == target))
    }

    /// Get all phony targets
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".PHONY: clean test build\n".parse().unwrap();
    /// let phony_targets: Vec<_> = makefile.phony_targets().collect();
    /// assert_eq!(phony_targets, vec!["clean", "test", "build"]);
    /// ```
    pub fn phony_targets(&self) -> impl Iterator<Item = String> + '_ {
        // Collect from all .PHONY rules since there can be multiple
        self.rules_by_target(".PHONY")
            .flat_map(|rule| rule.prerequisites().collect::<Vec<_>>())
    }

    /// Add a new include directive at the beginning of the makefile
    ///
    /// # Arguments
    /// * `path` - The file path to include (e.g., "config.mk")
    ///
    /// `#` is escaped as needed, so that [`Include::path`] returns `path`.
    /// Returns an error if `path` can not be written in an include
    /// directive, such as a path containing a newline.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile = Makefile::new();
    /// makefile.add_include("config.mk").unwrap();
    /// assert_eq!(makefile.included_files().collect::<Vec<_>>(), vec!["config.mk"]);
    /// ```
    pub fn add_include(&mut self, path: &str) -> Result<Include, Error> {
        let syntax = Include::new(path, &line_ending(self.syntax()))?
            .syntax()
            .clone();

        // Insert at the beginning (position 0)
        self.syntax().splice_children(0..0, vec![syntax.into()]);

        // Return the newly added include (first child)
        Ok(Include::cast(self.syntax().children().next().unwrap()).unwrap())
    }

    /// Insert an include directive at a specific position
    ///
    /// `index` is a position in [`Makefile::items`], which only has top-level
    /// items: the include is inserted directly before the item at `index`,
    /// after any blank lines preceding it, or appended to the end of the
    /// makefile if `index` is `items().count()`. No blank lines are added
    /// around it. If the item at `index` has comment lines directly above
    /// it, with no blank line in between, the include is inserted before
    /// them, since they document that item.
    ///
    /// # Arguments
    /// * `index` - The position to insert at (0 = beginning, items().count() = end)
    /// * `path` - The file path to include (e.g., "config.mk")
    ///
    /// `#` is escaped as needed, so that [`Include::path`] returns `path`.
    /// Returns an error if `path` can not be written in an include
    /// directive, such as a path containing a newline.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "VAR = value\nrule:\n\tcommand\n".parse().unwrap();
    /// makefile.insert_include(1, "config.mk").unwrap();
    /// let items: Vec<_> = makefile.items().collect();
    /// assert_eq!(items.len(), 3); // VAR, include, rule
    /// ```
    pub fn insert_include(&mut self, index: usize, path: &str) -> Result<Include, Error> {
        let items: Vec<_> = self.items().collect();

        if index > items.len() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: format!("Index {} out of bounds (max {})", index, items.len()),
                    line: 1,
                    context: "insert_include".to_string(),
                }],
            }));
        }

        let eol = line_ending(self.syntax());
        let syntax = Include::new(path, &eol)?.syntax().clone();

        let target_index = match items.get(index) {
            // Insert before the item at the given index, and any comment
            // documenting it
            Some(item) => index_before_doc_comment(item.syntax()),
            None => self.syntax().children_with_tokens().count(),
        };

        let target_index = terminate_line_before(self.syntax(), target_index, &eol);
        self.syntax()
            .splice_children(target_index..target_index, vec![syntax.clone().into()]);

        Ok(Include::cast(syntax).unwrap())
    }

    /// Insert an include directive after a specific MakefileItem
    ///
    /// This is useful when you want to insert an include relative to another item in the makefile.
    /// `after` may be nested, e.g. in a conditional, in which case the include
    /// is inserted in the same branch.
    ///
    /// # Arguments
    /// * `after` - The MakefileItem to insert after
    /// * `path` - The file path to include (e.g., "config.mk")
    ///
    /// `#` is escaped as needed, so that [`Include::path`] returns `path`.
    /// Returns an error if `path` can not be written in an include
    /// directive, such as a path containing a newline.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "VAR1 = value1\nVAR2 = value2\n".parse().unwrap();
    /// let first_var = makefile.items().next().unwrap();
    /// makefile.insert_include_after(&first_var, "config.mk").unwrap();
    /// let paths: Vec<_> = makefile.included_files().collect();
    /// assert_eq!(paths, vec!["config.mk"]);
    /// ```
    pub fn insert_include_after(
        &mut self,
        after: &MakefileItem,
        path: &str,
    ) -> Result<Include, Error> {
        let after_syntax = after.syntax();
        let parent = after_syntax
            .parent()
            .filter(|_| after_syntax.ancestors().last().as_ref() == Some(self.syntax()))
            .ok_or_else(|| {
                Error::Parse(ParseError {
                    errors: vec![ErrorInfo {
                        kind: crate::ParseErrorKind::Other,
                        message: "Could not find the reference item".to_string(),
                        line: 1,
                        context: "insert_include_after".to_string(),
                    }],
                })
            })?;

        let eol = line_ending(self.syntax());
        let syntax = Include::new(path, &eol)?.syntax().clone();

        let target_index = terminate_line_before(&parent, index_after(after_syntax), &eol);
        parent.splice_children(target_index..target_index, vec![syntax.clone().into()]);

        Ok(Include::cast(syntax).unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{assert_matches_reparse, item_without_newline};

    #[test]
    fn test_makefile_item_line_col() {
        let text = "VAR = 1\nall: dep\n\techo\ninclude foo.mk\nvpath %.c src\n.undef VAR\n$(info hi)\nload foo.so\n.for x in a b\n.endfor\nifdef X\na:\nelse\nb:\nendif\n\techo hi\n";
        let makefile: Makefile = text.parse().unwrap();
        assert_eq!(makefile.to_string(), text);
        let items: Vec<_> = makefile
            .items()
            .map(|item| {
                let kind = match item {
                    MakefileItem::Rule(_) => "rule",
                    MakefileItem::Variable(_) => "variable",
                    MakefileItem::Include(_) => "include",
                    MakefileItem::Conditional(_) => "conditional",
                    MakefileItem::Vpath(_) => "vpath",
                    MakefileItem::ForLoop(_) => "for",
                    MakefileItem::Directive(_) => "directive",
                    MakefileItem::ExpressionStatement(_) => "expression",
                    MakefileItem::Load(_) => "load",
                    MakefileItem::Recipe(_) => "recipe",
                };
                (kind, item.line(), item.column(), item.line_col())
            })
            .collect();
        assert_eq!(
            items,
            vec![
                ("variable", 0, 0, (0, 0)),
                ("rule", 1, 0, (1, 0)),
                ("include", 3, 0, (3, 0)),
                ("vpath", 4, 0, (4, 0)),
                ("directive", 5, 0, (5, 0)),
                ("expression", 6, 0, (6, 0)),
                ("load", 7, 0, (7, 0)),
                ("for", 8, 0, (8, 0)),
                ("conditional", 10, 0, (10, 0)),
                ("recipe", 15, 0, (15, 0)),
            ]
        );
    }

    #[test]
    fn test_makefile_item_column() {
        let makefile: Makefile = "\n  VAR = 1\n".parse().unwrap();
        let item = makefile.items().next().unwrap();
        assert_eq!(item.line_col(), (1, 2));
    }

    #[test]
    fn test_makefile_item_replace_variable_with_variable() {
        let makefile: Makefile = "VAR1 = old\nrule:\n\tcommand\n".parse().unwrap();
        let temp: Makefile = "VAR2 = new\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();
        first_item.replace(MakefileItem::Variable(new_var)).unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "VAR2 = new\nrule:\n\tcommand\n");
    }

    #[test]
    fn test_makefile_item_replace_variable_with_rule() {
        let makefile: Makefile = "VAR1 = value\nrule1:\n\tcommand1\n".parse().unwrap();
        let temp: Makefile = "new_rule:\n\tnew_command\n".parse().unwrap();
        let new_rule = temp.rules().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();
        first_item.replace(MakefileItem::Rule(new_rule)).unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "new_rule:\n\tnew_command\nrule1:\n\tcommand1\n");
    }

    #[test]
    fn test_makefile_item_replace_preserves_position() {
        let makefile: Makefile = "VAR1 = first\nVAR2 = second\nVAR3 = third\n"
            .parse()
            .unwrap();
        let temp: Makefile = "NEW = replacement\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();

        // Replace the second item
        let mut second_item = makefile.items().nth(1).unwrap();
        second_item
            .replace(MakefileItem::Variable(new_var))
            .unwrap();

        let items: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0].name(), Some("VAR1".to_string()));
        assert_eq!(items[1].name(), Some("NEW".to_string()));
        assert_eq!(items[2].name(), Some("VAR3".to_string()));
    }

    #[test]
    fn test_makefile_item_add_comment() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let mut item = makefile.items().next().unwrap();
        item.add_comment("This is a variable").unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "# This is a variable\nVAR = value\n");
    }

    #[test]
    fn test_makefile_item_add_multiple_comments() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let mut item = makefile.items().next().unwrap();
        item.add_comment("Comment 1").unwrap();
        // Note: After modifying the tree, we need to get a fresh reference
        let mut item = makefile.items().next().unwrap();
        item.add_comment("Comment 2").unwrap();

        let result = makefile.to_string();
        // Comments are added before the item, so adding Comment 2 after Comment 1
        // results in Comment 1 appearing first (furthest from item), then Comment 2
        assert_eq!(result, "# Comment 1\n# Comment 2\nVAR = value\n");
    }

    #[test]
    fn test_makefile_item_preceding_comments() {
        let makefile: Makefile = "# Comment 1\n# Comment 2\nVAR = value\n".parse().unwrap();
        let item = makefile.items().next().unwrap();
        let comments: Vec<_> = item.preceding_comments().collect();
        assert_eq!(comments.len(), 2);
        assert_eq!(comments[0], "Comment 1");
        assert_eq!(comments[1], "Comment 2");
    }

    #[test]
    fn test_makefile_item_preceding_comments_no_comments() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let item = makefile.items().next().unwrap();
        let comments: Vec<_> = item.preceding_comments().collect();
        assert_eq!(comments.len(), 0);
    }

    #[test]
    fn test_makefile_item_preceding_comments_ignores_shebang() {
        let makefile: Makefile = "#!/usr/bin/make\n# Real comment\nVAR = value\n"
            .parse()
            .unwrap();
        let item = makefile.items().next().unwrap();
        let comments: Vec<_> = item.preceding_comments().collect();
        assert_eq!(comments.len(), 1);
        assert_eq!(comments[0], "Real comment");
    }

    #[test]
    fn test_makefile_item_remove_comments() {
        let makefile: Makefile = "# Comment 1\n# Comment 2\nVAR = value\n".parse().unwrap();
        // Get a fresh reference to the item to ensure we have the current tree state
        let mut item = makefile.items().next().unwrap();
        let count = item.remove_comments().unwrap();

        assert_eq!(count, 2);
        let result = makefile.to_string();
        assert_eq!(result, "VAR = value\n");
    }

    #[test]
    fn test_makefile_item_remove_comments_no_comments() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let mut item = makefile.items().next().unwrap();
        let count = item.remove_comments().unwrap();

        assert_eq!(count, 0);
        assert_eq!(makefile.to_string(), "VAR = value\n");
    }

    #[test]
    fn test_makefile_item_remove_comments_with_one_blank_line() {
        // A single blank line between the comments and the item is consumed
        // along with the comments (one blank-line newline removed).
        let makefile: Makefile = "# c1\n# c2\n\nVAR = value\n".parse().unwrap();
        let mut item = makefile.items().last().unwrap();
        let count = item.remove_comments().unwrap();

        assert_eq!(count, 2);
        assert_eq!(makefile.to_string(), "\nVAR = value\n");
    }

    #[test]
    fn test_makefile_item_remove_comments_keeps_extra_blank_lines() {
        // Only one blank-line newline is removed; a second blank line stays.
        let makefile: Makefile = "# c1\n# c2\n\n\nVAR = value\n".parse().unwrap();
        let mut item = makefile.items().last().unwrap();
        let count = item.remove_comments().unwrap();

        assert_eq!(count, 2);
        assert_eq!(makefile.to_string(), "\n\nVAR = value\n");
    }

    #[test]
    fn test_makefile_item_remove_comments_stops_at_preceding_item() {
        // Comments are collected only back to the previous item, and the blank
        // line before the comment is preserved (it belongs to the item above).
        let makefile: Makefile = "VAR0 = x\n\n# c1\nVAR = value\n".parse().unwrap();
        let mut item = makefile.items().last().unwrap();
        let count = item.remove_comments().unwrap();

        assert_eq!(count, 1);
        assert_eq!(makefile.to_string(), "VAR0 = x\n\nVAR = value\n");
    }

    #[test]
    fn test_makefile_item_comments_after_rule() {
        // The parser puts the comment into the RULE node of `a`.
        let text = "a:\n\techo\n# far\n\n# doc of b\nb:\n";
        let makefile: Makefile = text.parse().unwrap();
        let item = makefile.items().nth(1).unwrap();
        assert_eq!(
            item.preceding_comments().collect::<Vec<_>>(),
            vec!["far", "doc of b"]
        );

        let mut item = makefile.items().nth(1).unwrap();
        assert!(item.modify_comment("new").unwrap());
        assert_eq!(makefile.to_string(), "a:\n\techo\n# far\n\n# new\nb:\n");

        let mut item = makefile.items().nth(1).unwrap();
        assert_eq!(item.remove_comments().unwrap(), 2);
        assert_eq!(makefile.to_string(), "a:\n\techo\n\nb:\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_makefile_item_preceding_comments_stop_at_content() {
        for text in [
            "X = 1 # x\nb:\n",
            "X = a \\\n# continued\nb:\n",
            "ifdef X # c\nb:\nendif\n",
        ] {
            let makefile: Makefile = text.parse().unwrap();
            let rule = makefile.rules().next().unwrap();
            let item = MakefileItem::Rule(rule);
            assert_eq!(item.preceding_comments().count(), 0, "{text:?}");
        }
    }

    #[test]
    fn test_makefile_item_add_comment_exact_output() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let mut item = makefile.items().next().unwrap();
        item.add_comment("note").unwrap();
        assert_eq!(makefile.to_string(), "# note\nVAR = value\n");
    }

    #[test]
    fn test_makefile_item_remove_comments_strips_trailing_whitespace() {
        // Trailing whitespace on the removed comment line is removed too.
        let makefile: Makefile = "# c1  \nVAR = value\n".parse().unwrap();
        let mut item = makefile.items().last().unwrap();
        let count = item.remove_comments().unwrap();

        assert_eq!(count, 1);
        assert_eq!(makefile.to_string(), "VAR = value\n");
    }

    #[test]
    fn test_makefile_item_remove_comments_stops_at_shebang() {
        // A shebang line is not a removable comment; nothing is removed.
        let makefile: Makefile = "#!/usr/bin/make -f\nVAR = value\n".parse().unwrap();
        let mut item = makefile.items().last().unwrap();
        let count = item.remove_comments().unwrap();

        assert_eq!(count, 0);
        assert_eq!(makefile.to_string(), "#!/usr/bin/make -f\nVAR = value\n");
    }

    #[test]
    fn test_makefile_item_modify_comment() {
        let makefile: Makefile = "# Old comment\nVAR = value\n".parse().unwrap();
        let mut item = makefile.items().next().unwrap();
        let modified = item.modify_comment("New comment").unwrap();

        assert!(modified);
        let result = makefile.to_string();
        assert_eq!(result, "# New comment\nVAR = value\n");
    }

    #[test]
    fn test_makefile_item_modify_comment_no_comment() {
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let mut item = makefile.items().next().unwrap();
        let modified = item.modify_comment("New comment").unwrap();

        assert!(!modified);
        assert_eq!(makefile.to_string(), "VAR = value\n");
    }

    #[test]
    fn test_makefile_item_modify_comment_modifies_closest() {
        let makefile: Makefile = "# Comment 1\n# Comment 2\n# Comment 3\nVAR = value\n"
            .parse()
            .unwrap();
        let mut item = makefile.items().next().unwrap();
        let modified = item.modify_comment("Modified").unwrap();

        assert!(modified);
        let result = makefile.to_string();
        assert_eq!(
            result,
            "# Comment 1\n# Comment 2\n# Modified\nVAR = value\n"
        );
    }

    #[test]
    fn test_makefile_item_comment_workflow() {
        // Test adding, modifying, and removing comments in sequence
        let makefile: Makefile = "VAR = value\n".parse().unwrap();
        let mut item = makefile.items().next().unwrap();

        // Add a comment
        item.add_comment("Initial comment").unwrap();
        assert_eq!(makefile.to_string(), "# Initial comment\nVAR = value\n");

        // Get a fresh reference after modification
        let mut item = makefile.items().next().unwrap();
        // Modify it
        item.modify_comment("Updated comment").unwrap();
        assert_eq!(makefile.to_string(), "# Updated comment\nVAR = value\n");

        // Get a fresh reference after modification
        let mut item = makefile.items().next().unwrap();
        // Remove it
        let count = item.remove_comments().unwrap();
        assert_eq!(count, 1);
        assert_eq!(makefile.to_string(), "VAR = value\n");
    }

    #[test]
    fn test_makefile_item_replace_with_comments() {
        let makefile: Makefile = "# Comment for VAR1\nVAR1 = old\nrule:\n\tcommand\n"
            .parse()
            .unwrap();
        let temp: Makefile = "VAR2 = new\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();

        // Verify comment exists before replace
        let comments: Vec<_> = first_item.preceding_comments().collect();
        assert_eq!(comments.len(), 1);
        assert_eq!(comments[0], "Comment for VAR1");

        // Replace the item
        first_item.replace(MakefileItem::Variable(new_var)).unwrap();

        let result = makefile.to_string();
        // The comment should still be there (replace preserves preceding comments)
        assert_eq!(result, "# Comment for VAR1\nVAR2 = new\nrule:\n\tcommand\n");
    }

    fn new_variable() -> MakefileItem {
        let temp: Makefile = "N = 1\n".parse().unwrap();
        let item = temp.items().next().unwrap();
        item
    }

    #[test]
    fn test_makefile_item_insert_before_doc_comment() {
        let cases = [
            ("a:\n\techo\n# doc\nc:\n", "a:\n\techo\nN = 1\n# doc\nc:\n"),
            ("a:\n# doc\n# more\nc:\n", "a:\nN = 1\n# doc\n# more\nc:\n"),
            ("X = 1\n# doc\nc:\n", "X = 1\nN = 1\n# doc\nc:\n"),
            ("X = 1\n# x\n\nc:\n", "X = 1\n# x\n\nN = 1\nc:\n"),
            ("X = 1 # x\nc:\n", "X = 1 # x\nN = 1\nc:\n"),
            ("a:\n  # doc\nc:\n", "a:\nN = 1\n  # doc\nc:\n"),
            // The comment is part of the line `X = a`.
            ("X = a \\\n# x\nc:\n", "X = a \\\n# x\nN = 1\nc:\n"),
            (
                "#!/usr/bin/make -f\nc:\n",
                "#!/usr/bin/make -f\nN = 1\nc:\n",
            ),
        ];
        for (text, expected) in cases {
            let makefile: Makefile = text.parse().unwrap();
            let mut item = makefile.items().last().unwrap();
            item.insert_before(new_variable()).unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?}");
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_makefile_item_insert_before_doc_comment_in_conditional() {
        let makefile: Makefile = "ifdef X\n# doc\nc:\nendif\n".parse().unwrap();
        let mut item = makefile
            .conditionals()
            .next()
            .unwrap()
            .if_items()
            .next()
            .unwrap();
        item.insert_before(new_variable()).unwrap();
        assert_eq!(makefile.to_string(), "ifdef X\nN = 1\n# doc\nc:\nendif\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_makefile_item_insert_after_before_doc_comment() {
        for (text, expected) in [
            ("a:\n\techo\n# doc\nc:\n", "a:\n\techo\nN = 1\n# doc\nc:\n"),
            ("X = 1\n# doc\nc:\n", "X = 1\nN = 1\n# doc\nc:\n"),
            ("a:\n\techo\n# a\n\nc:\n", "a:\n\techo\n# a\n\nN = 1\nc:\n"),
        ] {
            let makefile: Makefile = text.parse().unwrap();
            let mut item = makefile.items().next().unwrap();
            item.insert_after(new_variable()).unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?}");
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_insert_include_before_doc_comment() {
        let mut makefile: Makefile = "a:\n\techo\n# doc\nc:\n".parse().unwrap();
        let include = makefile.insert_include(1, "x.mk").unwrap();
        assert_eq!(include.path(), Some("x.mk".to_string()));
        assert_eq!(
            makefile.to_string(),
            "a:\n\techo\ninclude x.mk\n# doc\nc:\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_insert_include_after_before_doc_comment() {
        let mut makefile: Makefile = "a:\n\techo\n# doc\nc:\n".parse().unwrap();
        let a = makefile.items().next().unwrap();
        let include = makefile.insert_include_after(&a, "x.mk").unwrap();
        assert_eq!(include.path(), Some("x.mk".to_string()));
        assert_eq!(
            makefile.to_string(),
            "a:\n\techo\ninclude x.mk\n# doc\nc:\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_makefile_item_recipe_positions() {
        let code = "ifdef X\na:\nelse\nb:\nendif\n\techo 1\n\techo 2\n";
        let item = |text: &str| {
            let makefile: Makefile = text.parse().unwrap();
            makefile.items().last().unwrap()
        };
        let recipe = || item(code);
        let cases: Vec<(&str, usize, &str, MakefileItem, Option<&str>)> = vec![
            (code, 0, "after", item("X = 1\n"), None),
            (code, 0, "after", item("c:\n"), None),
            (code, 0, "replace", item("c:\n"), None),
            (code, 1, "before", item("X = 1\n"), None),
            (code, 1, "after", item("c:\n"), None),
            (code, 2, "before", item("X = 1\n"), None),
            (code, 1, "replace", item("X = 1\n"), None),
            (
                code,
                2,
                "after",
                item("X = 1\n"),
                Some("ifdef X\na:\nelse\nb:\nendif\n\techo 1\n\techo 2\nX = 1\n"),
            ),
            (
                code,
                2,
                "replace",
                item("c:\n"),
                Some("ifdef X\na:\nelse\nb:\nendif\n\techo 1\nc:\n"),
            ),
            (
                code,
                1,
                "after",
                recipe(),
                Some("ifdef X\na:\nelse\nb:\nendif\n\techo 1\n\techo 2\n\techo 2\n"),
            ),
            (
                code,
                1,
                "before",
                recipe(),
                Some("ifdef X\na:\nelse\nb:\nendif\n\techo 2\n\techo 1\n\techo 2\n"),
            ),
            (
                code,
                1,
                "replace",
                recipe(),
                Some("ifdef X\na:\nelse\nb:\nendif\n\techo 2\n\techo 2\n"),
            ),
            ("X = 1\n", 0, "after", recipe(), None),
            ("X = 1\n", 0, "replace", recipe(), None),
            ("a:\n\techo\n", 0, "after", recipe(), None),
        ];
        for (code, index, op, new_item, expected) in cases {
            let makefile: Makefile = code.parse().unwrap();
            let mut target = makefile.items().nth(index).unwrap();
            let result = match op {
                "before" => target.insert_before(new_item),
                "after" => target.insert_after(new_item),
                _ => target.replace(new_item),
            };
            assert_eq!(result.is_ok(), expected.is_some(), "{code:?} {index} {op}");
            assert_eq!(
                makefile.code(),
                expected.unwrap_or(code),
                "{code:?} {index} {op}"
            );
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_makefile_item_insert_before_recipe_in_conditional() {
        let code = "a:\nifdef X\n\techo\nendif\n";
        let makefile: Makefile = code.parse().unwrap();
        let node = makefile
            .syntax()
            .descendants()
            .find(|n| n.kind() == RECIPE)
            .unwrap();
        let mut recipe = MakefileItem::cast(node).unwrap();
        let temp: Makefile = "Y = 1\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        assert!(recipe
            .insert_before(MakefileItem::Variable(new_var))
            .is_err());
        assert_eq!(makefile.code(), code);
    }

    #[test]
    fn test_makefile_item_insert_before_variable() {
        let makefile: Makefile = "VAR1 = first\nVAR2 = second\n".parse().unwrap();
        let temp: Makefile = "VAR_NEW = inserted\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut second_item = makefile.items().nth(1).unwrap();
        second_item
            .insert_before(MakefileItem::Variable(new_var))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "VAR1 = first\nVAR_NEW = inserted\nVAR2 = second\n");
    }

    #[test]
    fn test_makefile_item_insert_after_variable() {
        let makefile: Makefile = "VAR1 = first\nVAR2 = second\n".parse().unwrap();
        let temp: Makefile = "VAR_NEW = inserted\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();
        first_item
            .insert_after(MakefileItem::Variable(new_var))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "VAR1 = first\nVAR_NEW = inserted\nVAR2 = second\n");
    }

    #[test]
    fn test_makefile_item_insert_before_first_item() {
        let makefile: Makefile = "VAR1 = first\nVAR2 = second\n".parse().unwrap();
        let temp: Makefile = "VAR_NEW = inserted\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();
        first_item
            .insert_before(MakefileItem::Variable(new_var))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "VAR_NEW = inserted\nVAR1 = first\nVAR2 = second\n");
    }

    #[test]
    fn test_makefile_item_insert_after_last_item() {
        let makefile: Makefile = "VAR1 = first\nVAR2 = second\n".parse().unwrap();
        let temp: Makefile = "VAR_NEW = inserted\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut last_item = makefile.items().nth(1).unwrap();
        last_item
            .insert_after(MakefileItem::Variable(new_var))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "VAR1 = first\nVAR2 = second\nVAR_NEW = inserted\n");
    }

    #[test]
    fn test_makefile_item_insert_before_include() {
        let makefile: Makefile = "VAR1 = value\nrule:\n\tcommand\n".parse().unwrap();
        let temp: Makefile = "include test.mk\n".parse().unwrap();
        let new_include = temp.includes().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();
        first_item
            .insert_before(MakefileItem::Include(new_include))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "include test.mk\nVAR1 = value\nrule:\n\tcommand\n");
    }

    #[test]
    fn test_makefile_item_insert_after_include() {
        let makefile: Makefile = "VAR1 = value\nrule:\n\tcommand\n".parse().unwrap();
        let temp: Makefile = "include test.mk\n".parse().unwrap();
        let new_include = temp.includes().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();
        first_item
            .insert_after(MakefileItem::Include(new_include))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "VAR1 = value\ninclude test.mk\nrule:\n\tcommand\n");
    }

    #[test]
    fn test_makefile_item_insert_before_rule() {
        let makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
        let temp: Makefile = "new_rule:\n\tnew_command\n".parse().unwrap();
        let new_rule = temp.rules().next().unwrap();
        let mut second_item = makefile.items().nth(1).unwrap();
        second_item
            .insert_before(MakefileItem::Rule(new_rule))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(
            result,
            "rule1:\n\tcommand1\nnew_rule:\n\tnew_command\nrule2:\n\tcommand2\n"
        );
    }

    #[test]
    fn test_makefile_item_insert_after_rule() {
        let makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
        let temp: Makefile = "new_rule:\n\tnew_command\n".parse().unwrap();
        let new_rule = temp.rules().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();
        first_item
            .insert_after(MakefileItem::Rule(new_rule))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(
            result,
            "rule1:\n\tcommand1\nnew_rule:\n\tnew_command\nrule2:\n\tcommand2\n"
        );
    }

    #[test]
    fn test_makefile_item_insert_before_with_comments() {
        let makefile: Makefile = "# Comment 1\nVAR1 = first\n# Comment 2\nVAR2 = second\n"
            .parse()
            .unwrap();
        let temp: Makefile = "VAR_NEW = inserted\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut second_item = makefile.items().nth(1).unwrap();
        second_item
            .insert_before(MakefileItem::Variable(new_var))
            .unwrap();

        let result = makefile.to_string();
        // The new variable is inserted before Comment 2, which documents VAR2
        assert_eq!(
            result,
            "# Comment 1\nVAR1 = first\nVAR_NEW = inserted\n# Comment 2\nVAR2 = second\n"
        );
    }

    #[test]
    fn test_makefile_item_insert_after_with_comments() {
        let makefile: Makefile = "# Comment 1\nVAR1 = first\n# Comment 2\nVAR2 = second\n"
            .parse()
            .unwrap();
        let temp: Makefile = "VAR_NEW = inserted\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut first_item = makefile.items().next().unwrap();
        first_item
            .insert_after(MakefileItem::Variable(new_var))
            .unwrap();

        let result = makefile.to_string();
        // The new variable should be inserted between VAR1 and Comment 2/VAR2
        assert_eq!(
            result,
            "# Comment 1\nVAR1 = first\nVAR_NEW = inserted\n# Comment 2\nVAR2 = second\n"
        );
    }

    #[test]
    fn test_makefile_item_insert_before_preserves_formatting() {
        let makefile: Makefile = "VAR1  =  first\nVAR2  =  second\n".parse().unwrap();
        let temp: Makefile = "VAR_NEW  =  inserted\n".parse().unwrap();
        let new_var = temp.variable_definitions().next().unwrap();
        let mut second_item = makefile.items().nth(1).unwrap();
        second_item
            .insert_before(MakefileItem::Variable(new_var))
            .unwrap();

        let result = makefile.to_string();
        // Formatting of the new item is preserved from its source
        assert_eq!(
            result,
            "VAR1  =  first\nVAR_NEW  =  inserted\nVAR2  =  second\n"
        );
    }

    #[test]
    fn test_makefile_item_insert_multiple_items() {
        let makefile: Makefile = "VAR1 = first\nVAR2 = last\n".parse().unwrap();
        let temp: Makefile = "VAR_A = a\nVAR_B = b\n".parse().unwrap();
        let mut new_vars: Vec<_> = temp.variable_definitions().collect();

        let mut target_item = makefile.items().nth(1).unwrap();
        target_item
            .insert_before(MakefileItem::Variable(new_vars.pop().unwrap()))
            .unwrap();

        // Get fresh reference after first insertion
        let mut target_item = makefile.items().nth(1).unwrap();
        target_item
            .insert_before(MakefileItem::Variable(new_vars.pop().unwrap()))
            .unwrap();

        let result = makefile.to_string();
        assert_eq!(result, "VAR1 = first\nVAR_A = a\nVAR_B = b\nVAR2 = last\n");
    }

    #[test]
    fn test_rules_after_nested_conditionals() {
        // Test for bug where .rules() returns no rules after nested conditionals
        // This was reported in https://bugs.debian.org/1126511
        let makefile_content = r#"#!/usr/bin/make -f

ifeq ($(filter nodoc, $(DEB_BUILD_OPTIONS)),)
ifneq ($(shell which valadoc),)
  BUILD_DOC:=-Ddocs=true
endif
endif

%:
	dh $@

override_dh_auto_configure:
	echo test
"#;
        let makefile: Makefile = makefile_content.parse().unwrap();

        let rules: Vec<_> = makefile.rules().collect();
        let targets: Vec<Vec<_>> = rules.iter().map(|r| r.targets().collect()).collect();
        assert_eq!(
            rules.len(),
            2,
            "Expected 2 rules (% and override_dh_auto_configure), got {} rules with targets: {:?}",
            rules.len(),
            targets
        );

        assert_eq!(targets[0], vec!["%"]);
        assert_eq!(targets[1], vec!["override_dh_auto_configure"]);

        // Also test that pattern matching works
        assert!(makefile.find_rule_by_target_pattern("build-arch").is_some());
        assert!(makefile
            .find_rule_by_target_pattern("build-indep")
            .is_some());
    }

    #[test]
    fn test_items_in_range_single_item() {
        let input = "CC = gcc\n\nall: build\n\techo done\n";
        let makefile: Makefile = input.parse().unwrap();
        // Range covering just the variable definition "CC = gcc\n"
        let range = rowan::TextRange::new(0.into(), 8.into());
        let items: Vec<_> = makefile.items_in_range(range).collect();
        assert_eq!(items.len(), 1);
        assert!(matches!(items[0], MakefileItem::Variable(_)));
    }

    #[test]
    fn test_items_in_range_multiple_items() {
        let input = "CC = gcc\n\nall: build\n\techo done\n";
        let makefile: Makefile = input.parse().unwrap();
        // Range covering the whole file
        let range = rowan::TextRange::new(0.into(), (input.len() as u32).into());
        let items: Vec<_> = makefile.items_in_range(range).collect();
        assert_eq!(items.len(), 2);
    }

    #[test]
    fn test_items_in_range_no_overlap() {
        let input = "CC = gcc\n\nall: build\n\techo done\n";
        let makefile: Makefile = input.parse().unwrap();
        // Range in the blank line between items
        let range = rowan::TextRange::new(9.into(), 10.into());
        let items: Vec<_> = makefile.items_in_range(range).collect();
        assert_eq!(items.len(), 0);
    }

    #[test]
    fn test_items_in_range_partial_overlap() {
        let input = "CC = gcc\nLD = ld\nall: build\n\techo done\n";
        let makefile: Makefile = input.parse().unwrap();
        // Range overlapping end of first var and start of second
        let range = rowan::TextRange::new(5.into(), 12.into());
        let items: Vec<_> = makefile.items_in_range(range).collect();
        assert_eq!(items.len(), 2);
    }

    #[test]
    fn test_rules_in_range() {
        let input = "CC = gcc\nall: build\n\techo done\nclean:\n\trm -rf build\n";
        let makefile: Makefile = input.parse().unwrap();
        // Range covering the whole file
        let range = rowan::TextRange::new(0.into(), (input.len() as u32).into());
        let rules: Vec<_> = makefile.rules_in_range(range).collect();
        assert_eq!(rules.len(), 2);

        // Range covering only the variable
        let range = rowan::TextRange::new(0.into(), 9.into());
        let rules: Vec<_> = makefile.rules_in_range(range).collect();
        assert_eq!(rules.len(), 0);
    }

    #[test]
    fn test_variable_definitions_in_range() {
        let input = "CC = gcc\nLD = ld\nall: build\n\techo done\n";
        let makefile: Makefile = input.parse().unwrap();
        // Range covering the two variable definitions
        let range = rowan::TextRange::new(0.into(), 17.into());
        let vars: Vec<_> = makefile.variable_definitions_in_range(range).collect();
        assert_eq!(vars.len(), 2);

        // Range covering only the rule
        let range = rowan::TextRange::new(17.into(), (input.len() as u32).into());
        let vars: Vec<_> = makefile.variable_definitions_in_range(range).collect();
        assert_eq!(vars.len(), 0);
    }

    #[test]
    fn test_variable_references_in_range() {
        let input = "CFLAGS = $(BASE) -Wall\nall: $(TARGETS)\n\techo done\n";
        let makefile: Makefile = input.parse().unwrap();

        // Full range should find the same refs as variable_references()
        let all_refs: Vec<_> = makefile.variable_references().collect();
        let range = rowan::TextRange::new(0.into(), (input.len() as u32).into());
        let refs: Vec<_> = makefile.variable_references_in_range(range).collect();
        assert_eq!(refs.len(), all_refs.len());

        // Range covering only the variable definition should find $(BASE)
        // Find the actual end of the variable item
        let var_item = makefile.items().next().unwrap();
        let var_end: u32 = var_item.syntax().text_range().end().into();
        let range = rowan::TextRange::new(0.into(), var_end.into());
        let refs: Vec<_> = makefile.variable_references_in_range(range).collect();
        assert_eq!(refs.len(), 1);
        assert_eq!(refs[0].name(), Some("BASE".to_string()));

        // Range covering only the rule should find $(TARGETS)
        let range = rowan::TextRange::new(var_end.into(), (input.len() as u32).into());
        let refs: Vec<_> = makefile.variable_references_in_range(range).collect();
        assert_eq!(refs.len(), 1);
        assert_eq!(refs[0].name(), Some("TARGETS".to_string()));
    }

    #[test]
    fn test_comment_blocks_single_block() {
        let makefile: Makefile = "# line 1\n# line 2\n# line 3\nall:\n\techo done\n"
            .parse()
            .unwrap();
        let blocks: Vec<_> = makefile.comment_blocks().collect();
        assert_eq!(blocks.len(), 1);
        let text = &makefile.to_string()[std::ops::Range::from(blocks[0])];
        assert!(text.contains("# line 1"));
        assert!(text.contains("# line 3"));
    }

    #[test]
    fn test_comment_blocks_multiple_blocks() {
        let makefile: Makefile =
            "# block 1a\n# block 1b\nVAR = value\n# block 2a\n# block 2b\nall:\n\techo done\n"
                .parse()
                .unwrap();
        let blocks: Vec<_> = makefile.comment_blocks().collect();
        assert_eq!(blocks.len(), 2);
    }

    #[test]
    fn test_comment_blocks_no_blocks() {
        let makefile: Makefile = "VAR = value\nall:\n\techo done\n".parse().unwrap();
        let blocks: Vec<_> = makefile.comment_blocks().collect();
        assert_eq!(blocks.len(), 0);
    }

    #[test]
    fn test_comment_blocks_single_comment_not_a_block() {
        let makefile: Makefile = "# just one line\nVAR = value\n".parse().unwrap();
        let blocks: Vec<_> = makefile.comment_blocks().collect();
        assert_eq!(blocks.len(), 0);
    }

    #[test]
    fn test_comment_blocks_with_blank_line_between() {
        let makefile: Makefile = "# line 1\n\n# line 2\nVAR = value\n".parse().unwrap();
        let blocks: Vec<_> = makefile.comment_blocks().collect();
        // Blank lines between comments should still form a block
        assert_eq!(blocks.len(), 1);
    }

    #[test]
    fn test_insert_rule_at_front() {
        let mut makefile: Makefile = "a:\n\tx\n\nb:\n\ty\n".parse().unwrap();
        let new_rule: Rule = "new:\n\tz\n".parse().unwrap();
        makefile.insert_rule(0, new_rule).unwrap();
        assert_eq!(makefile.to_string(), "new:\n\tz\n\na:\n\tx\n\nb:\n\ty\n");
    }

    #[test]
    fn test_insert_rule_in_middle_no_blank_before_target() {
        let mut makefile: Makefile = "a:\n\tx\nb:\n\ty\n".parse().unwrap();
        let new_rule: Rule = "new:\n\tz\n".parse().unwrap();
        makefile.insert_rule(1, new_rule).unwrap();
        assert_eq!(makefile.to_string(), "a:\n\tx\n\nnew:\n\tz\n\nb:\n\ty\n");
    }

    #[test]
    fn test_insert_rule_in_middle_blank_before_target() {
        let mut makefile: Makefile = "a:\n\tx\n\nb:\n\ty\n".parse().unwrap();
        let new_rule: Rule = "new:\n\tz\n".parse().unwrap();
        makefile.insert_rule(1, new_rule).unwrap();
        assert_eq!(makefile.to_string(), "a:\n\tx\n\nnew:\n\tz\n\nb:\n\ty\n");
    }

    #[test]
    fn test_insert_rule_at_end() {
        let mut makefile: Makefile = "a:\n\tx\n".parse().unwrap();
        let new_rule: Rule = "new:\n\tz\n".parse().unwrap();
        makefile.insert_rule(1, new_rule).unwrap();
        assert_eq!(makefile.to_string(), "a:\n\tx\n\nnew:\n\tz\n");
    }

    fn rule_targets(makefile: &Makefile) -> Vec<String> {
        makefile
            .rules()
            .flat_map(|r| r.targets().collect::<Vec<_>>())
            .collect()
    }

    #[test]
    fn test_insert_rule_in_conditional() {
        let cases = [
            ("ifdef X\nall:\nendif\n", 0, "ifdef X\nb:\n\nall:\nendif\n"),
            ("ifdef X\nall:\nendif\n", 1, "ifdef X\nall:\nendif\n\nb:\n"),
            (
                "a:\nifdef X\nc:\nelse\nd:\nendif\n",
                2,
                "a:\nifdef X\nc:\nelse\nb:\n\nd:\nendif\n",
            ),
            (
                "a:\nifdef X\nc:\nd:\nendif\ne:\n",
                2,
                "a:\nifdef X\nc:\n\nb:\n\nd:\nendif\ne:\n",
            ),
            (
                "a:\nifdef X\nc:\nendif\ne:\n",
                2,
                "a:\nifdef X\nc:\nendif\n\nb:\n\ne:\n",
            ),
            (
                "a:\nifdef X\nc:\n\nd:\nendif\n",
                2,
                "a:\nifdef X\nc:\n\nb:\n\nd:\nendif\n",
            ),
        ];
        for (text, index, expected) in cases {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile
                .insert_rule(index, "b:\n".parse().unwrap())
                .unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?} at {index}");
            let reparsed: Makefile = expected.parse().unwrap();
            assert_eq!(rule_targets(&reparsed), rule_targets(&makefile));
            assert_eq!(rule_targets(&reparsed)[index], "b", "{text:?} at {index}");
        }
    }

    #[test]
    fn test_insert_rule_in_for_loop() {
        let (mut makefile, _) = Makefile::from_str_relaxed(".for x in a b\nfoo:\n.endfor\n");
        makefile.insert_rule(0, "b:\n".parse().unwrap()).unwrap();
        assert_eq!(makefile.to_string(), ".for x in a b\nb:\n\nfoo:\n.endfor\n");
    }

    #[test]
    fn test_insert_rule_in_conditional_out_of_bounds() {
        let mut makefile: Makefile = "ifdef X\nall:\nendif\n".parse().unwrap();
        let err = makefile
            .insert_rule(2, "b:\n".parse().unwrap())
            .unwrap_err();
        assert_eq!(
            err.to_string(),
            "Parse error: Error at line 1: Rule index 2 out of bounds (max 1)\n1| insert_rule\n"
        );
    }

    #[test]
    fn test_remove_rule_in_conditional() {
        let mut makefile: Makefile = "a:\nifdef X\nc:\nendif\ne:\n".parse().unwrap();
        let removed = makefile.remove_rule(1).unwrap();
        assert_eq!(removed.targets().collect::<Vec<_>>(), vec!["c"]);
        assert_eq!(makefile.to_string(), "a:\nifdef X\nendif\ne:\n");
        let removed = makefile.remove_rule(1).unwrap();
        assert_eq!(removed.targets().collect::<Vec<_>>(), vec!["e"]);
        assert_eq!(makefile.to_string(), "a:\nifdef X\nendif\n");
        let reparsed: Makefile = makefile.to_string().parse().unwrap();
        assert_eq!(rule_targets(&reparsed), vec!["a"]);
    }

    #[test]
    fn test_replace_rule_in_conditional() {
        let mut makefile: Makefile = "a:\nifdef X\nc:\nendif\ne:\n".parse().unwrap();
        makefile.replace_rule(1, "z:\n".parse().unwrap()).unwrap();
        assert_eq!(makefile.to_string(), "a:\nifdef X\nz:\nendif\ne:\n");
        makefile.replace_rule(2, "y:\n".parse().unwrap()).unwrap();
        assert_eq!(makefile.to_string(), "a:\nifdef X\nz:\nendif\ny:\n");
        let reparsed: Makefile = makefile.to_string().parse().unwrap();
        assert_eq!(rule_targets(&reparsed), vec!["a", "z", "y"]);
    }

    #[test]
    fn test_insert_rule_blank_line() {
        let cases = [
            ("", 0, "b:\n"),
            ("all: a\n", 1, "all: a\n\nb:\n"),
            ("all: a\n\n", 1, "all: a\n\nb:\n"),
            ("all: a\n\n\n", 1, "all: a\n\n\nb:\n"),
            ("X = 1\n", 0, "X = 1\n\nb:\n"),
            ("X = 1\n\n", 0, "X = 1\n\nb:\n"),
            ("# comment\n", 0, "# comment\n\nb:\n"),
            ("\n", 0, "\nb:\n"),
            (
                "ifdef X\nY = 1\nendif\n\n",
                0,
                "ifdef X\nY = 1\nendif\n\nb:\n",
            ),
            ("a:\n", 0, "b:\n\na:\n"),
            ("a:\n\n", 0, "b:\n\na:\n\n"),
            ("\na:\n", 0, "\nb:\n\na:\n"),
            ("X = 1\na:\n", 0, "X = 1\n\nb:\n\na:\n"),
            ("X = 1\n\na:\n", 0, "X = 1\n\nb:\n\na:\n"),
            ("a:\nc:\n", 1, "a:\n\nb:\n\nc:\n"),
            ("a:\n\nc:\n", 1, "a:\n\nb:\n\nc:\n"),
            ("a:\n\n\nc:\n", 1, "a:\n\n\nb:\n\nc:\n"),
            ("a:\n\tx\n\nc:\n", 1, "a:\n\tx\n\nb:\n\nc:\n"),
            ("a:\nX = 1\nc:\n", 1, "a:\nX = 1\n\nb:\n\nc:\n"),
        ];
        for (text, index, expected) in cases {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile
                .insert_rule(index, "b:\n".parse().unwrap())
                .unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?} at {index}");
            let reparsed: Makefile = expected.parse().unwrap();
            assert_eq!(
                reparsed
                    .rules()
                    .nth(index)
                    .unwrap()
                    .targets()
                    .collect::<Vec<_>>(),
                vec!["b"],
                "{text:?} at {index}"
            );
        }
    }

    #[test]
    fn test_insert_rule_ending_in_blank_line() {
        let mut makefile: Makefile = "a:\n".parse().unwrap();
        makefile.insert_rule(0, "b:\n\n".parse().unwrap()).unwrap();
        assert_eq!(makefile.to_string(), "b:\n\na:\n");
    }

    #[test]
    fn test_insert_rule_out_of_bounds() {
        let mut makefile: Makefile = "a:\n\tx\n".parse().unwrap();
        let new_rule: Rule = "new:\n\tz\n".parse().unwrap();
        assert!(makefile.insert_rule(5, new_rule).is_err());
    }

    #[test]
    fn test_variable_definitions_document_order() {
        let makefile: Makefile = "ifdef X\nA = 1\nendif\nB = 2\nC = 3\n".parse().unwrap();
        let names: Vec<_> = makefile
            .variable_definitions()
            .map(|v| v.name().unwrap())
            .collect();
        assert_eq!(names, vec!["A", "B", "C"]);
    }

    #[test]
    fn test_variable_definitions_document_order_nested() {
        let makefile: Makefile =
            "A = 1\nifdef X\nB = 2\nifdef Y\nC = 3\nendif\nD = 4\nelse\nE = 5\nendif\nF = 6\n"
                .parse()
                .unwrap();
        let names: Vec<_> = makefile
            .variable_definitions()
            .map(|v| v.name().unwrap())
            .collect();
        assert_eq!(names, vec!["A", "B", "C", "D", "E", "F"]);
    }

    #[test]
    fn test_rules_document_order() {
        let makefile: Makefile =
            "ifdef X\nifdef Y\na:\n\tx\nendif\nb:\n\ty\nelse\nc:\n\tz\nendif\nd:\n\tw\n"
                .parse()
                .unwrap();
        let targets: Vec<_> = makefile
            .rules()
            .map(|r| r.targets().collect::<Vec<_>>().join(" "))
            .collect();
        assert_eq!(targets, vec!["a", "b", "c", "d"]);
    }

    #[test]
    fn test_find_variable_document_order() {
        let makefile: Makefile = "ifdef X\nA = 1\nendif\nA = 2\n".parse().unwrap();
        let values: Vec<_> = makefile
            .find_variable("A")
            .map(|v| v.raw_value().unwrap())
            .collect();
        assert_eq!(values, vec!["1", "2"]);
    }

    #[test]
    fn test_variable_definitions_document_order_bsd() {
        let makefile = Makefile::parse_with_variant(
            ".if 1\nA=1\n.elif 2\nB=2\n.else\nC=3\n.endif\n.for x in a\nD=4\n.endfor\nE=5\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        let names: Vec<_> = makefile
            .variable_definitions()
            .map(|v| v.name().unwrap())
            .collect();
        assert_eq!(names, vec!["A", "B", "C", "D", "E"]);
    }

    #[test]
    fn test_includes_in_conditionals() {
        let makefile: Makefile = "include a.mk\nifdef X\ninclude b.mk\nelse\n-include c.mk\nifdef Y\ninclude d.mk\nendif\nendif\nall:\nifdef Z\ninclude e.mk\nendif\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile.includes().map(|i| i.path()).collect::<Vec<_>>(),
            vec![
                Some("a.mk".to_string()),
                Some("b.mk".to_string()),
                Some("c.mk".to_string()),
                Some("d.mk".to_string()),
                Some("e.mk".to_string()),
            ]
        );
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["a.mk", "b.mk", "c.mk", "d.mk", "e.mk"]
        );
    }

    #[test]
    fn test_includes_in_for_loop() {
        let makefile = Makefile::parse_with_variant(
            ".for f in a b\n.include \"${f}.mk\"\n.endfor\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        assert_eq!(
            makefile.includes().map(|i| i.path()).collect::<Vec<_>>(),
            vec![Some("${f}.mk".to_string())]
        );
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["${f}.mk"]
        );
    }

    fn doc_comments_of_rules(text: &str) -> Vec<Vec<String>> {
        let makefile = Makefile::from_str_relaxed(text).0;
        makefile
            .rules()
            .map(|r| MakefileItem::Rule(r).doc_comments().collect())
            .collect()
    }

    #[test]
    fn test_doc_comments() {
        assert_eq!(
            doc_comments_of_rules("# one\n#two\n#  three  \na:\n"),
            vec![vec!["one", "two", " three"]]
        );
        assert_eq!(
            doc_comments_of_rules("# far\n\n# near\na:\n"),
            vec![vec!["near"]]
        );
        assert_eq!(
            doc_comments_of_rules("# far\n   \n# near\na:\n"),
            vec![vec!["near"]]
        );
        assert_eq!(
            doc_comments_of_rules("# far\n\na:\n"),
            vec![Vec::<String>::new()]
        );
        assert_eq!(doc_comments_of_rules("a:\n"), vec![Vec::<String>::new()]);
        assert_eq!(
            doc_comments_of_rules("##\n## Help\n#\na:\n"),
            vec![vec!["", "Help", ""]]
        );
    }

    #[test]
    fn test_doc_comments_shebang() {
        assert_eq!(
            doc_comments_of_rules("#!/usr/bin/make -f\n# doc\na:\n"),
            vec![vec!["doc"]]
        );
        assert_eq!(
            doc_comments_of_rules("#!/usr/bin/make -f\na:\n"),
            vec![Vec::<String>::new()]
        );
    }

    #[test]
    fn test_doc_comments_stop_at_content() {
        assert_eq!(
            doc_comments_of_rules("FOO = 1 # trailing\na:\n"),
            vec![Vec::<String>::new()]
        );
        assert_eq!(
            doc_comments_of_rules("FOO = 1 # trailing\n# doc\na:\n"),
            vec![vec!["doc"]]
        );
        assert_eq!(
            doc_comments_of_rules("ifdef X # on directive\na:\nendif\n"),
            vec![Vec::<String>::new()]
        );
        assert_eq!(
            doc_comments_of_rules("FOO = a \\\n# continued\nb:\n"),
            vec![Vec::<String>::new()]
        );
        assert_eq!(
            doc_comments_of_rules("a:\n\t# recipe\nb:\n"),
            vec![Vec::<String>::new(), Vec::<String>::new()]
        );
    }

    #[test]
    fn test_doc_comments_after_rule() {
        assert_eq!(
            doc_comments_of_rules("# a doc\na:\n\techo a\n# b doc\nb:\n"),
            vec![vec!["a doc"], vec!["b doc"]]
        );
    }

    #[test]
    fn test_doc_comments_comment_continuation() {
        assert_eq!(
            doc_comments_of_rules("# one \\\n  two\na:\n"),
            vec![vec!["one \\\n  two"]]
        );
    }

    #[test]
    fn test_doc_comments_crlf() {
        assert_eq!(
            doc_comments_of_rules("# far\r\n\r\n# one \r\n# two\r\na:\r\n"),
            vec![vec!["one", "two"]]
        );
    }

    #[test]
    fn test_doc_comments_indented() {
        let makefile: Makefile = "ifdef X\n  # doc\n  FOO = 1\nendif\n".parse().unwrap();
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(
            MakefileItem::Variable(var)
                .doc_comments()
                .collect::<Vec<_>>(),
            vec!["doc"]
        );
    }

    #[test]
    fn test_doc_comments_in_conditionals() {
        let makefile: Makefile =
            "ifdef X\n# in if\nFOO = 1\nelse\n# in else\nFOO = 2\nendif\n# after\nBAR = 3\n"
                .parse()
                .unwrap();
        let docs: Vec<Vec<String>> = makefile
            .variable_definitions()
            .map(|v| MakefileItem::Variable(v).doc_comments().collect())
            .collect();
        assert_eq!(docs, vec![vec!["in if"], vec!["in else"], vec!["after"]]);

        let cond = makefile.items().next().unwrap();
        assert_eq!(cond.doc_comments().count(), 0);
    }

    #[test]
    fn test_doc_comments_bsd() {
        let makefile = Makefile::parse_with_variant(
            "# doc\n.if ${A}\n# inner\nX=1\n.endif\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        let item = makefile.items().next().unwrap();
        assert_eq!(item.doc_comments().collect::<Vec<_>>(), vec!["doc"]);
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(
            MakefileItem::Variable(var)
                .doc_comments()
                .collect::<Vec<_>>(),
            vec!["inner"]
        );
    }

    #[test]
    fn test_comment_ranges() {
        let text = "#!/bin/make\n# a\n  # b\nFOO = 1 # c\nifdef X # d\nall: # e\n\t# f\n\techo # g\nendif\ndefine F\n# h\nendef\n# i \\\n  j\n";
        let makefile: Makefile = text.parse().unwrap();
        let comments: Vec<_> = makefile
            .comment_ranges()
            .map(|r| &text[r.start().into()..r.end().into()])
            .collect();
        assert_eq!(
            comments,
            vec![
                "#!/bin/make",
                "# a",
                "# b",
                "# c",
                "# d",
                "# e",
                "# f",
                "# h",
                "# i \\\n  j"
            ]
        );
    }

    #[test]
    fn test_comment_ranges_with_references() {
        // References in recipe comment lines and define bodies are parsed,
        // but the comment is still a single range.
        let text = "all:\n\t# a $(X) b\n\t# $(Y)\ndefine F\n# c $(Z) d\nendef\n";
        let makefile: Makefile = text.parse().unwrap();
        let comments: Vec<_> = makefile
            .comment_ranges()
            .map(|r| &text[r.start().into()..r.end().into()])
            .collect();
        assert_eq!(comments, vec!["# a $(X) b", "# $(Y)", "# c $(Z) d"]);
    }

    #[test]
    fn test_comment_ranges_crlf() {
        let text = "# a\r\nFOO = 1 # b\r\n";
        let makefile: Makefile = text.parse().unwrap();
        let comments: Vec<_> = makefile
            .comment_ranges()
            .map(|r| &text[r.start().into()..r.end().into()])
            .collect();
        assert_eq!(comments, vec!["# a", "# b"]);
    }

    #[test]
    fn test_comment_ranges_none() {
        let makefile: Makefile = "all:\n\techo '#'\n".parse().unwrap();
        assert_eq!(makefile.comment_ranges().count(), 0);
    }

    #[test]
    fn test_all_conditionals() {
        let makefile: Makefile = "ifdef A\nifdef B\nX = 1\nendif\nelse ifdef C\nifeq ($(D),1)\nY = 2\nendif\nelse\nifndef E\nendif\nendif\nall:\nifdef F\n\techo f\nifdef G\n\techo g\nendif\nendif\nifdef H\nendif\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile
                .conditionals()
                .map(|c| c.condition().unwrap())
                .collect::<Vec<_>>(),
            vec!["A", "H"]
        );
        assert_eq!(
            makefile
                .all_conditionals()
                .map(|c| c.condition().unwrap())
                .collect::<Vec<_>>(),
            vec!["A", "B", "($(D),1)", "E", "F", "G", "H"]
        );
    }

    #[test]
    fn test_all_conditionals_bsd() {
        let makefile = Makefile::parse_with_variant(
            ".if ${A}\n.if ${B}\n.endif\n.elif ${C}\n.for x in a b\n.ifdef D\n.endif\n.endfor\n.endif\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        assert_eq!(
            makefile
                .all_conditionals()
                .map(|c| c.condition().unwrap())
                .collect::<Vec<_>>(),
            vec!["${A}", "${B}", "D"]
        );
    }

    #[test]
    fn test_all_conditionals_empty() {
        let makefile: Makefile = "all:\n\techo\n".parse().unwrap();
        assert_eq!(makefile.all_conditionals().count(), 0);
    }

    #[test]
    fn test_recipe_nodes() {
        let makefile: Makefile = "a:\n\techo a1\n\techo a2\nifdef X\nb:\n\techo b\nelse\nc:\nifdef Y\n\techo c1\nelse\n\techo c2\nendif\n\techo c3\nendif\nd:\n\techo d\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile
                .recipe_nodes()
                .map(|r| r.text())
                .collect::<Vec<_>>(),
            vec!["echo a1", "echo a2", "echo b", "echo c1", "echo c2", "echo c3", "echo d"]
        );
    }

    #[test]
    fn test_recipe_nodes_outside_rules() {
        let (makefile, errors) = Makefile::from_str_relaxed(
            "\techo orphan\nifdef X\na:\nelse\nb:\nendif\n\techo after\nc:\n\techo c\n",
        );
        assert_eq!(errors.len(), 1);
        assert_eq!(
            makefile
                .recipe_nodes()
                .map(|r| r.text())
                .collect::<Vec<_>>(),
            vec!["echo orphan", "echo after", "echo c"]
        );
        let lines: Vec<_> = makefile.recipe_nodes().map(|r| r.line()).collect();
        assert_eq!(lines, vec![0, 6, 8]);
    }

    #[test]
    fn test_recipe_nodes_matches_descendants() {
        let texts = [
            "a:\n\techo a\nifdef X\n\techo x\nendif\n",
            "ifdef X\na:\n\techo a\nelse ifdef Y\nb:\n\techo b\nendif\n\techo after\n",
            "a: ; inline\n\techo a \\\n\t  continued\n",
            "a:\r\n\techo a\r\nifdef X\r\n\techo x\r\nendif\r\n",
            "define F\n\techo not a recipe\nendef\na:\n\t$(F)\n",
        ];
        for text in texts {
            let makefile = Makefile::from_str_relaxed(text).0;
            let expected: Vec<_> = makefile
                .syntax()
                .descendants()
                .filter_map(Recipe::cast)
                .map(|r| r.syntax().text_range())
                .collect();
            let actual: Vec<_> = makefile
                .recipe_nodes()
                .map(|r| r.syntax().text_range())
                .collect();
            assert_eq!(actual, expected, "{:?}", text);
        }
    }

    #[test]
    fn test_recipe_nodes_continuation_and_crlf() {
        let makefile: Makefile = "a:\r\n\techo a \\\r\n\t  b\r\nifdef X\r\n\techo x\r\nendif\r\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile
                .recipe_nodes()
                .map(|r| r.text())
                .collect::<Vec<_>>(),
            vec!["echo a \\\n  b", "echo x"]
        );
    }

    #[test]
    fn test_recipe_nodes_bsd_for_loop() {
        let makefile = Makefile::parse_with_variant(
            "all:\n.for f in a b\n\techo ${f}\n.endfor\n.if ${X}\n\techo x\n.elif ${Y}\n\techo y\n.endif\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        assert_eq!(
            makefile
                .recipe_nodes()
                .map(|r| r.text())
                .collect::<Vec<_>>(),
            vec!["echo ${f}", "echo x", "echo y"]
        );
    }

    #[test]
    fn test_vpaths() {
        let makefile: Makefile =
            "vpath %.c src\nifdef X\nvpath %.h include\nelse\nifdef Y\nvpath %.o obj\nendif\nendif\nVPATH = dir\nvpath\n"
                .parse()
                .unwrap();
        assert_eq!(
            makefile.vpaths().map(|v| v.pattern()).collect::<Vec<_>>(),
            vec![
                Some("%.c".to_string()),
                Some("%.h".to_string()),
                Some("%.o".to_string()),
                None
            ]
        );
    }

    #[test]
    fn test_expression_statements() {
        let makefile: Makefile = "$(info a)\nifdef X\n$(eval $(call f,x))\nelse\nifdef Y\n$(warning w)\nendif\nendif\nall:\nifdef Z\n$(error e)\nendif\n\techo $(info not a statement)\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile
                .expression_statements()
                .map(|e| e.expression())
                .collect::<Vec<_>>(),
            vec![
                "$(info a)",
                "$(eval $(call f,x))",
                "$(warning w)",
                "$(error e)"
            ]
        );
    }

    #[test]
    fn test_remove_include_in_conditional() {
        let makefile: Makefile = "ifdef X\ninclude b.mk\nendif\n".parse().unwrap();
        makefile.includes().next().unwrap().remove().unwrap();
        assert_eq!(makefile.to_string(), "ifdef X\nendif\n");
    }

    #[test]
    fn test_add_rule() {
        let mut makefile = Makefile::new();
        let rule = makefile.add_rule("rule");
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            Vec::<String>::new()
        );

        assert_eq!(makefile.to_string(), "rule:\n");
    }

    #[test]
    fn test_add_rule_blank_line() {
        let cases = [
            ("", "b:\n"),
            ("all: a\n", "all: a\n\nb:\n"),
            ("all: a\n\n", "all: a\n\nb:\n"),
            ("all: a\n\n\n", "all: a\n\n\nb:\n"),
            ("all:\n\techo\n", "all:\n\techo\n\nb:\n"),
            ("all:\n\techo\n\n", "all:\n\techo\n\nb:\n"),
            ("ifdef X\nall:\nendif\n", "ifdef X\nall:\nendif\n\nb:\n"),
            ("ifdef X\nall:\nendif\n\n", "ifdef X\nall:\nendif\n\nb:\n"),
            ("X = 1\n", "X = 1\n\nb:\n"),
            ("X = 1\n\n", "X = 1\n\nb:\n"),
            ("# comment\n", "# comment\n\nb:\n"),
            ("include a.mk\n", "include a.mk\n\nb:\n"),
            ("\n", "\nb:\n"),
            ("all:\r\n\r\n", "all:\r\n\r\nb:\r\n"),
        ];
        for (text, expected) in cases {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile.add_rule("b");
            assert_eq!(makefile.to_string(), expected, "{text:?}");
            let reparsed: Makefile = expected.parse().unwrap();
            assert_eq!(
                reparsed
                    .rules()
                    .last()
                    .unwrap()
                    .targets()
                    .collect::<Vec<_>>(),
                vec!["b"],
                "{text:?}"
            );
        }
    }

    #[test]
    fn test_add_rule_matches_reparse() {
        for text in [
            "",
            "X = 1\n",
            "X = 1\r\n",
            "X = 1",
            "ifdef X\nall:\nendif\n",
        ] {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile.add_rule("b");
            assert_matches_reparse(&makefile);

            let mut makefile: Makefile = text.parse().unwrap();
            makefile.try_add_rule("$(OBJS)").unwrap();
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_try_add_rule() {
        let mut makefile: Makefile = "all: $(OBJS) a#b\n".parse().unwrap();
        for target in ["$(OBJS)", "a#b", "$(call f,x y)", "lib(a.o)", "a\\ b"] {
            let rule = makefile.try_add_rule(target).unwrap();
            assert_eq!(rule.targets().collect::<Vec<_>>(), vec![target]);
        }
        assert_eq!(
            makefile.to_string(),
            "all: $(OBJS) a#b\n\n$(OBJS):\n\na\\#b:\n\n$(call f,x y):\n\nlib(a.o):\n\na\\ b:\n"
        );
    }

    #[test]
    fn test_try_add_rule_invalid() {
        let mut makefile: Makefile = "all: x\n".parse().unwrap();
        for target in ["", "a b", "a:b", "a\nb", "a=b", "$(X", "a\\"] {
            let Err(Error::Parse(e)) = makefile.try_add_rule(target) else {
                panic!("expected an error for {target:?}");
            };
            assert_eq!(
                e.errors
                    .iter()
                    .map(|e| (e.message.clone(), e.context.as_str()))
                    .collect::<Vec<_>>(),
                vec![(
                    format!("Cannot write {:?} as targets", [target]),
                    "add_rule"
                )]
            );
        }
        assert_eq!(makefile.to_string(), "all: x\n");
    }

    #[test]
    #[should_panic(expected = "invalid target")]
    fn test_add_rule_invalid_panics() {
        Makefile::new().add_rule("a b");
    }

    #[test]
    fn test_add_rule_with_shebang() {
        // Regression test for bug where add_rule() panics on makefiles with shebangs
        let content = r#"#!/usr/bin/make -f

build: blah
	$(MAKE) install

clean:
	dh_clean
"#;

        let mut makefile = Makefile::read_relaxed(content.as_bytes()).unwrap();
        let initial_count = makefile.rules().count();
        assert_eq!(initial_count, 2);

        // This should not panic
        let rule = makefile.add_rule("build-indep");
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["build-indep"]);

        // Should have one more rule now
        assert_eq!(makefile.rules().count(), initial_count + 1);
    }

    #[test]
    fn test_add_rule_formatting() {
        // Regression test for formatting issues when adding rules
        let content = r#"build: blah
	$(MAKE) install

clean:
	dh_clean
"#;

        let mut makefile = Makefile::read_relaxed(content.as_bytes()).unwrap();
        let mut rule = makefile.add_rule("build-indep");
        rule.add_prerequisite("build").unwrap();

        let expected = r#"build: blah
	$(MAKE) install

clean:
	dh_clean

build-indep: build
"#;

        assert_eq!(makefile.to_string(), expected);
    }

    #[test]
    fn test_replace_rule() {
        let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
        let new_rule: Rule = "new_rule:\n\tnew_command\n".parse().unwrap();

        makefile.replace_rule(0, new_rule).unwrap();

        let targets: Vec<_> = makefile
            .rules()
            .flat_map(|r| r.targets().collect::<Vec<_>>())
            .collect();
        assert_eq!(targets, vec!["new_rule", "rule2"]);

        let recipes: Vec<_> = makefile.rules().next().unwrap().recipes().collect();
        assert_eq!(recipes, vec!["new_command"]);
    }

    #[test]
    fn test_replace_rule_out_of_bounds() {
        let mut makefile: Makefile = "rule1:\n\tcommand1\n".parse().unwrap();
        let new_rule: Rule = "new_rule:\n\tnew_command\n".parse().unwrap();

        let result = makefile.replace_rule(5, new_rule);
        assert!(result.is_err());
    }

    #[test]
    fn test_remove_rule() {
        let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\nrule3:\n\tcommand3\n"
            .parse()
            .unwrap();

        let removed = makefile.remove_rule(1).unwrap();
        assert_eq!(removed.targets().collect::<Vec<_>>(), vec!["rule2"]);

        let remaining_targets: Vec<_> = makefile
            .rules()
            .flat_map(|r| r.targets().collect::<Vec<_>>())
            .collect();
        assert_eq!(remaining_targets, vec!["rule1", "rule3"]);
        assert_eq!(makefile.rules().count(), 2);
    }

    #[test]
    fn test_remove_rule_out_of_bounds() {
        let mut makefile: Makefile = "rule1:\n\tcommand1\n".parse().unwrap();

        let result = makefile.remove_rule(5);
        assert!(result.is_err());
    }

    #[test]
    fn test_insert_rule() {
        let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
        let new_rule: Rule = "inserted_rule:\n\tinserted_command\n".parse().unwrap();

        makefile.insert_rule(1, new_rule).unwrap();

        let targets: Vec<_> = makefile
            .rules()
            .flat_map(|r| r.targets().collect::<Vec<_>>())
            .collect();
        assert_eq!(targets, vec!["rule1", "inserted_rule", "rule2"]);
        assert_eq!(makefile.rules().count(), 3);
    }

    #[test]
    fn test_insert_rule_preserves_blank_line_spacing_at_end() {
        // Test that inserting at the end preserves blank line spacing
        let input = "rule1:\n\tcommand1\n\nrule2:\n\tcommand2\n";
        let mut makefile: Makefile = input.parse().unwrap();
        let new_rule = Rule::new(&["rule3"], &[], &["command3"]);

        makefile.insert_rule(2, new_rule).unwrap();

        let expected = "rule1:\n\tcommand1\n\nrule2:\n\tcommand2\n\nrule3:\n\tcommand3\n";
        assert_eq!(makefile.to_string(), expected);
    }

    #[test]
    fn test_insert_rule_adds_blank_lines_when_missing() {
        // Test that inserting adds blank lines even when input has none
        let input = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n";
        let mut makefile: Makefile = input.parse().unwrap();
        let new_rule = Rule::new(&["rule3"], &[], &["command3"]);

        makefile.insert_rule(2, new_rule).unwrap();

        let expected = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n\nrule3:\n\tcommand3\n";
        assert_eq!(makefile.to_string(), expected);
    }

    #[test]
    fn test_rule_manipulation_preserves_structure() {
        // Test that makefile structure (comments, variables, etc.) is preserved during rule manipulation
        let input = r#"# Comment
VAR = value

rule1:
	command1

# Another comment
rule2:
	command2

VAR2 = value2
"#;

        let mut makefile: Makefile = input.parse().unwrap();
        let new_rule: Rule = "new_rule:\n\tnew_command\n".parse().unwrap();

        // Insert rule in the middle
        makefile.insert_rule(1, new_rule).unwrap();

        // Check that rules are correct
        let targets: Vec<_> = makefile
            .rules()
            .flat_map(|r| r.targets().collect::<Vec<_>>())
            .collect();
        assert_eq!(targets, vec!["rule1", "new_rule", "rule2"]);

        // Check that variables are preserved
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars.len(), 2);

        // The structure should be preserved in the output
        let output = makefile.code();
        assert!(output.contains("# Comment"));
        assert!(output.contains("VAR = value"));
        assert!(output.contains("# Another comment"));
        assert!(output.contains("VAR2 = value2"));
    }

    #[test]
    fn test_replace_rule_with_multiple_targets() {
        let mut makefile: Makefile = "target1 target2: dep\n\tcommand\n".parse().unwrap();
        let new_rule: Rule = "new_target: new_dep\n\tnew_command\n".parse().unwrap();

        makefile.replace_rule(0, new_rule).unwrap();

        let targets: Vec<_> = makefile
            .rules()
            .flat_map(|r| r.targets().collect::<Vec<_>>())
            .collect();
        assert_eq!(targets, vec!["new_target"]);
    }

    #[test]
    fn test_empty_makefile_operations() {
        let mut makefile = Makefile::new();

        // Test operations on empty makefile
        assert!(makefile
            .replace_rule(0, "rule:\n\tcommand\n".parse().unwrap())
            .is_err());
        assert!(makefile.remove_rule(0).is_err());

        // Insert into empty makefile should work
        let new_rule: Rule = "first_rule:\n\tcommand\n".parse().unwrap();
        makefile.insert_rule(0, new_rule).unwrap();
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_rule_operations_with_variables_and_includes() {
        let input = r#"VAR1 = value1
include common.mk

rule1:
	command1

VAR2 = value2
include other.mk

rule2:
	command2
"#;

        let mut makefile: Makefile = input.parse().unwrap();

        // Remove middle rule
        makefile.remove_rule(0).unwrap();

        // Verify structure is preserved
        let output = makefile.code();
        assert!(output.contains("VAR1 = value1"));
        assert!(output.contains("include common.mk"));
        assert!(output.contains("VAR2 = value2"));
        assert!(output.contains("include other.mk"));

        // Only rule2 should remain
        assert_eq!(makefile.rules().count(), 1);
        let remaining_targets: Vec<_> = makefile
            .rules()
            .flat_map(|r| r.targets().collect::<Vec<_>>())
            .collect();
        assert_eq!(remaining_targets, vec!["rule2"]);
    }

    #[test]
    fn test_makefile_find_variable() {
        let makefile: Makefile = r#"VAR1 = value1
VAR2 = value2
VAR3 = value3
"#
        .parse()
        .unwrap();

        // Find existing variable
        let vars: Vec<_> = makefile.find_variable("VAR2").collect();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].name(), Some("VAR2".to_string()));
        assert_eq!(vars[0].raw_value(), Some("value2".to_string()));

        // Try to find non-existent variable
        assert_eq!(makefile.find_variable("NONEXISTENT").count(), 0);
    }

    #[test]
    fn test_makefile_find_variable_with_export() {
        let makefile: Makefile = r#"VAR1 = value1
export VAR2 := value2
VAR3 = value3
"#
        .parse()
        .unwrap();

        // Find exported variable
        let vars: Vec<_> = makefile.find_variable("VAR2").collect();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].name(), Some("VAR2".to_string()));
        assert_eq!(vars[0].raw_value(), Some("value2".to_string()));
    }

    #[test]
    fn test_makefile_find_variable_multiple() {
        let makefile: Makefile = r#"VAR1 = value1
VAR1 = value2
VAR2 = other
VAR1 = value3
"#
        .parse()
        .unwrap();

        // Find all VAR1 definitions
        let vars: Vec<_> = makefile.find_variable("VAR1").collect();
        assert_eq!(vars.len(), 3);
        assert_eq!(vars[0].raw_value(), Some("value1".to_string()));
        assert_eq!(vars[1].raw_value(), Some("value2".to_string()));
        assert_eq!(vars[2].raw_value(), Some("value3".to_string()));

        // Find VAR2
        let var2s: Vec<_> = makefile.find_variable("VAR2").collect();
        assert_eq!(var2s.len(), 1);
        assert_eq!(var2s[0].raw_value(), Some("other".to_string()));
    }

    #[test]
    fn test_variable_remove_and_find() {
        let makefile: Makefile = r#"VAR1 = value1
VAR2 = value2
VAR3 = value3
"#
        .parse()
        .unwrap();

        // Find and remove VAR2
        let mut var2 = makefile
            .find_variable("VAR2")
            .next()
            .expect("Should find VAR2");
        var2.remove();

        // Verify VAR2 is gone
        assert_eq!(makefile.find_variable("VAR2").count(), 0);

        // Verify other variables still exist
        assert_eq!(makefile.find_variable("VAR1").count(), 1);
        assert_eq!(makefile.find_variable("VAR3").count(), 1);
    }

    #[test]
    fn test_rule_remove() {
        let makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
        let rule = makefile.find_rule_by_target("rule1").unwrap();
        rule.remove().unwrap();
        assert_eq!(makefile.rules().count(), 1);
        assert!(makefile.find_rule_by_target("rule1").is_none());
        assert!(makefile.find_rule_by_target("rule2").is_some());
    }

    #[test]
    fn test_rule_remove_last_trims_blank_lines() {
        // Regression test for bug where removing the last rule left trailing blank lines
        let makefile: Makefile =
            "%:\n\tdh $@\n\noverride_dh_missing:\n\tdh_missing --fail-missing\n"
                .parse()
                .unwrap();

        // Remove the last rule (override_dh_missing)
        let rule = makefile.find_rule_by_target("override_dh_missing").unwrap();
        rule.remove().unwrap();

        // Should not have trailing blank line
        assert_eq!(makefile.code(), "%:\n\tdh $@\n");
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_insert_rule_before_doc_comment() {
        let cases = [
            ("a:\n# doc\nc:\n", 1, "a:\n\nb:\n\n# doc\nc:\n"),
            (
                "a:\n# doc\n# more\nc:\n",
                1,
                "a:\n\nb:\n\n# doc\n# more\nc:\n",
            ),
            ("# doc\nc:\n", 0, "b:\n\n# doc\nc:\n"),
            (
                "a:\n\techo\n# doc\nc:\n",
                1,
                "a:\n\techo\n\nb:\n\n# doc\nc:\n",
            ),
            (
                "X = 1\n# x\n\n# doc\nc:\n",
                0,
                "X = 1\n# x\n\nb:\n\n# doc\nc:\n",
            ),
            ("X = 1\n# x\n\nc:\n", 0, "X = 1\n# x\n\nb:\n\nc:\n"),
            ("a:\n  c:\n", 1, "a:\n\nb:\n\n  c:\n"),
            ("a:\n  # x\nc:\n", 1, "a:\n\nb:\n\n  # x\nc:\n"),
            ("X = a \\\n# x\nc:\n", 0, "X = a \\\n# x\n\nb:\n\nc:\n"),
            (
                "ifdef X\n# doc\nc:\nendif\n",
                0,
                "ifdef X\nb:\n\n# doc\nc:\nendif\n",
            ),
            (
                "a:\nifdef X\nc:\n\techo\n# doc\nd:\nendif\n",
                2,
                "a:\nifdef X\nc:\n\techo\n\nb:\n\n# doc\nd:\nendif\n",
            ),
        ];
        for (text, index, expected) in cases {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile
                .insert_rule(index, "b:\n".parse().unwrap())
                .unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?} at {index}");
            let reparsed: Makefile = expected.parse().unwrap();
            assert_eq!(
                reparsed
                    .rules()
                    .nth(index)
                    .unwrap()
                    .targets()
                    .collect::<Vec<_>>(),
                vec!["b"],
                "{text:?} at {index}"
            );
            crate::test_util::assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_insert_rule_after_non_doc_comment() {
        // A trailing comment or a shebang does not document the next rule.
        for text in ["X = 1 # x\nc:\n", "#!/usr/bin/make -f\nc:\n"] {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile.insert_rule(0, "b:\n".parse().unwrap()).unwrap();
            let result = makefile.to_string();
            let (before, after) = result.split_once("b:\n").unwrap();
            assert_eq!(before.trim_end(), text.strip_suffix("\nc:\n").unwrap());
            assert_eq!(after, "\nc:\n");
        }
    }

    #[test]
    fn test_replace_rule_keeps_doc_comment() {
        let mut makefile: Makefile = "a:\n\techo\n# doc\nc:\n".parse().unwrap();
        makefile.replace_rule(1, "z:\n".parse().unwrap()).unwrap();
        assert_eq!(makefile.to_string(), "a:\n\techo\n# doc\nz:\n");
    }

    #[test]
    fn test_remove_rule_keeps_doc_comment() {
        let mut makefile: Makefile = "a:\n# doc\nc:\n".parse().unwrap();
        makefile.remove_rule(1).unwrap();
        assert_eq!(makefile.to_string(), "a:\n# doc\n");
    }

    #[test]
    fn test_makefile_find_rule_by_target() {
        let makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
        let rule = makefile.find_rule_by_target("rule2");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().collect::<Vec<_>>(), vec!["rule2"]);
        assert!(makefile.find_rule_by_target("nonexistent").is_none());
    }

    #[test]
    fn test_makefile_find_rules_by_target() {
        let makefile: Makefile = "rule1:\n\tcommand1\nrule1:\n\tcommand2\nrule2:\n\tcommand3\n"
            .parse()
            .unwrap();
        assert_eq!(makefile.find_rules_by_target("rule1").count(), 2);
        assert_eq!(makefile.find_rules_by_target("rule2").count(), 1);
        assert_eq!(makefile.find_rules_by_target("nonexistent").count(), 0);
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_simple() {
        let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("foo.o");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "%.o");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_no_match() {
        let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("foo.c");
        assert!(rule.is_none());
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_exact() {
        let makefile: Makefile = "foo.o: foo.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("foo.o");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "foo.o");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_prefix() {
        let makefile: Makefile = "lib%.a: %.o\n\tar rcs $@ $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("libfoo.a");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "lib%.a");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_suffix() {
        let makefile: Makefile = "%_test.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("foo_test.o");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "%_test.o");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_middle() {
        let makefile: Makefile = "lib%_debug.a: %.o\n\tar rcs $@ $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("libfoo_debug.a");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "lib%_debug.a");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_wildcard_only() {
        let makefile: Makefile = "%: %.c\n\t$(CC) -o $@ $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("anything");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "%");
    }

    #[test]
    fn test_makefile_find_rules_by_target_pattern_multiple() {
        let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n%.o: %.s\n\t$(AS) -o $@ $<\n"
            .parse()
            .unwrap();
        let rules: Vec<_> = makefile.find_rules_by_target_pattern("foo.o").collect();
        assert_eq!(rules.len(), 2);
    }

    #[test]
    fn test_makefile_find_rules_by_target_pattern_mixed() {
        let makefile: Makefile =
        "%.o: %.c\n\t$(CC) -c $<\nfoo.o: foo.h\n\t$(CC) -c foo.c\nbar.txt: baz.txt\n\tcp $< $@\n"
            .parse()
            .unwrap();
        let rules: Vec<_> = makefile.find_rules_by_target_pattern("foo.o").collect();
        assert_eq!(rules.len(), 2); // Matches both %.o and foo.o
        let rules: Vec<_> = makefile.find_rules_by_target_pattern("bar.txt").collect();
        assert_eq!(rules.len(), 1); // Only exact match
    }

    #[test]
    fn test_makefile_find_rules_by_target_pattern_no_wildcard() {
        let makefile: Makefile = "foo.o: foo.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rules: Vec<_> = makefile.find_rules_by_target_pattern("foo.o").collect();
        assert_eq!(rules.len(), 1);
        let rules: Vec<_> = makefile.find_rules_by_target_pattern("bar.o").collect();
        assert_eq!(rules.len(), 0);
    }

    #[test]
    fn test_makefile_add_phony_target() {
        let mut makefile = Makefile::new();
        makefile.add_phony_target("clean").unwrap();
        assert!(makefile.is_phony("clean"));
        assert_eq!(makefile.phony_targets().collect::<Vec<_>>(), vec!["clean"]);
    }

    #[test]
    fn test_makefile_add_phony_target_existing() {
        let mut makefile: Makefile = ".PHONY: test\n".parse().unwrap();
        makefile.add_phony_target("clean").unwrap();
        assert!(makefile.is_phony("test"));
        assert!(makefile.is_phony("clean"));
        let targets: Vec<_> = makefile.phony_targets().collect();
        assert!(targets.contains(&"test".to_string()));
        assert!(targets.contains(&"clean".to_string()));
    }

    #[test]
    fn test_makefile_remove_phony_target() {
        let mut makefile: Makefile = ".PHONY: clean test\n".parse().unwrap();
        assert!(makefile.remove_phony_target("clean").unwrap());
        assert!(!makefile.is_phony("clean"));
        assert!(makefile.is_phony("test"));
        assert!(!makefile.remove_phony_target("nonexistent").unwrap());
    }

    #[test]
    fn test_makefile_remove_phony_target_last() {
        let mut makefile: Makefile = ".PHONY: clean\n".parse().unwrap();
        assert!(makefile.remove_phony_target("clean").unwrap());
        assert!(!makefile.is_phony("clean"));
        // .PHONY rule should be removed entirely
        assert!(makefile.find_rule_by_target(".PHONY").is_none());
    }

    #[test]
    fn test_makefile_is_phony() {
        let makefile: Makefile = ".PHONY: clean test\n".parse().unwrap();
        assert!(makefile.is_phony("clean"));
        assert!(makefile.is_phony("test"));
        assert!(!makefile.is_phony("build"));
    }

    #[test]
    fn test_makefile_phony_targets() {
        let makefile: Makefile = ".PHONY: clean test build\n".parse().unwrap();
        let phony_targets: Vec<_> = makefile.phony_targets().collect();
        assert_eq!(phony_targets, vec!["clean", "test", "build"]);
    }

    #[test]
    fn test_makefile_phony_targets_empty() {
        let makefile = Makefile::new();
        assert_eq!(makefile.phony_targets().count(), 0);
    }

    #[test]
    fn test_makefile_remove_first_phony_target_no_extra_space() {
        let mut makefile: Makefile = ".PHONY: clean test build\n".parse().unwrap();
        assert!(makefile.remove_phony_target("clean").unwrap());
        let result = makefile.to_string();
        assert_eq!(result, ".PHONY: test build\n");
    }

    #[test]
    fn test_add_conditional_ifdef() {
        let mut makefile = Makefile::new();
        let result = makefile.add_conditional("ifdef", "DEBUG", "VAR = debug\n", None);
        assert!(result.is_ok());

        let code = makefile.to_string();
        assert!(code.contains("ifdef DEBUG"));
        assert!(code.contains("VAR = debug"));
        assert!(code.contains("endif"));
    }

    #[test]
    fn test_add_conditional_with_else() {
        let mut makefile = Makefile::new();
        let result =
            makefile.add_conditional("ifdef", "DEBUG", "VAR = debug\n", Some("VAR = release\n"));
        assert!(result.is_ok());

        let code = makefile.to_string();
        assert!(code.contains("ifdef DEBUG"));
        assert!(code.contains("VAR = debug"));
        assert!(code.contains("else"));
        assert!(code.contains("VAR = release"));
        assert!(code.contains("endif"));
    }

    #[test]
    fn test_add_conditional_body_without_trailing_newline() {
        let mut makefile: Makefile = "X = 1\n".parse().unwrap();
        makefile
            .add_conditional("ifdef", "DEBUG", "Y = 1\nZ = 1", Some("Y = 2"))
            .unwrap();
        let text = makefile.to_string();
        assert_eq!(
            text,
            "X = 1\n\nifdef DEBUG\nY = 1\nZ = 1\nelse\nY = 2\nendif\n"
        );
        assert_eq!(text.parse::<Makefile>().unwrap().to_string(), text);
    }

    #[test]
    fn test_add_conditional_if_body_without_trailing_newline() {
        let mut makefile = Makefile::new();
        makefile
            .add_conditional("ifdef", "DEBUG", "Y = 1", None)
            .unwrap();
        assert_eq!(makefile.to_string(), "ifdef DEBUG\nY = 1\nendif\n");
    }

    #[test]
    fn test_add_conditional_body_with_trailing_newline() {
        let mut makefile = Makefile::new();
        makefile
            .add_conditional("ifdef", "DEBUG", "Y = 1\n", Some("Y = 2\n"))
            .unwrap();
        assert_eq!(
            makefile.to_string(),
            "ifdef DEBUG\nY = 1\nelse\nY = 2\nendif\n"
        );
    }

    #[test]
    fn test_add_conditional_body_ending_in_blank_line() {
        let mut makefile = Makefile::new();
        makefile
            .add_conditional("ifdef", "DEBUG", "Y = 1\n\n", Some("Y = 2\n\n"))
            .unwrap();
        assert_eq!(
            makefile.to_string(),
            "ifdef DEBUG\nY = 1\n\nelse\nY = 2\n\nendif\n"
        );
    }

    #[test]
    fn test_insert_rule_blank_line_in_rule() {
        // The parser puts blank lines after a rule in the rule, as they
        // don't end its recipe.
        let cases = [
            ("a:\n", 1, "a:\n\nb:\n"),
            ("a:\n\techo\n", 1, "a:\n\techo\n\nb:\n"),
            ("a: c\n# x\n", 1, "a: c\n# x\n\nb:\n"),
            ("a:\n", 0, "b:\n\na:\n"),
            ("a:\nc:\n", 1, "a:\n\nb:\n\nc:\n"),
            (
                "ifdef X\na:\nc:\nendif\n",
                1,
                "ifdef X\na:\n\nb:\n\nc:\nendif\n",
            ),
            ("a: X = 1\n", 1, "a: X = 1\n\nb:\n"),
        ];
        for (text, index, expected) in cases {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile
                .insert_rule(index, "b:\n".parse().unwrap())
                .unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?} at {index}");
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_add_conditional_after_rule_matches_reparse() {
        for text in [
            "a:\n",
            "a:\n\techo\n",
            "a: b\n# c\n",
            "a:\n\techo \\",
            "a: X = 1\n",
        ] {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile.add_conditional("ifdef", "X", "", None).unwrap();
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_add_rule_after_rule() {
        let mut makefile: Makefile = "a:\n\techo\n".parse().unwrap();
        makefile.add_rule("b");
        assert_eq!(makefile.to_string(), "a:\n\techo\n\nb:\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_rule_after_unterminated_line() {
        let mut makefile: Makefile = "X = 1".parse().unwrap();
        makefile.add_rule("b");
        assert_eq!(makefile.to_string(), "X = 1\n\nb:\n");
    }

    #[test]
    fn test_add_rule_after_unterminated_define() {
        let mut makefile: Makefile = "define V\nx\nendef".parse().unwrap();
        makefile.add_rule("b");
        assert_eq!(makefile.to_string(), "define V\nx\nendef\n\nb:\n");
    }

    #[test]
    fn test_add_rule_after_unterminated_conditional() {
        let mut makefile: Makefile = "ifdef X\nY = 1\nendif".parse().unwrap();
        makefile.add_rule("b");
        assert_eq!(makefile.to_string(), "ifdef X\nY = 1\nendif\n\nb:\n");
    }

    #[test]
    fn test_add_conditional_blank_line() {
        let cases = [
            ("", "ifdef D\nY = 1\nendif\n"),
            ("all: a\n", "all: a\n\nifdef D\nY = 1\nendif\n"),
            ("all: a\n\n", "all: a\n\nifdef D\nY = 1\nendif\n"),
            ("all: a\n\n\n", "all: a\n\n\nifdef D\nY = 1\nendif\n"),
            ("X = 1\n", "X = 1\n\nifdef D\nY = 1\nendif\n"),
            ("X = 1\n\n", "X = 1\n\nifdef D\nY = 1\nendif\n"),
            ("# comment\n", "# comment\n\nifdef D\nY = 1\nendif\n"),
            ("include a.mk\n", "include a.mk\n\nifdef D\nY = 1\nendif\n"),
            ("\n", "\nifdef D\nY = 1\nendif\n"),
            ("all:\r\n\r\n", "all:\r\n\r\nifdef D\r\nY = 1\r\nendif\r\n"),
        ];
        for (text, expected) in cases {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile
                .add_conditional("ifdef", "D", "Y = 1\n", None)
                .unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?}");

            let mut makefile: Makefile = text.parse().unwrap();
            let items: Makefile = "Y = 1\n".parse().unwrap();
            makefile
                .add_conditional_with_items("ifdef", "D", items.items(), None::<Vec<MakefileItem>>)
                .unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?}");

            let reparsed: Makefile = expected.parse().unwrap();
            assert_eq!(reparsed.to_string(), expected);
            let conditional = reparsed.conditionals().last().unwrap();
            assert_eq!(conditional.conditional_type(), Some("ifdef".to_string()));
            assert_eq!(
                reparsed.variable_definitions().last().unwrap().raw_value(),
                Some("1".to_string())
            );
        }
    }

    #[test]
    fn test_add_conditional_matches_reparse() {
        let bodies = [
            "VAR = debug\n",
            "a: b\n\techo $@\n\nX := $(Y)\n",
            "ifdef Y\nZ = 1\nelse\nZ = 2\nendif\n",
            "include a.mk\n# comment\n\n",
            "export X\n",
        ];
        for prefix in ["", "X = 1\n", "X = 1\r\n"] {
            for body in bodies {
                let mut makefile: Makefile = prefix.parse().unwrap();
                makefile
                    .add_conditional("ifeq", "($(A),b)", body, Some(body))
                    .unwrap();
                assert_matches_reparse(&makefile);

                let mut makefile: Makefile = prefix.parse().unwrap();
                let items: Makefile = body.parse().unwrap();
                makefile
                    .add_conditional_with_items("ifdef", "D", items.items(), Some(items.items()))
                    .unwrap();
                assert_matches_reparse(&makefile);
            }
        }
    }

    #[test]
    fn test_add_conditional_items_accessible() {
        let mut makefile = Makefile::new();
        let cond = makefile
            .add_conditional("ifdef", "D", "a: b\n\techo\nX = 1\n", Some("Y = 2\n"))
            .unwrap();
        assert_eq!(cond.condition(), Some("D".to_string()));
        assert_eq!(cond.if_items().count(), 2);
        assert_eq!(cond.else_items().count(), 1);
        assert_eq!(makefile.rules().count(), 1);
        assert_eq!(
            makefile
                .variable_definitions()
                .map(|v| v.name().unwrap())
                .collect::<Vec<_>>(),
            vec!["X", "Y"]
        );
    }

    #[test]
    fn test_add_conditional_with_items_without_newline() {
        let mut makefile = Makefile::new();
        let first: Makefile = "X = 1".parse().unwrap();
        let second: Makefile = "Y = 2\n".parse().unwrap();
        makefile
            .add_conditional_with_items(
                "ifdef",
                "D",
                first.items().chain(second.items()),
                Some(first.items()),
            )
            .unwrap();
        assert_eq!(
            makefile.to_string(),
            "ifdef D\nX = 1\nY = 2\nelse\nX = 1\nendif\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_conditional_with_items_crlf_item() {
        let mut makefile = Makefile::new();
        let items: Makefile = "a:\r\n\techo\r\n".parse().unwrap();
        makefile
            .add_conditional_with_items("ifdef", "D", items.items(), None::<Vec<MakefileItem>>)
            .unwrap();
        assert_eq!(makefile.to_string(), "ifdef D\na:\n\techo\nendif\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_conditional_rejects_invalid_body() {
        let mut makefile: Makefile = "X = 1\n".parse().unwrap();
        for body in ["endif\n", "ifdef Y\n", "define V\n"] {
            assert!(
                makefile.add_conditional("ifdef", "D", body, None).is_err(),
                "{body:?}"
            );
        }
        assert_eq!(makefile.to_string(), "X = 1\n");
    }

    #[test]
    fn test_add_conditional_after_unterminated_line() {
        let mut makefile: Makefile = "X = 1".parse().unwrap();
        makefile
            .add_conditional("ifdef", "D", "Y = 1\n", None)
            .unwrap();
        assert_eq!(makefile.to_string(), "X = 1\n\nifdef D\nY = 1\nendif\n");
    }

    #[test]
    fn test_add_conditional_with_items_after_unterminated_line() {
        let mut makefile: Makefile = "X = 1".parse().unwrap();
        let items: Makefile = "Y = 1\n".parse().unwrap();
        makefile
            .add_conditional_with_items("ifdef", "D", items.items(), None::<Vec<MakefileItem>>)
            .unwrap();
        assert_eq!(makefile.to_string(), "X = 1\n\nifdef D\nY = 1\nendif\n");
    }

    #[test]
    fn test_insert_rule_after_unterminated_line() {
        let mut makefile: Makefile = "a:".parse().unwrap();
        makefile.insert_rule(1, "b:\n".parse().unwrap()).unwrap();
        assert_eq!(makefile.to_string(), "a:\n\nb:\n");

        let mut makefile: Makefile = "X = 1".parse().unwrap();
        makefile.insert_rule(0, "b:\n".parse().unwrap()).unwrap();
        assert_eq!(makefile.to_string(), "X = 1\n\nb:\n");
    }

    #[test]
    fn test_insert_include_after_unterminated() {
        let mut makefile: Makefile = "X = 1".parse().unwrap();
        makefile.insert_include(1, "a.mk").unwrap();
        assert_eq!(makefile.to_string(), "X = 1\ninclude a.mk\n");
        assert_matches_reparse(&makefile);

        let mut makefile: Makefile = "X = 1".parse().unwrap();
        let first = makefile.items().next().unwrap();
        let include = makefile.insert_include_after(&first, "a.mk").unwrap();
        assert_eq!(include.path(), Some("a.mk".to_string()));
        assert_eq!(makefile.to_string(), "X = 1\ninclude a.mk\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_add_after_unterminated_continuation() {
        // A newline after the backslash would continue the line onto the
        // new item, so a blank line ends the continuation.
        let cases = [
            ("X = a \\", "X = a \\\n\n"),
            ("X = a \\\\\\", "X = a \\\\\\\n\n"),
            ("# c \\", "# c \\\n\n"),
            ("a: x \\", "a: x \\\n\n"),
            ("a: x\\", "a: x\\\n\n"),
            ("a: x \\\\\\", "a: x \\\\\\\n\n"),
            ("a:\n\techo \\", "a:\n\techo \\\n\n"),
            ("include a.mk \\", "include a.mk \\\n\n"),
        ];
        for (text, expected) in cases {
            let mut makefile: Makefile = text.parse().unwrap();
            makefile.add_rule("b");
            assert_eq!(makefile.to_string(), format!("{expected}b:\n"), "{text:?}");

            let (mut makefile, _) = Makefile::from_str_relaxed(text);
            let index = makefile.items().count();
            makefile.insert_include(index, "b.mk").unwrap();
            assert_eq!(
                makefile.to_string(),
                format!("{expected}include b.mk\n"),
                "{text:?}"
            );
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_add_after_unterminated_escaped_backslash() {
        let mut makefile: Makefile = "X = a\\\\".parse().unwrap();
        makefile.insert_include(1, "b.mk").unwrap();
        assert_eq!(makefile.to_string(), "X = a\\\\\ninclude b.mk\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_insert_include_after_unterminated_continuation() {
        let mut makefile: Makefile = "X = a \\".parse().unwrap();
        makefile.insert_include(1, "b.mk").unwrap();
        assert_eq!(makefile.to_string(), "X = a \\\n\ninclude b.mk\n");
        assert_eq!(makefile.includes().count(), 1);
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_push_command_after_unterminated_continuation() {
        let makefile: Makefile = "a:\n\techo a \\".parse().unwrap();
        let mut rule = makefile.rules().next().unwrap();
        rule.push_command("echo b");
        assert_eq!(makefile.to_string(), "a:\n\techo a \\\n\n\techo b\n");
        assert_eq!(rule.recipe_count(), 2);
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_insert_include_index_skips_blank_lines() {
        let cases = [
            ("X = 1\n\nY = 2\n", 0, "include a.mk\nX = 1\n\nY = 2\n"),
            ("X = 1\n\nY = 2\n", 1, "X = 1\n\ninclude a.mk\nY = 2\n"),
            ("X = 1\n\nY = 2\n", 2, "X = 1\n\nY = 2\ninclude a.mk\n"),
            ("\n\nX = 1\n", 0, "\n\ninclude a.mk\nX = 1\n"),
            ("\n\nX = 1\n", 1, "\n\nX = 1\ninclude a.mk\n"),
            ("X = 1\n\n", 1, "X = 1\n\ninclude a.mk\n"),
            ("a:\n\techo\n\nb:\n", 1, "a:\n\techo\n\ninclude a.mk\nb:\n"),
            (
                "X = 1\n\n# doc\nY = 2\n",
                1,
                "X = 1\n\ninclude a.mk\n# doc\nY = 2\n",
            ),
        ];
        for (text, index, expected) in cases {
            let mut makefile: Makefile = text.parse().unwrap();
            let include = makefile.insert_include(index, "a.mk").unwrap();
            assert_eq!(makefile.to_string(), expected, "{text:?} at {index}");
            assert_eq!(include.path(), Some("a.mk".to_string()));
            assert_eq!(
                makefile.items().nth(index).unwrap().syntax(),
                include.syntax(),
                "{text:?} at {index}"
            );
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_insert_include_index_out_of_bounds_with_blank_lines() {
        let mut makefile: Makefile = "X = 1\n\nY = 2\n".parse().unwrap();
        let Err(err) = makefile.insert_include(3, "a.mk") else {
            panic!("expected an error");
        };
        assert_eq!(
            err.to_string(),
            "Parse error: Error at line 1: Index 3 out of bounds (max 2)\n1| insert_include\n"
        );
        assert_eq!(makefile.to_string(), "X = 1\n\nY = 2\n");
    }

    #[test]
    fn test_insert_include_after_nested_item() {
        let mut makefile: Makefile = "ifdef X\nA = 1\nendif\nB = 2\n".parse().unwrap();
        let a = makefile
            .conditionals()
            .next()
            .unwrap()
            .if_items()
            .next()
            .unwrap();
        let include = makefile.insert_include_after(&a, "a.mk").unwrap();
        assert_eq!(include.path(), Some("a.mk".to_string()));
        assert_eq!(
            makefile.to_string(),
            "ifdef X\nA = 1\ninclude a.mk\nendif\nB = 2\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_insert_include_after_nested_item_before_doc_comment() {
        let mut makefile: Makefile = "ifdef X\nA = 1\n# doc\nB = 2\nendif\n".parse().unwrap();
        let a = makefile
            .conditionals()
            .next()
            .unwrap()
            .if_items()
            .next()
            .unwrap();
        makefile.insert_include_after(&a, "a.mk").unwrap();
        assert_eq!(
            makefile.to_string(),
            "ifdef X\nA = 1\ninclude a.mk\n# doc\nB = 2\nendif\n"
        );
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_insert_include_after_foreign_item() {
        let mut makefile: Makefile = "A = 1\n".parse().unwrap();
        let other: Makefile = "B = 2\n".parse().unwrap();
        let b = other.items().next().unwrap();
        let Err(err) = makefile.insert_include_after(&b, "a.mk") else {
            panic!("expected an error");
        };
        assert_eq!(
            err.to_string(),
            "Parse error: Error at line 1: Could not find the reference item\n1| insert_include_after\n"
        );
        assert_eq!(makefile.to_string(), "A = 1\n");
        assert_eq!(other.to_string(), "B = 2\n");
    }

    #[test]
    fn test_add_phony_target_after_unterminated_line() {
        let mut makefile: Makefile = "X = 1".parse().unwrap();
        makefile.add_phony_target("clean").unwrap();
        assert_eq!(makefile.to_string(), "X = 1\n\n.PHONY: clean\n");
    }

    #[test]
    fn test_add_conditional_invalid_type() {
        let mut makefile = Makefile::new();
        let result = makefile.add_conditional("invalid", "DEBUG", "VAR = debug\n", None);
        assert!(result.is_err());
    }

    #[test]
    fn test_add_conditional_rejects_invalid_condition() {
        let cases = [
            ("ifdef", "A B"),
            ("ifeq", ""),
            ("ifeq", "()"),
            ("ifneq", "(a)"),
            ("ifeq", "a,b"),
            (".if", ""),
            (".if", " "),
            (".ifdef", ""),
            (".ifndef", ""),
            (".ifmake", ""),
            (".ifnmake", ""),
        ];
        for (conditional_type, condition) in cases {
            let mut makefile: Makefile = "X = 1\n".parse().unwrap();
            assert!(
                makefile
                    .add_conditional(conditional_type, condition, "Y = 1\n", None)
                    .is_err(),
                "{conditional_type} {condition:?}"
            );
            let items: Makefile = "Y = 1\n".parse().unwrap();
            assert!(
                makefile
                    .add_conditional_with_items(
                        conditional_type,
                        condition,
                        items.items(),
                        None::<Vec<MakefileItem>>
                    )
                    .is_err(),
                "{conditional_type} {condition:?}"
            );
            assert_eq!(makefile.to_string(), "X = 1\n");
        }
    }

    #[test]
    fn test_add_conditional_bsd_empty_condition_error() {
        let mut makefile = Makefile::new();
        let Err(error) = makefile.add_conditional(".ifdef", "", "Y = 1\n", None) else {
            panic!("empty condition accepted");
        };
        assert_eq!(
            error.to_string(),
            "Parse error: Error at line 1: expected condition after .ifdef\n1| .ifdef\n"
        );
    }

    #[test]
    fn test_add_conditional_empty_ifdef() {
        for conditional_type in ["ifdef", "ifndef"] {
            let mut makefile = Makefile::new();
            let cond = makefile
                .add_conditional(conditional_type, "", "", None)
                .unwrap();
            assert_eq!(cond.condition(), Some(String::new()));
            assert_eq!(makefile.to_string(), format!("{conditional_type}\nendif\n"));
            assert_matches_reparse(&makefile);

            let mut makefile = Makefile::new();
            makefile
                .add_conditional_with_items(
                    conditional_type,
                    "",
                    std::iter::empty(),
                    None::<Vec<MakefileItem>>,
                )
                .unwrap();
            assert_eq!(makefile.to_string(), format!("{conditional_type}\nendif\n"));
            assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_add_conditional_rejects_invalid_branches() {
        let cases = [
            ("ifdef", "else\nX = 1\n", None),
            ("ifdef", "X = 1\n", Some("else\nY = 2\n")),
            ("ifdef", "else\nX = 1\n", Some("Y = 2\n")),
            ("ifdef", "X = 1\nelse ifdef B\nY = 1\n", None),
            ("ifdef", "endif\n", None),
            ("ifdef", "ifdef B\n", None),
            ("ifdef", "define V\n", None),
            (".if", "X = 1\n.else\nY = 2\n", None),
            (".if", "X = 1\n.elif defined(B)\nY = 2\n", None),
        ];
        for (conditional_type, if_body, else_body) in cases {
            let mut makefile: Makefile = "X = 1\n".parse().unwrap();
            let condition = if conditional_type == ".if" {
                "defined(A)"
            } else {
                "A"
            };
            assert!(
                makefile
                    .add_conditional(conditional_type, condition, if_body, else_body)
                    .is_err(),
                "{if_body:?} {else_body:?}"
            );
            assert_eq!(makefile.to_string(), "X = 1\n");
        }
    }

    #[test]
    fn test_add_conditional_nested_else() {
        let mut makefile = Makefile::new();
        let body = "ifdef B\nX = 1\nelse\nX = 2\nendif\n";
        makefile
            .add_conditional("ifeq", "(,)", body, Some(body))
            .unwrap();
        assert_eq!(
            makefile.to_string(),
            format!("ifeq (,)\n{body}else\n{body}endif\n")
        );
    }

    #[test]
    fn test_add_conditional_formatting() {
        let mut makefile: Makefile = "VAR1 = value1\n".parse().unwrap();
        let result = makefile.add_conditional("ifdef", "DEBUG", "VAR = debug\n", None);
        assert!(result.is_ok());

        let code = makefile.to_string();
        // Should have a blank line before the conditional
        assert!(code.contains("\n\nifdef DEBUG"));
    }

    #[test]
    fn test_add_conditional_ifndef() {
        let mut makefile = Makefile::new();
        let result = makefile.add_conditional("ifndef", "NDEBUG", "VAR = enabled\n", None);
        assert!(result.is_ok());

        let code = makefile.to_string();
        assert!(code.contains("ifndef NDEBUG"));
        assert!(code.contains("VAR = enabled"));
        assert!(code.contains("endif"));
    }

    #[test]
    fn test_add_conditional_ifeq() {
        let mut makefile = Makefile::new();
        let result = makefile.add_conditional("ifeq", "($(OS),Linux)", "VAR = linux\n", None);
        assert!(result.is_ok());

        let code = makefile.to_string();
        assert!(code.contains("ifeq ($(OS),Linux)"));
        assert!(code.contains("VAR = linux"));
        assert!(code.contains("endif"));
    }

    #[test]
    fn test_add_conditional_ifneq() {
        let mut makefile = Makefile::new();
        let result = makefile.add_conditional("ifneq", "($(OS),Windows)", "VAR = unix\n", None);
        assert!(result.is_ok());

        let code = makefile.to_string();
        assert!(code.contains("ifneq ($(OS),Windows)"));
        assert!(code.contains("VAR = unix"));
        assert!(code.contains("endif"));
    }

    #[test]
    fn test_item_replace_without_newline() {
        let makefile: Makefile = "X = 1\nY = 1\n".parse().unwrap();
        let mut first = makefile.items().next().unwrap();
        first.replace(item_without_newline("Z = 1")).unwrap();
        assert_eq!(makefile.to_string(), "Z = 1\nY = 1\n");
        assert_eq!(first.syntax().to_string(), "Z = 1\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_replace_rule_without_newline() {
        let mut makefile: Makefile = "a:\nb:\n".parse().unwrap();
        makefile
            .replace_rule(0, "c:\n\tcmd".parse().unwrap())
            .unwrap();
        assert_eq!(makefile.to_string(), "c:\n\tcmd\nb:\n");
        assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_insert_rule_without_newline() {
        let mut makefile: Makefile = "a:\nb:\n".parse().unwrap();
        makefile.insert_rule(0, "c:".parse().unwrap()).unwrap();
        makefile.insert_rule(2, "d:".parse().unwrap()).unwrap();
        makefile.insert_rule(4, "e:".parse().unwrap()).unwrap();
        assert_eq!(makefile.to_string(), "c:\n\na:\n\nd:\n\nb:\n\ne:\n");
    }

    #[test]
    fn test_add_conditional_with_items() {
        let mut makefile = Makefile::new();

        // Parse items from temporary makefiles
        let temp1: Makefile = "CFLAGS = -g\n".parse().unwrap();
        let var1 = temp1.variable_definitions().next().unwrap();

        let temp2: Makefile = "CFLAGS = -O2\n".parse().unwrap();
        let var2 = temp2.variable_definitions().next().unwrap();

        let temp3: Makefile = "debug:\n\techo debug\n".parse().unwrap();
        let rule1 = temp3.rules().next().unwrap();

        let result = makefile.add_conditional_with_items(
            "ifdef",
            "DEBUG",
            vec![MakefileItem::Variable(var1), MakefileItem::Rule(rule1)],
            Some(vec![MakefileItem::Variable(var2)]),
        );

        assert!(result.is_ok());

        let code = makefile.to_string();
        assert!(code.contains("ifdef DEBUG"));
        assert!(code.contains("CFLAGS = -g"));
        assert!(code.contains("debug:"));
        assert!(code.contains("else"));
        assert!(code.contains("CFLAGS = -O2"));
    }

    #[test]
    fn test_makefile_items_iterator() {
        let makefile: Makefile = r#"VAR = value
ifdef DEBUG
CFLAGS = -g
endif
rule:
	command
include common.mk
"#
        .parse()
        .unwrap();

        // First verify we can find each type individually
        // variable_definitions() is recursive, so it finds VAR and CFLAGS (inside conditional)
        assert_eq!(makefile.variable_definitions().count(), 2);
        assert_eq!(makefile.conditionals().count(), 1);
        assert_eq!(makefile.rules().count(), 1);

        let items: Vec<_> = makefile.items().collect();
        // Note: include directives might not be at top level, need to check
        assert!(
            items.len() >= 3,
            "Expected at least 3 items, got {}",
            items.len()
        );

        match &items[0] {
            MakefileItem::Variable(v) => {
                assert_eq!(v.name(), Some("VAR".to_string()));
            }
            _ => panic!("Expected variable at position 0"),
        }

        match &items[1] {
            MakefileItem::Conditional(c) => {
                assert_eq!(c.conditional_type(), Some("ifdef".to_string()));
            }
            _ => panic!("Expected conditional at position 1"),
        }

        match &items[2] {
            MakefileItem::Rule(r) => {
                let targets: Vec<_> = r.targets().collect();
                assert_eq!(targets, vec!["rule"]);
            }
            _ => panic!("Expected rule at position 2"),
        }
    }

    #[test]
    fn test_item_parent_in_conditional() {
        let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
rule:
	command
endif
"#
        .parse()
        .unwrap();

        let cond = makefile.conditionals().next().unwrap();

        // Get items from the conditional
        let items: Vec<_> = cond.if_items().collect();
        assert_eq!(items.len(), 2);

        // Check variable parent is the conditional
        if let MakefileItem::Variable(var) = &items[0] {
            let parent = var.parent();
            assert!(parent.is_some());
            if let Some(MakefileItem::Conditional(_)) = parent {
                // Expected - parent is a conditional
            } else {
                panic!("Expected variable parent to be a Conditional");
            }
        } else {
            panic!("Expected first item to be a Variable");
        }

        // Check rule parent is the conditional
        if let MakefileItem::Rule(rule) = &items[1] {
            let parent = rule.parent();
            assert!(parent.is_some());
            if let Some(MakefileItem::Conditional(_)) = parent {
                // Expected - parent is a conditional
            } else {
                panic!("Expected rule parent to be a Conditional");
            }
        } else {
            panic!("Expected second item to be a Rule");
        }
    }

    #[test]
    fn test_nested_conditional_parent() {
        let makefile: Makefile = r#"ifdef OUTER
VAR = outer
ifdef INNER
VAR2 = inner
endif
endif
"#
        .parse()
        .unwrap();

        let outer_cond = makefile.conditionals().next().unwrap();

        // Get inner conditional from outer conditional's items
        let items: Vec<_> = outer_cond.if_items().collect();

        // Find the nested conditional
        let inner_cond = items
            .iter()
            .find_map(|item| {
                if let MakefileItem::Conditional(c) = item {
                    Some(c)
                } else {
                    None
                }
            })
            .unwrap();

        // Inner conditional's parent should be the outer conditional
        let parent = inner_cond.parent();
        assert!(parent.is_some());
        if let Some(MakefileItem::Conditional(_)) = parent {
            // Expected - parent is a conditional
        } else {
            panic!("Expected inner conditional's parent to be a Conditional");
        }
    }

    #[test]
    fn test_item_text_range() {
        let makefile: Makefile = "A = 1\nifdef X\nrule:\n\tcmd\nendif\n".parse().unwrap();
        let ranges: Vec<_> = makefile.items().map(|i| i.text_range()).collect();
        assert_eq!(
            ranges,
            vec![
                rowan::TextRange::new(0.into(), 6.into()),
                rowan::TextRange::new(6.into(), 31.into()),
            ]
        );
        let cond = makefile.conditionals().next().unwrap();
        let branch = cond.branches().next().unwrap();
        let ranges: Vec<_> = branch.items().map(|i| i.text_range()).collect();
        assert_eq!(ranges, vec![rowan::TextRange::new(14.into(), 25.into())]);
    }
}
