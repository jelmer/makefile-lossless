use super::rule::build_targets_node;
use super::{line_ending, terminate_line_before, with_trailing_newline};
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

/// Whether an item appended to `root` needs a blank line before it, i.e.
/// the makefile is neither empty nor already ends in a blank line. The
/// text must end in a line ending unless empty; see
/// [`terminate_line_before`].
fn needs_blank_line_at_end(root: &SyntaxNode) -> bool {
    let text = root.text().to_string();
    let Some(body) = text.strip_suffix('\n') else {
        return false;
    };
    let last_line = body.rsplit('\n').next().unwrap_or(body);
    !last_line.trim().is_empty()
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

    /// Check if a token is a regular comment (not a shebang)
    fn is_regular_comment(token: &rowan::SyntaxToken<crate::lossless::Lang>) -> bool {
        token.kind() == COMMENT && !token.text().starts_with("#!")
    }

    /// Extract comment text from a comment token, removing '#' prefix
    fn extract_comment_text(token: &rowan::SyntaxToken<crate::lossless::Lang>) -> String {
        let text = token.text();
        text.strip_prefix("# ")
            .or_else(|| text.strip_prefix('#'))
            .unwrap_or(text)
            .to_string()
    }

    /// Helper to find all preceding comment-related elements up to the first non-comment element
    ///
    /// Returns elements in reverse order (from closest to furthest from the item)
    fn collect_preceding_comment_elements(
        &self,
    ) -> Vec<rowan::NodeOrToken<SyntaxNode, rowan::SyntaxToken<crate::lossless::Lang>>> {
        let mut elements = Vec::new();
        let mut current = self.syntax().prev_sibling_or_token();

        while let Some(element) = current {
            match &element {
                rowan::NodeOrToken::Token(token) if Self::is_regular_comment(token) => {
                    elements.push(element.clone());
                }
                rowan::NodeOrToken::Token(token)
                    if token.kind() == NEWLINE || token.kind() == WHITESPACE =>
                {
                    elements.push(element.clone());
                }
                rowan::NodeOrToken::Node(n) if n.kind() == BLANK_LINE => {
                    elements.push(element.clone());
                }
                rowan::NodeOrToken::Token(token) if token.kind() == COMMENT => {
                    // Hit a shebang, stop here
                    break;
                }
                _ => break,
            }
            current = element.prev_sibling_or_token();
        }

        elements
    }

    /// Helper to parse comment text and extract properly formatted comment tokens
    fn parse_comment_tokens(
        comment_text: &str,
        eol: &str,
    ) -> (
        rowan::SyntaxToken<crate::lossless::Lang>,
        Option<rowan::SyntaxToken<crate::lossless::Lang>>,
    ) {
        let comment_line = format!("# {}{}", comment_text, eol);
        let temp_makefile = crate::lossless::parse(&comment_line, None);
        let root = temp_makefile.root();

        let mut comment_token = None;
        let mut newline_token = None;
        let mut found_comment = false;

        for element in root.syntax().children_with_tokens() {
            if let rowan::NodeOrToken::Token(token) = element {
                if token.kind() == COMMENT {
                    comment_token = Some(token);
                    found_comment = true;
                } else if token.kind() == NEWLINE && found_comment && newline_token.is_none() {
                    newline_token = Some(token);
                    break;
                }
            }
        }

        (
            comment_token.expect("Failed to extract comment token"),
            newline_token,
        )
    }

    /// Replace this MakefileItem with another MakefileItem
    ///
    /// This preserves the position of the original item but replaces its content
    /// with the new item. Preceding comments are preserved.
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
        let current_index = self.syntax().index();
        let new_node = with_trailing_newline(new_item.syntax(), &line_ending(&parent));

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
            Self::parse_comment_tokens(comment_text, &line_ending(self.syntax()));

        let mut elements = vec![rowan::NodeOrToken::Token(comment_token)];
        if let Some(newline) = newline_token {
            elements.push(rowan::NodeOrToken::Token(newline));
        }

        // Insert comment and newline before the current item
        parent.splice_children(current_index..current_index, elements);

        Ok(())
    }

    /// Get all preceding comments for this MakefileItem
    ///
    /// Returns an iterator of comment strings (without the leading '#' and whitespace).
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
        let elements = self.collect_preceding_comment_elements();
        let mut comments = Vec::new();

        // Process elements in reverse order (furthest to closest)
        for element in elements.iter().rev() {
            if let rowan::NodeOrToken::Token(token) = element {
                if token.kind() == COMMENT {
                    comments.push(Self::extract_comment_text(token));
                }
            }
        }

        comments.into_iter()
    }

    /// Remove all preceding comments for this MakefileItem
    ///
    /// Returns the number of comments removed.
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
        let parent = self.get_parent_or_error("remove comments from", "remove_comments")?;
        let collected_elements = self.collect_preceding_comment_elements();

        // Count the comments
        let mut comment_count = 0;
        for element in collected_elements.iter() {
            if let rowan::NodeOrToken::Token(token) = element {
                if token.kind() == COMMENT {
                    comment_count += 1;
                }
            }
        }

        // Determine which elements to remove - similar to remove_with_preceding_comments
        // We remove comments and up to 1 blank line worth of newlines
        let mut elements_to_remove = Vec::new();
        let mut consecutive_newlines = 0;
        for element in collected_elements.iter().rev() {
            let should_remove = match element {
                rowan::NodeOrToken::Token(token) if token.kind() == COMMENT => {
                    consecutive_newlines = 0;
                    true // Remove comments
                }
                rowan::NodeOrToken::Token(token) if token.kind() == NEWLINE => {
                    consecutive_newlines += 1;
                    comment_count > 0 && consecutive_newlines <= 1
                }
                rowan::NodeOrToken::Token(token) if token.kind() == WHITESPACE => comment_count > 0,
                rowan::NodeOrToken::Node(n) if n.kind() == BLANK_LINE => {
                    consecutive_newlines += 1;
                    comment_count > 0 && consecutive_newlines <= 1
                }
                _ => false,
            };

            if should_remove {
                elements_to_remove.push(element.clone());
            }
        }

        // Remove elements in reverse order (from highest index to lowest)
        elements_to_remove.sort_by_key(|el| std::cmp::Reverse(el.index()));
        for element in elements_to_remove {
            let idx = element.index();
            parent.splice_children(idx..idx + 1, vec![]);
        }

        Ok(comment_count)
    }

    /// Modify the first preceding comment for this MakefileItem
    ///
    /// Returns `true` if a comment was found and modified, `false` if no comment exists.
    /// The comment text should not include the leading '#' character.
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
        let parent = self.get_parent_or_error("modify comment for", "modify_comment")?;

        // Find the first preceding comment (closest to the item)
        let collected_elements = self.collect_preceding_comment_elements();
        let comment_element = collected_elements.iter().find(|element| {
            if let rowan::NodeOrToken::Token(token) = element {
                token.kind() == COMMENT
            } else {
                false
            }
        });

        if let Some(element) = comment_element {
            let idx = element.index();
            let (new_comment_token, _) =
                Self::parse_comment_tokens(new_comment_text, &line_ending(self.syntax()));
            parent.splice_children(
                idx..idx + 1,
                vec![rowan::NodeOrToken::Token(new_comment_token)],
            );
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Insert a new MakefileItem before this item
    ///
    /// This inserts the new item immediately before the current item in the makefile.
    /// The new item is inserted at the same level as the current item.
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
        let current_index = self.syntax().index();
        let new_node = with_trailing_newline(new_item.syntax(), &line_ending(&parent));

        // Insert the new item before the current item
        parent.splice_children(current_index..current_index, vec![new_node.into()]);

        Ok(())
    }

    /// Insert a new MakefileItem after this item
    ///
    /// This inserts the new item immediately after the current item in the makefile.
    /// The new item is inserted at the same level as the current item.
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
        let eol = line_ending(&parent);
        let new_node = with_trailing_newline(new_item.syntax(), &eol);
        let index = terminate_line_before(&parent, self.syntax().index() + 1, &eol);

        // Insert the new item after the current item
        parent.splice_children(index..index, vec![new_node.into()]);

        Ok(())
    }
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
    pub fn conditionals(&self) -> impl Iterator<Item = Conditional> + '_ {
        self.items().filter_map(|item| match item {
            MakefileItem::Conditional(c) => Some(c),
            _ => None,
        })
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
    /// Walks the entire syntax tree to find all `$(VAR)` and `${VAR}` references
    /// in variable values, prerequisites, and targets.
    ///
    /// Note: Variable references inside recipes and `define` bodies are not
    /// included, since those are stored as raw text in the syntax tree. Use
    /// [`Recipe::variable_references`](crate::Recipe::variable_references) and
    /// [`VariableDefinition::define_variable_references`](crate::VariableDefinition::define_variable_references)
    /// for them.
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
                rowan::GreenToken::new(NEWLINE.into(), &eol).into(),
            ],
        ));
        let pos = terminate_line_before(
            self.syntax(),
            self.syntax().children_with_tokens().count(),
            &eol,
        );

        if needs_blank_line_at_end(self.syntax()) {
            // Create a BLANK_LINE node
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), &eol);
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());

            self.syntax()
                .splice_children(pos..pos, vec![blank_line.into(), syntax.into()]);
        } else {
            self.syntax().splice_children(pos..pos, vec![syntax.into()]);
        }

        // Use children().count() - 1 to get the last added child node
        // (not children_with_tokens().count() which includes tokens)
        Ok(Rule::cast(self.syntax().children().last().unwrap()).unwrap())
    }

    /// Add a new conditional to the makefile
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

        let eol = line_ending(self.syntax());
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(CONDITIONAL.into());

        // Build CONDITIONAL_IF
        builder.start_node(CONDITIONAL_IF.into());
        builder.token(IDENTIFIER.into(), conditional_type);
        builder.token(WHITESPACE.into(), " ");

        // Wrap condition in EXPR node
        builder.start_node(EXPR.into());
        builder.token(IDENTIFIER.into(), condition);
        builder.finish_node();

        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();

        for line in if_body.lines() {
            if !line.is_empty() {
                builder.token(IDENTIFIER.into(), line);
            }
            builder.token(NEWLINE.into(), &eol);
        }

        // Add else clause if provided
        if let Some(else_content) = else_body {
            builder.start_node(CONDITIONAL_ELSE.into());
            builder.token(IDENTIFIER.into(), else_keyword);
            builder.token(NEWLINE.into(), &eol);
            builder.finish_node();

            for line in else_content.lines() {
                if !line.is_empty() {
                    builder.token(IDENTIFIER.into(), line);
                }
                builder.token(NEWLINE.into(), &eol);
            }
        }

        // Build CONDITIONAL_ENDIF
        builder.start_node(CONDITIONAL_ENDIF.into());
        builder.token(IDENTIFIER.into(), endif_keyword);
        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();

        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        let pos = terminate_line_before(
            self.syntax(),
            self.syntax().children_with_tokens().count(),
            &eol,
        );

        // Add a blank line before the new conditional if there are existing elements
        let needs_blank_line = self
            .syntax()
            .children()
            .any(|c| c.kind() == RULE || c.kind() == VARIABLE || c.kind() == CONDITIONAL);

        if needs_blank_line {
            // Create a BLANK_LINE node
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), &eol);
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());

            self.syntax()
                .splice_children(pos..pos, vec![blank_line.into(), syntax.into()]);
        } else {
            self.syntax().splice_children(pos..pos, vec![syntax.into()]);
        }

        // Return the newly added conditional
        Ok(Conditional::cast(self.syntax().children().last().unwrap()).unwrap())
    }

    /// Add a new conditional to the makefile with typed items
    ///
    /// This is a more type-safe alternative to `add_conditional` that accepts iterators of
    /// `MakefileItem` instead of raw strings.
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

        let eol = line_ending(self.syntax());
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(CONDITIONAL.into());

        // Build CONDITIONAL_IF
        builder.start_node(CONDITIONAL_IF.into());
        builder.token(IDENTIFIER.into(), conditional_type);
        builder.token(WHITESPACE.into(), " ");

        // Wrap condition in EXPR node
        builder.start_node(EXPR.into());
        builder.token(IDENTIFIER.into(), condition);
        builder.finish_node();

        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();

        // Add if branch items
        for item in if_items {
            // Clone the item's syntax tree into our builder
            let item_text = item.syntax().to_string();
            // Parse it again to get green nodes
            builder.token(IDENTIFIER.into(), item_text.trim());
            builder.token(NEWLINE.into(), &eol);
        }

        // Add else clause if provided
        if let Some(else_iter) = else_items {
            builder.start_node(CONDITIONAL_ELSE.into());
            builder.token(IDENTIFIER.into(), else_keyword);
            builder.token(NEWLINE.into(), &eol);
            builder.finish_node();

            // Add else branch items
            for item in else_iter {
                let item_text = item.syntax().to_string();
                builder.token(IDENTIFIER.into(), item_text.trim());
                builder.token(NEWLINE.into(), &eol);
            }
        }

        // Build CONDITIONAL_ENDIF
        builder.start_node(CONDITIONAL_ENDIF.into());
        builder.token(IDENTIFIER.into(), endif_keyword);
        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();

        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        let pos = terminate_line_before(
            self.syntax(),
            self.syntax().children_with_tokens().count(),
            &eol,
        );

        // Add a blank line before the new conditional if there are existing elements
        let needs_blank_line = self
            .syntax()
            .children()
            .any(|c| c.kind() == RULE || c.kind() == VARIABLE || c.kind() == CONDITIONAL);

        if needs_blank_line {
            // Create a BLANK_LINE node
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), &eol);
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());

            self.syntax()
                .splice_children(pos..pos, vec![blank_line.into(), syntax.into()]);
        } else {
            self.syntax().splice_children(pos..pos, vec![syntax.into()]);
        }

        // Return the newly added conditional
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

        let new_node = with_trailing_newline(new_rule.syntax(), &line_ending(self.syntax()));

        target_node
            .parent()
            .unwrap()
            .splice_children(target_index..target_index + 1, vec![new_node.into()]);
        Ok(())
    }

    /// Remove rule at given index
    ///
    /// `index` is a position in [`Makefile::rules`], so it can refer to a
    /// rule inside a conditional or loop.
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
            Some(rule) => (rule.parent().unwrap(), rule.index()),
            None => (
                self.syntax().clone(),
                self.syntax().children_with_tokens().count(),
            ),
        };

        // Build the nodes to insert
        let eol = line_ending(self.syntax());
        let new_node = with_trailing_newline(new_rule.syntax(), &eol);
        let mut nodes_to_insert = Vec::new();

        // Determine if we need to add blank lines to maintain formatting consistency
        if index == 0 && !rules.is_empty() {
            // Inserting before the first rule - check if first rule has a blank line before it
            // If so, we should add one after our new rule instead
            // For now, just add the rule without a blank line before it
            nodes_to_insert.push(new_node.clone().into());

            // Add a blank line after the new rule
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), &eol);
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());
            nodes_to_insert.push(blank_line.into());
        } else if index < rules.len() {
            // Inserting in the middle (before an existing rule)
            // The syntax tree structure is: ... [maybe BLANK_LINE] RULE(target) ...
            // We're inserting right before RULE(target)

            // If there's a BLANK_LINE immediately before the target rule,
            // it will stay there and separate the previous rule from our new rule.
            // We don't need to add a BLANK_LINE before our new rule in that case.

            // But we DO need to add a BLANK_LINE after our new rule to separate it
            // from the target rule (which we're inserting before).

            // Check if there's a blank line immediately before target_index
            let has_blank_before = if target_index > 0 {
                parent
                    .children_with_tokens()
                    .nth(target_index - 1)
                    .and_then(|n| n.as_node().map(|node| node.kind() == BLANK_LINE))
                    .unwrap_or(false)
            } else {
                false
            };

            // No blank line directly after a conditional or loop header
            let at_block_start = rules[index].prev_sibling().is_some_and(|n| {
                matches!(n.kind(), CONDITIONAL_IF | CONDITIONAL_ELSE | FOR_HEADER)
            });

            // Only add a blank before if there isn't one already and we're not at the start
            if !has_blank_before && index > 0 && !at_block_start {
                let mut bl_builder = GreenNodeBuilder::new();
                bl_builder.start_node(BLANK_LINE.into());
                bl_builder.token(NEWLINE.into(), &eol);
                bl_builder.finish_node();
                let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());
                nodes_to_insert.push(blank_line.into());
            }

            // Add the new rule
            nodes_to_insert.push(new_node.clone().into());

            // Always add a blank line after the new rule to separate it from the next rule
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), &eol);
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());
            nodes_to_insert.push(blank_line.into());
        } else {
            // Inserting at the end when there are existing rules
            // Add a blank line before the new rule
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), &eol);
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());
            nodes_to_insert.push(blank_line.into());

            // Add the new rule
            nodes_to_insert.push(new_node.clone().into());
        }

        // Insert all nodes at the target index
        let target_index = terminate_line_before(&parent, target_index, &eol);
        parent.splice_children(target_index..target_index, nodes_to_insert);
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
    /// The position is relative to other top-level items (rules, variables, includes, conditionals).
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
        let items: Vec<_> = self.syntax().children().collect();

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

        let target_index = if index == items.len() {
            // Insert at the end
            self.syntax().children_with_tokens().count()
        } else {
            // Insert before the item at the given index
            items[index].index()
        };

        // Insert the include node
        let target_index = terminate_line_before(self.syntax(), target_index, &eol);
        self.syntax()
            .splice_children(target_index..target_index, vec![syntax.into()]);

        // Find and return the newly added include
        // It should be at the child index we inserted at
        Ok(Include::cast(self.syntax().children().nth(index).unwrap()).unwrap())
    }

    /// Insert an include directive after a specific MakefileItem
    ///
    /// This is useful when you want to insert an include relative to another item in the makefile.
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
        let eol = line_ending(self.syntax());
        let syntax = Include::new(path, &eol)?.syntax().clone();

        // Find the position of the item to insert after
        let after_syntax = after.syntax();
        let target_index = terminate_line_before(self.syntax(), after_syntax.index() + 1, &eol);

        // Insert the include node after the target item
        self.syntax()
            .splice_children(target_index..target_index, vec![syntax.into()]);

        // Find and return the newly added include
        // It should be the child immediately after the 'after' item
        let after_child_index = self
            .syntax()
            .children()
            .position(|child| child.text_range() == after_syntax.text_range())
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

        Ok(Include::cast(self.syntax().children().nth(after_child_index + 1).unwrap()).unwrap())
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
        assert_eq!(makefile.to_string(), "VAR0 = x\nVAR = value\n");
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
        // The new variable should be inserted before Comment 2 (which precedes VAR2)
        // This is correct because insert_before inserts before the item and its preceding comments
        assert_eq!(
            result,
            "# Comment 1\nVAR1 = first\n# Comment 2\nVAR_NEW = inserted\nVAR2 = second\n"
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
        assert_eq!(makefile.to_string(), "a:\n\tx\n\n\nnew:\n\tz\n\nb:\n\ty\n");
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
