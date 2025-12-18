use crate::lossless::{
    parse, Conditional, Error, ErrorInfo, Include, Makefile, ParseError, Rule, SyntaxNode,
    VariableDefinition,
};
use crate::pattern::matches_pattern;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::GreenNodeBuilder;

/// Represents different types of items that can appear in a Makefile
#[derive(Clone)]
pub enum MakefileItem {
    /// A rule definition (e.g., "target: prerequisites")
    Rule(Rule),
    /// A variable definition (e.g., "VAR = value")
    Variable(VariableDefinition),
    /// An include directive (e.g., "include foo.mk")
    Include(Include),
    /// A conditional block (e.g., "ifdef DEBUG ... endif")
    Conditional(Conditional),
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
        } else {
            Conditional::cast(node).map(MakefileItem::Conditional)
        }
    }

    /// Get the underlying syntax node
    pub(crate) fn syntax(&self) -> &SyntaxNode {
        match self {
            MakefileItem::Rule(r) => r.syntax(),
            MakefileItem::Variable(v) => v.syntax(),
            MakefileItem::Include(i) => i.syntax(),
            MakefileItem::Conditional(c) => c.syntax(),
        }
    }

    /// Helper to get parent node or return an appropriate error
    fn get_parent_or_error(&self, action: &str, method: &str) -> Result<SyntaxNode, Error> {
        self.syntax().parent().ok_or_else(|| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
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
    ) -> (
        rowan::SyntaxToken<crate::lossless::Lang>,
        Option<rowan::SyntaxToken<crate::lossless::Lang>>,
    ) {
        let comment_line = format!("# {}\n", comment_text);
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

        // Replace the current node with the new item's syntax
        parent.splice_children(
            current_index..current_index + 1,
            vec![new_item.syntax().clone().into()],
        );

        // Update self to point to the new item
        *self = new_item;

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
        let (comment_token, newline_token) = Self::parse_comment_tokens(comment_text);

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
            let (new_comment_token, _) = Self::parse_comment_tokens(new_comment_text);
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

        // Insert the new item before the current item
        parent.splice_children(
            current_index..current_index,
            vec![new_item.syntax().clone().into()],
        );

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
        let current_index = self.syntax().index();

        // Insert the new item after the current item
        parent.splice_children(
            current_index + 1..current_index + 1,
            vec![new_item.syntax().clone().into()],
        );

        Ok(())
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
    pub fn parse(text: &str) -> crate::Parse<Makefile> {
        crate::Parse::<Makefile>::parse_makefile(text)
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

    /// Retrieve the rules in the makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "rule: dependency\n\tcommand\n".parse().unwrap();
    /// assert_eq!(makefile.rules().count(), 1);
    /// ```
    pub fn rules(&self) -> impl Iterator<Item = Rule> + '_ {
        self.syntax().children().filter_map(Rule::cast)
    }

    /// Get all rules that have a specific target
    pub fn rules_by_target<'a>(&'a self, target: &'a str) -> impl Iterator<Item = Rule> + 'a {
        self.rules()
            .filter(move |rule| rule.targets().any(|t| t == target))
    }

    /// Get all variable definitions in the makefile
    pub fn variable_definitions(&self) -> impl Iterator<Item = VariableDefinition> {
        self.syntax()
            .children()
            .filter_map(VariableDefinition::cast)
    }

    /// Get all conditionals in the makefile
    pub fn conditionals(&self) -> impl Iterator<Item = Conditional> + '_ {
        self.syntax().children().filter_map(Conditional::cast)
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

    /// Add a new rule to the makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile = Makefile::new();
    /// makefile.add_rule("rule");
    /// assert_eq!(makefile.to_string(), "rule:\n");
    /// ```
    pub fn add_rule(&mut self, target: &str) -> Rule {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RULE.into());
        builder.token(IDENTIFIER.into(), target);
        builder.token(OPERATOR.into(), ":");
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        let pos = self.syntax().children_with_tokens().count();

        // Add a blank line before the new rule if there are existing rules
        // This maintains standard makefile formatting
        let needs_blank_line = self.syntax().children().any(|c| c.kind() == RULE);

        if needs_blank_line {
            // Create a BLANK_LINE node
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), "\n");
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());

            self.syntax()
                .splice_children(pos..pos, vec![blank_line.into(), syntax.into()]);
        } else {
            self.syntax().splice_children(pos..pos, vec![syntax.into()]);
        }

        // Use children().count() - 1 to get the last added child node
        // (not children_with_tokens().count() which includes tokens)
        Rule::cast(self.syntax().children().last().unwrap()).unwrap()
    }

    /// Add a new conditional to the makefile
    ///
    /// # Arguments
    /// * `conditional_type` - The type of conditional: "ifdef", "ifndef", "ifeq", or "ifneq"
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
        if !["ifdef", "ifndef", "ifeq", "ifneq"].contains(&conditional_type) {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: format!(
                        "Invalid conditional type: {}. Must be one of: ifdef, ifndef, ifeq, ifneq",
                        conditional_type
                    ),
                    line: 1,
                    context: "add_conditional".to_string(),
                }],
            }));
        }

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

        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        // Add if body content
        if !if_body.is_empty() {
            for line in if_body.lines() {
                if !line.is_empty() {
                    builder.token(IDENTIFIER.into(), line);
                }
                builder.token(NEWLINE.into(), "\n");
            }
            // Add final newline if if_body doesn't end with one
            if !if_body.ends_with('\n') && !if_body.is_empty() {
                builder.token(NEWLINE.into(), "\n");
            }
        }

        // Add else clause if provided
        if let Some(else_content) = else_body {
            builder.start_node(CONDITIONAL_ELSE.into());
            builder.token(IDENTIFIER.into(), "else");
            builder.token(NEWLINE.into(), "\n");
            builder.finish_node();

            // Add else body content
            if !else_content.is_empty() {
                for line in else_content.lines() {
                    if !line.is_empty() {
                        builder.token(IDENTIFIER.into(), line);
                    }
                    builder.token(NEWLINE.into(), "\n");
                }
                // Add final newline if else_content doesn't end with one
                if !else_content.ends_with('\n') && !else_content.is_empty() {
                    builder.token(NEWLINE.into(), "\n");
                }
            }
        }

        // Build CONDITIONAL_ENDIF
        builder.start_node(CONDITIONAL_ENDIF.into());
        builder.token(IDENTIFIER.into(), "endif");
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        let pos = self.syntax().children_with_tokens().count();

        // Add a blank line before the new conditional if there are existing elements
        let needs_blank_line = self
            .syntax()
            .children()
            .any(|c| c.kind() == RULE || c.kind() == VARIABLE || c.kind() == CONDITIONAL);

        if needs_blank_line {
            // Create a BLANK_LINE node
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), "\n");
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
    /// * `conditional_type` - The type of conditional: "ifdef", "ifndef", "ifeq", or "ifneq"
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
        if !["ifdef", "ifndef", "ifeq", "ifneq"].contains(&conditional_type) {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: format!(
                        "Invalid conditional type: {}. Must be one of: ifdef, ifndef, ifeq, ifneq",
                        conditional_type
                    ),
                    line: 1,
                    context: "add_conditional_with_items".to_string(),
                }],
            }));
        }

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

        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        // Add if branch items
        for item in if_items {
            // Clone the item's syntax tree into our builder
            let item_text = item.syntax().to_string();
            // Parse it again to get green nodes
            builder.token(IDENTIFIER.into(), item_text.trim());
            builder.token(NEWLINE.into(), "\n");
        }

        // Add else clause if provided
        if let Some(else_iter) = else_items {
            builder.start_node(CONDITIONAL_ELSE.into());
            builder.token(IDENTIFIER.into(), "else");
            builder.token(NEWLINE.into(), "\n");
            builder.finish_node();

            // Add else branch items
            for item in else_iter {
                let item_text = item.syntax().to_string();
                builder.token(IDENTIFIER.into(), item_text.trim());
                builder.token(NEWLINE.into(), "\n");
            }
        }

        // Build CONDITIONAL_ENDIF
        builder.start_node(CONDITIONAL_ENDIF.into());
        builder.token(IDENTIFIER.into(), "endif");
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        let pos = self.syntax().children_with_tokens().count();

        // Add a blank line before the new conditional if there are existing elements
        let needs_blank_line = self
            .syntax()
            .children()
            .any(|c| c.kind() == RULE || c.kind() == VARIABLE || c.kind() == CONDITIONAL);

        if needs_blank_line {
            // Create a BLANK_LINE node
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), "\n");
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
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
    /// let new_rule: makefile_lossless::Rule = "new_rule:\n\tnew_command\n".parse().unwrap();
    /// makefile.replace_rule(0, new_rule).unwrap();
    /// assert!(makefile.rules().any(|r| r.targets().any(|t| t == "new_rule")));
    /// ```
    pub fn replace_rule(&mut self, index: usize, new_rule: Rule) -> Result<(), Error> {
        let rules: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| n.kind() == RULE)
            .collect();

        if rules.is_empty() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot replace rule in empty makefile".to_string(),
                    line: 1,
                    context: "replace_rule".to_string(),
                }],
            }));
        }

        if index >= rules.len() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
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

        // Replace the rule at the target index
        self.syntax().splice_children(
            target_index..target_index + 1,
            vec![new_rule.syntax().clone().into()],
        );
        Ok(())
    }

    /// Remove rule at given index
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
        let rules: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| n.kind() == RULE)
            .collect();

        if rules.is_empty() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot remove rule from empty makefile".to_string(),
                    line: 1,
                    context: "remove_rule".to_string(),
                }],
            }));
        }

        if index >= rules.len() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
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

        // Remove the rule at the target index
        self.syntax()
            .splice_children(target_index..target_index + 1, vec![]);
        Ok(Rule::cast(target_node).unwrap())
    }

    /// Insert rule at given position
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
        let rules: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| n.kind() == RULE)
            .collect();

        if index > rules.len() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: format!("Rule index {} out of bounds (max {})", index, rules.len()),
                    line: 1,
                    context: "insert_rule".to_string(),
                }],
            }));
        }

        let target_index = if index == rules.len() {
            // Insert at the end
            self.syntax().children_with_tokens().count()
        } else {
            // Insert before the rule at the given index
            rules[index].index()
        };

        // Build the nodes to insert
        let mut nodes_to_insert = Vec::new();

        // Determine if we need to add blank lines to maintain formatting consistency
        if index == 0 && !rules.is_empty() {
            // Inserting before the first rule - check if first rule has a blank line before it
            // If so, we should add one after our new rule instead
            // For now, just add the rule without a blank line before it
            nodes_to_insert.push(new_rule.syntax().clone().into());

            // Add a blank line after the new rule
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), "\n");
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
                self.syntax()
                    .children_with_tokens()
                    .nth(target_index - 1)
                    .and_then(|n| n.as_node().map(|node| node.kind() == BLANK_LINE))
                    .unwrap_or(false)
            } else {
                false
            };

            // Only add a blank before if there isn't one already and we're not at the start
            if !has_blank_before && index > 0 {
                let mut bl_builder = GreenNodeBuilder::new();
                bl_builder.start_node(BLANK_LINE.into());
                bl_builder.token(NEWLINE.into(), "\n");
                bl_builder.finish_node();
                let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());
                nodes_to_insert.push(blank_line.into());
            }

            // Add the new rule
            nodes_to_insert.push(new_rule.syntax().clone().into());

            // Always add a blank line after the new rule to separate it from the next rule
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), "\n");
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());
            nodes_to_insert.push(blank_line.into());
        } else {
            // Inserting at the end when there are existing rules
            // Add a blank line before the new rule
            let mut bl_builder = GreenNodeBuilder::new();
            bl_builder.start_node(BLANK_LINE.into());
            bl_builder.token(NEWLINE.into(), "\n");
            bl_builder.finish_node();
            let blank_line = SyntaxNode::new_root_mut(bl_builder.finish());
            nodes_to_insert.push(blank_line.into());

            // Add the new rule
            nodes_to_insert.push(new_rule.syntax().clone().into());
        }

        // Insert all nodes at the target index
        self.syntax()
            .splice_children(target_index..target_index, nodes_to_insert);
        Ok(())
    }

    /// Get all include directives in the makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include config.mk\n-include .env\n".parse().unwrap();
    /// let includes = makefile.includes().collect::<Vec<_>>();
    /// assert_eq!(includes.len(), 2);
    /// ```
    pub fn includes(&self) -> impl Iterator<Item = Include> {
        self.syntax().children().filter_map(Include::cast)
    }

    /// Get all included file paths
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include config.mk\n-include .env\n".parse().unwrap();
    /// let paths = makefile.included_files().collect::<Vec<_>>();
    /// assert_eq!(paths, vec!["config.mk", ".env"]);
    /// ```
    pub fn included_files(&self) -> impl Iterator<Item = String> + '_ {
        // We need to collect all Include nodes from anywhere in the syntax tree,
        // not just direct children of the root, to handle includes in conditionals
        fn collect_includes(node: &SyntaxNode) -> Vec<Include> {
            let mut includes = Vec::new();

            // First check if this node itself is an Include
            if let Some(include) = Include::cast(node.clone()) {
                includes.push(include);
            }

            // Then recurse into all children
            for child in node.children() {
                includes.extend(collect_includes(&child));
            }

            includes
        }

        // Start collection from the root node
        let includes = collect_includes(self.syntax());

        // Convert to an iterator of paths
        includes.into_iter().map(|include| {
            include
                .syntax()
                .children()
                .find(|node| node.kind() == EXPR)
                .map(|expr| expr.text().to_string().trim().to_string())
                .unwrap_or_default()
        })
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
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile = Makefile::new();
    /// makefile.add_include("config.mk");
    /// assert_eq!(makefile.included_files().collect::<Vec<_>>(), vec!["config.mk"]);
    /// ```
    pub fn add_include(&mut self, path: &str) -> Include {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(INCLUDE.into());
        builder.token(IDENTIFIER.into(), "include");
        builder.token(WHITESPACE.into(), " ");

        // Wrap path in EXPR node
        builder.start_node(EXPR.into());
        builder.token(IDENTIFIER.into(), path);
        builder.finish_node();

        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        // Insert at the beginning (position 0)
        self.syntax().splice_children(0..0, vec![syntax.into()]);

        // Return the newly added include (first child)
        Include::cast(self.syntax().children().next().unwrap()).unwrap()
    }

    /// Insert an include directive at a specific position
    ///
    /// The position is relative to other top-level items (rules, variables, includes, conditionals).
    ///
    /// # Arguments
    /// * `index` - The position to insert at (0 = beginning, items().count() = end)
    /// * `path` - The file path to include (e.g., "config.mk")
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
                    message: format!("Index {} out of bounds (max {})", index, items.len()),
                    line: 1,
                    context: "insert_include".to_string(),
                }],
            }));
        }

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(INCLUDE.into());
        builder.token(IDENTIFIER.into(), "include");
        builder.token(WHITESPACE.into(), " ");

        // Wrap path in EXPR node
        builder.start_node(EXPR.into());
        builder.token(IDENTIFIER.into(), path);
        builder.finish_node();

        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        let target_index = if index == items.len() {
            // Insert at the end
            self.syntax().children_with_tokens().count()
        } else {
            // Insert before the item at the given index
            items[index].index()
        };

        // Insert the include node
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
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(INCLUDE.into());
        builder.token(IDENTIFIER.into(), "include");
        builder.token(WHITESPACE.into(), " ");

        // Wrap path in EXPR node
        builder.start_node(EXPR.into());
        builder.token(IDENTIFIER.into(), path);
        builder.finish_node();

        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        // Find the position of the item to insert after
        let after_syntax = after.syntax();
        let target_index = after_syntax.index() + 1;

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
}
