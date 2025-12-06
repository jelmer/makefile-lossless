use crate::lossless::{
    build_prerequisites_node, build_targets_node, remove_with_preceding_comments,
    trim_trailing_newlines, Conditional, Error, ErrorInfo, Makefile, MakefileItem, ParseError,
    Rule, SyntaxElement, SyntaxNode,
};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::GreenNodeBuilder;

/// Represents different types of items that can appear in a Rule's body
#[derive(Clone)]
pub enum RuleItem {
    /// A recipe line (command to execute)
    Recipe(String),
    /// A conditional block within the rule
    Conditional(Conditional),
}

impl std::fmt::Debug for RuleItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuleItem::Recipe(text) => f.debug_tuple("Recipe").field(text).finish(),
            RuleItem::Conditional(_) => f
                .debug_tuple("Conditional")
                .field(&"<Conditional>")
                .finish(),
        }
    }
}

impl RuleItem {
    /// Try to cast a syntax node to a RuleItem
    pub(crate) fn cast(node: SyntaxNode) -> Option<Self> {
        match node.kind() {
            RECIPE => {
                // Extract the recipe text from the RECIPE node
                let text = node.children_with_tokens().find_map(|it| {
                    if let Some(token) = it.as_token() {
                        if token.kind() == TEXT {
                            return Some(token.text().to_string());
                        }
                    }
                    None
                })?;
                Some(RuleItem::Recipe(text))
            }
            CONDITIONAL => Conditional::cast(node).map(RuleItem::Conditional),
            _ => None,
        }
    }
}

impl Rule {
    /// Parse rule text, returning a Parse result
    pub fn parse(text: &str) -> crate::Parse<Rule> {
        crate::Parse::<Rule>::parse_rule(text)
    }

    /// Create a new rule with the given targets, prerequisites, and recipes
    ///
    /// # Arguments
    /// * `targets` - A slice of target names
    /// * `prerequisites` - A slice of prerequisite names (can be empty)
    /// * `recipes` - A slice of recipe lines (can be empty)
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    ///
    /// let rule = Rule::new(&["all"], &["build", "test"], &["echo Done"]);
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["all"]);
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["build", "test"]);
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo Done"]);
    /// ```
    pub fn new(targets: &[&str], prerequisites: &[&str], recipes: &[&str]) -> Rule {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RULE.into());

        // Build targets
        for (i, target) in targets.iter().enumerate() {
            if i > 0 {
                builder.token(WHITESPACE.into(), " ");
            }
            builder.token(IDENTIFIER.into(), target);
        }

        // Add colon
        builder.token(OPERATOR.into(), ":");

        // Build prerequisites
        if !prerequisites.is_empty() {
            builder.token(WHITESPACE.into(), " ");
            builder.start_node(PREREQUISITES.into());

            for (i, prereq) in prerequisites.iter().enumerate() {
                if i > 0 {
                    builder.token(WHITESPACE.into(), " ");
                }
                builder.start_node(PREREQUISITE.into());
                builder.token(IDENTIFIER.into(), prereq);
                builder.finish_node();
            }

            builder.finish_node();
        }

        // Add newline after rule declaration
        builder.token(NEWLINE.into(), "\n");

        // Build recipes
        for recipe in recipes {
            builder.start_node(RECIPE.into());
            builder.token(INDENT.into(), "\t");
            builder.token(TEXT.into(), recipe);
            builder.token(NEWLINE.into(), "\n");
            builder.finish_node();
        }

        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        Rule::cast(syntax).unwrap()
    }

    /// Get the parent item of this rule, if any
    ///
    /// Returns `Some(MakefileItem)` if this rule has a parent that is a MakefileItem
    /// (e.g., a Conditional), or `None` if the parent is the root Makefile node.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = r#"ifdef DEBUG
    /// all:
    ///     echo "test"
    /// endif
    /// "#.parse().unwrap();
    ///
    /// let cond = makefile.conditionals().next().unwrap();
    /// let rule = cond.if_items().next().unwrap();
    /// // Rule's parent is the conditional
    /// assert!(matches!(rule, makefile_lossless::MakefileItem::Rule(_)));
    /// ```
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }

    // Helper method to collect variable references from tokens
    fn collect_variable_reference(
        &self,
        tokens: &mut std::iter::Peekable<impl Iterator<Item = SyntaxElement>>,
    ) -> Option<String> {
        let mut var_ref = String::new();

        // Check if we're at a $ token
        if let Some(token) = tokens.next() {
            if let Some(t) = token.as_token() {
                if t.kind() == DOLLAR {
                    var_ref.push_str(t.text());

                    // Check if the next token is a (
                    if let Some(next) = tokens.peek() {
                        if let Some(nt) = next.as_token() {
                            if nt.kind() == LPAREN {
                                // Consume the opening parenthesis
                                var_ref.push_str(nt.text());
                                tokens.next();

                                // Track parenthesis nesting level
                                let mut paren_count = 1;

                                // Keep consuming tokens until we find the matching closing parenthesis
                                for next_token in tokens.by_ref() {
                                    if let Some(nt) = next_token.as_token() {
                                        var_ref.push_str(nt.text());

                                        if nt.kind() == LPAREN {
                                            paren_count += 1;
                                        } else if nt.kind() == RPAREN {
                                            paren_count -= 1;
                                            if paren_count == 0 {
                                                break;
                                            }
                                        }
                                    }
                                }

                                return Some(var_ref);
                            }
                        }
                    }

                    // Handle simpler variable references (though this branch may be less common)
                    for next_token in tokens.by_ref() {
                        if let Some(nt) = next_token.as_token() {
                            var_ref.push_str(nt.text());
                            if nt.kind() == RPAREN {
                                break;
                            }
                        }
                    }
                    return Some(var_ref);
                }
            }
        }

        None
    }

    // Helper method to extract targets from a TARGETS node
    fn extract_targets_from_node(node: &SyntaxNode) -> Vec<String> {
        let mut result = Vec::new();
        let mut current_target = String::new();
        let mut in_parens = 0;

        for child in node.children_with_tokens() {
            if let Some(token) = child.as_token() {
                match token.kind() {
                    IDENTIFIER => {
                        current_target.push_str(token.text());
                    }
                    WHITESPACE => {
                        // Only treat whitespace as a delimiter if we're not inside parentheses
                        if in_parens == 0 && !current_target.is_empty() {
                            result.push(current_target.clone());
                            current_target.clear();
                        } else if in_parens > 0 {
                            current_target.push_str(token.text());
                        }
                    }
                    LPAREN => {
                        in_parens += 1;
                        current_target.push_str(token.text());
                    }
                    RPAREN => {
                        in_parens -= 1;
                        current_target.push_str(token.text());
                    }
                    DOLLAR => {
                        current_target.push_str(token.text());
                    }
                    _ => {
                        current_target.push_str(token.text());
                    }
                }
            } else if let Some(child_node) = child.as_node() {
                // Handle nested nodes like ARCHIVE_MEMBERS
                current_target.push_str(&child_node.text().to_string());
            }
        }

        // Push the last target if any
        if !current_target.is_empty() {
            result.push(current_target);
        }

        result
    }

    /// Targets of this rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    ///
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
    /// ```
    pub fn targets(&self) -> impl Iterator<Item = String> + '_ {
        // First check if there's a TARGETS node
        for child in self.syntax().children_with_tokens() {
            if let Some(node) = child.as_node() {
                if node.kind() == TARGETS {
                    // Extract targets from the TARGETS node
                    return Self::extract_targets_from_node(node).into_iter();
                }
            }
            // Stop at the operator
            if let Some(token) = child.as_token() {
                if token.kind() == OPERATOR {
                    break;
                }
            }
        }

        // Fallback to old parsing logic for backward compatibility
        let mut result = Vec::new();
        let mut tokens = self
            .syntax()
            .children_with_tokens()
            .take_while(|it| it.as_token().map(|t| t.kind() != OPERATOR).unwrap_or(true))
            .peekable();

        while let Some(token) = tokens.peek().cloned() {
            if let Some(node) = token.as_node() {
                tokens.next(); // Consume the node
                if node.kind() == EXPR {
                    // Handle when the target is an expression node
                    let mut var_content = String::new();
                    for child in node.children_with_tokens() {
                        if let Some(t) = child.as_token() {
                            var_content.push_str(t.text());
                        }
                    }
                    if !var_content.is_empty() {
                        result.push(var_content);
                    }
                }
            } else if let Some(t) = token.as_token() {
                if t.kind() == DOLLAR {
                    if let Some(var_ref) = self.collect_variable_reference(&mut tokens) {
                        result.push(var_ref);
                    }
                } else if t.kind() == IDENTIFIER {
                    // Check if this identifier is followed by archive members
                    let ident_text = t.text().to_string();
                    tokens.next(); // Consume the identifier

                    // Peek ahead to see if we have archive member syntax
                    if let Some(next) = tokens.peek() {
                        if let Some(next_token) = next.as_token() {
                            if next_token.kind() == LPAREN {
                                // This is an archive member target, collect the whole thing
                                let mut archive_target = ident_text;
                                archive_target.push_str(next_token.text()); // Add '('
                                tokens.next(); // Consume LPAREN

                                // Collect everything until RPAREN
                                while let Some(token) = tokens.peek() {
                                    if let Some(node) = token.as_node() {
                                        if node.kind() == ARCHIVE_MEMBERS {
                                            archive_target.push_str(&node.text().to_string());
                                            tokens.next();
                                        } else {
                                            tokens.next();
                                        }
                                    } else if let Some(t) = token.as_token() {
                                        if t.kind() == RPAREN {
                                            archive_target.push_str(t.text());
                                            tokens.next();
                                            break;
                                        } else {
                                            tokens.next();
                                        }
                                    } else {
                                        break;
                                    }
                                }
                                result.push(archive_target);
                            } else {
                                // Regular identifier
                                result.push(ident_text);
                            }
                        } else {
                            // Regular identifier
                            result.push(ident_text);
                        }
                    } else {
                        // Regular identifier
                        result.push(ident_text);
                    }
                } else {
                    tokens.next(); // Skip other token types
                }
            }
        }
        result.into_iter()
    }

    /// Get the prerequisites in the rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
    /// ```
    pub fn prerequisites(&self) -> impl Iterator<Item = String> + '_ {
        // Find PREREQUISITES node after OPERATOR token
        let mut found_operator = false;
        let mut prerequisites_node = None;

        for element in self.syntax().children_with_tokens() {
            if let Some(token) = element.as_token() {
                if token.kind() == OPERATOR {
                    found_operator = true;
                }
            } else if let Some(node) = element.as_node() {
                if found_operator && node.kind() == PREREQUISITES {
                    prerequisites_node = Some(node.clone());
                    break;
                }
            }
        }

        let result: Vec<String> = if let Some(prereqs) = prerequisites_node {
            // Iterate over PREREQUISITE child nodes
            prereqs
                .children()
                .filter(|child| child.kind() == PREREQUISITE)
                .map(|child| child.text().to_string().trim().to_string())
                .collect()
        } else {
            Vec::new()
        };

        result.into_iter()
    }

    /// Get the commands in the rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);
    /// ```
    pub fn recipes(&self) -> impl Iterator<Item = String> {
        self.syntax()
            .children()
            .filter(|it| it.kind() == RECIPE)
            .flat_map(|it| {
                it.children_with_tokens().filter_map(|it| {
                    it.as_token().and_then(|t| {
                        if t.kind() == TEXT {
                            Some(t.text().to_string())
                        } else {
                            None
                        }
                    })
                })
            })
    }

    /// Get all items (recipe lines and conditionals) in the rule's body
    ///
    /// This method iterates through the rule's body and yields both recipe lines
    /// and any conditionals that appear within the rule.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Rule, RuleItem};
    ///
    /// let rule_text = r#"test:
    /// 	echo "before"
    /// ifeq (,$(filter nocheck,$(DEB_BUILD_OPTIONS)))
    /// 	./run-tests
    /// endif
    /// 	echo "after"
    /// "#;
    /// let rule: Rule = rule_text.parse().unwrap();
    ///
    /// let items: Vec<_> = rule.items().collect();
    /// assert_eq!(items.len(), 3); // recipe, conditional, recipe
    ///
    /// match &items[0] {
    ///     RuleItem::Recipe(r) => assert_eq!(r, "echo \"before\""),
    ///     _ => panic!("Expected recipe"),
    /// }
    ///
    /// match &items[1] {
    ///     RuleItem::Conditional(_) => {},
    ///     _ => panic!("Expected conditional"),
    /// }
    ///
    /// match &items[2] {
    ///     RuleItem::Recipe(r) => assert_eq!(r, "echo \"after\""),
    ///     _ => panic!("Expected recipe"),
    /// }
    /// ```
    pub fn items(&self) -> impl Iterator<Item = RuleItem> + '_ {
        self.syntax()
            .children()
            .filter(|n| n.kind() == RECIPE || n.kind() == CONDITIONAL)
            .filter_map(RuleItem::cast)
    }

    /// Replace the command at index i with a new line
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// rule.replace_command(0, "new command");
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["new command"]);
    /// ```
    pub fn replace_command(&mut self, i: usize, line: &str) -> bool {
        // Collect all RECIPE nodes that contain TEXT tokens (actual commands, not just comments)
        // This matches the behavior of recipes() which only returns recipes with TEXT
        let recipes: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| {
                n.kind() == RECIPE
                    && n.children_with_tokens()
                        .any(|t| t.as_token().map(|t| t.kind() == TEXT).unwrap_or(false))
            })
            .collect();

        if i >= recipes.len() {
            return false;
        }

        // Get the target RECIPE node and its index among all siblings
        let target_node = &recipes[i];
        let target_index = target_node.index();

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), line);
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        self.syntax()
            .splice_children(target_index..target_index + 1, vec![syntax.into()]);

        true
    }

    /// Add a new command to the rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// rule.push_command("command2");
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command", "command2"]);
    /// ```
    pub fn push_command(&mut self, line: &str) {
        // Find the latest RECIPE entry, then append the new line after it.
        let index = self
            .syntax()
            .children_with_tokens()
            .filter(|it| it.kind() == RECIPE)
            .last();

        let index = index.map_or_else(
            || self.syntax().children_with_tokens().count(),
            |it| it.index() + 1,
        );

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), line);
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();
        let syntax = SyntaxNode::new_root_mut(builder.finish());

        self.syntax()
            .splice_children(index..index, vec![syntax.into()]);
    }

    /// Remove command at given index
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "rule:\n\tcommand1\n\tcommand2\n".parse().unwrap();
    /// rule.remove_command(0);
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command2"]);
    /// ```
    pub fn remove_command(&mut self, index: usize) -> bool {
        let recipes: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| n.kind() == RECIPE)
            .collect();

        if index >= recipes.len() {
            return false;
        }

        let target_node = &recipes[index];
        let target_index = target_node.index();

        self.syntax()
            .splice_children(target_index..target_index + 1, vec![]);
        true
    }

    /// Insert command at given index
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "rule:\n\tcommand1\n\tcommand2\n".parse().unwrap();
    /// rule.insert_command(1, "inserted_command");
    /// let recipes: Vec<_> = rule.recipes().collect();
    /// assert_eq!(recipes, vec!["command1", "inserted_command", "command2"]);
    /// ```
    pub fn insert_command(&mut self, index: usize, line: &str) -> bool {
        let recipes: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| n.kind() == RECIPE)
            .collect();

        if index > recipes.len() {
            return false;
        }

        let target_index = if index == recipes.len() {
            // Insert at the end - find position after last recipe
            recipes.last().map(|n| n.index() + 1).unwrap_or_else(|| {
                // No recipes exist, insert after the rule header
                self.syntax().children_with_tokens().count()
            })
        } else {
            // Insert before the recipe at the given index
            recipes[index].index()
        };

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), line);
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();
        let syntax = SyntaxNode::new_root_mut(builder.finish());

        self.syntax()
            .splice_children(target_index..target_index, vec![syntax.into()]);
        true
    }

    /// Get the number of commands/recipes in this rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule:\n\tcommand1\n\tcommand2\n".parse().unwrap();
    /// assert_eq!(rule.recipe_count(), 2);
    /// ```
    pub fn recipe_count(&self) -> usize {
        self.syntax()
            .children()
            .filter(|n| n.kind() == RECIPE)
            .count()
    }

    /// Clear all commands from this rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "rule:\n\tcommand1\n\tcommand2\n".parse().unwrap();
    /// rule.clear_commands();
    /// assert_eq!(rule.recipe_count(), 0);
    /// ```
    pub fn clear_commands(&mut self) {
        let recipes: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| n.kind() == RECIPE)
            .collect();

        if recipes.is_empty() {
            return;
        }

        // Remove all recipes in reverse order to maintain correct indices
        for recipe in recipes.iter().rev() {
            let index = recipe.index();
            self.syntax().splice_children(index..index + 1, vec![]);
        }
    }

    /// Remove a prerequisite from this rule
    ///
    /// Returns `true` if the prerequisite was found and removed, `false` if it wasn't found.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "target: dep1 dep2 dep3\n".parse().unwrap();
    /// assert!(rule.remove_prerequisite("dep2").unwrap());
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dep1", "dep3"]);
    /// assert!(!rule.remove_prerequisite("nonexistent").unwrap());
    /// ```
    pub fn remove_prerequisite(&mut self, target: &str) -> Result<bool, Error> {
        // Find the PREREQUISITES node after the OPERATOR
        let mut found_operator = false;
        let mut prereqs_node = None;

        for child in self.syntax().children_with_tokens() {
            if let Some(token) = child.as_token() {
                if token.kind() == OPERATOR {
                    found_operator = true;
                }
            } else if let Some(node) = child.as_node() {
                if found_operator && node.kind() == PREREQUISITES {
                    prereqs_node = Some(node.clone());
                    break;
                }
            }
        }

        let prereqs_node = match prereqs_node {
            Some(node) => node,
            None => return Ok(false), // No prerequisites
        };

        // Collect current prerequisites
        let current_prereqs: Vec<String> = self.prerequisites().collect();

        // Check if target exists
        if !current_prereqs.iter().any(|p| p == target) {
            return Ok(false);
        }

        // Filter out the target
        let new_prereqs: Vec<String> = current_prereqs
            .into_iter()
            .filter(|p| p != target)
            .collect();

        // Check if the existing PREREQUISITES node starts with whitespace
        let has_leading_whitespace = prereqs_node
            .children_with_tokens()
            .next()
            .map(|e| matches!(e.as_token().map(|t| t.kind()), Some(WHITESPACE)))
            .unwrap_or(false);

        // Rebuild the PREREQUISITES node with the new prerequisites
        let prereqs_index = prereqs_node.index();
        let new_prereqs_node = build_prerequisites_node(&new_prereqs, has_leading_whitespace);

        self.syntax().splice_children(
            prereqs_index..prereqs_index + 1,
            vec![new_prereqs_node.into()],
        );

        Ok(true)
    }

    /// Add a prerequisite to this rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "target: dep1\n".parse().unwrap();
    /// rule.add_prerequisite("dep2").unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dep1", "dep2"]);
    /// ```
    pub fn add_prerequisite(&mut self, target: &str) -> Result<(), Error> {
        let mut current_prereqs: Vec<String> = self.prerequisites().collect();
        current_prereqs.push(target.to_string());
        self.set_prerequisites(current_prereqs.iter().map(|s| s.as_str()).collect())
    }

    /// Set the prerequisites for this rule, replacing any existing ones
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "target: old_dep\n".parse().unwrap();
    /// rule.set_prerequisites(vec!["new_dep1", "new_dep2"]).unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["new_dep1", "new_dep2"]);
    /// ```
    pub fn set_prerequisites(&mut self, prereqs: Vec<&str>) -> Result<(), Error> {
        // Find the PREREQUISITES node after the OPERATOR, or the position to insert it
        let mut prereqs_index = None;
        let mut operator_found = false;

        for child in self.syntax().children_with_tokens() {
            if let Some(token) = child.as_token() {
                if token.kind() == OPERATOR {
                    operator_found = true;
                }
            } else if let Some(node) = child.as_node() {
                if operator_found && node.kind() == PREREQUISITES {
                    prereqs_index = Some((node.index(), true)); // (index, exists)
                    break;
                }
            }
        }

        match prereqs_index {
            Some((idx, true)) => {
                // Check if there's whitespace between OPERATOR and PREREQUISITES
                let has_external_whitespace = self
                    .syntax()
                    .children_with_tokens()
                    .skip_while(|e| !matches!(e.as_token().map(|t| t.kind()), Some(OPERATOR)))
                    .nth(1) // Skip the OPERATOR itself and get next
                    .map(|e| matches!(e.as_token().map(|t| t.kind()), Some(WHITESPACE)))
                    .unwrap_or(false);

                let new_prereqs = build_prerequisites_node(
                    &prereqs.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
                    !has_external_whitespace, // Include leading space only if no external whitespace
                );
                self.syntax()
                    .splice_children(idx..idx + 1, vec![new_prereqs.into()]);
            }
            _ => {
                // Insert new PREREQUISITES (need leading space inside node)
                let new_prereqs = build_prerequisites_node(
                    &prereqs.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
                    true, // Include leading space
                );

                let insert_pos = self
                    .syntax()
                    .children_with_tokens()
                    .position(|t| t.as_token().map(|t| t.kind() == OPERATOR).unwrap_or(false))
                    .map(|p| p + 1)
                    .ok_or_else(|| {
                        Error::Parse(ParseError {
                            errors: vec![ErrorInfo {
                                message: "No operator found in rule".to_string(),
                                line: 1,
                                context: "set_prerequisites".to_string(),
                            }],
                        })
                    })?;

                self.syntax()
                    .splice_children(insert_pos..insert_pos, vec![new_prereqs.into()]);
            }
        }

        Ok(())
    }

    /// Rename a target in this rule
    ///
    /// Returns `Ok(true)` if the target was found and renamed, `Ok(false)` if the target was not found.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "old_target: dependency\n\tcommand".parse().unwrap();
    /// rule.rename_target("old_target", "new_target").unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["new_target"]);
    /// ```
    pub fn rename_target(&mut self, old_name: &str, new_name: &str) -> Result<bool, Error> {
        // Collect current targets
        let current_targets: Vec<String> = self.targets().collect();

        // Check if the target to rename exists
        if !current_targets.iter().any(|t| t == old_name) {
            return Ok(false);
        }

        // Create new target list with the renamed target
        let new_targets: Vec<String> = current_targets
            .into_iter()
            .map(|t| {
                if t == old_name {
                    new_name.to_string()
                } else {
                    t
                }
            })
            .collect();

        // Find the TARGETS node
        let mut targets_index = None;
        for (idx, child) in self.syntax().children_with_tokens().enumerate() {
            if let Some(node) = child.as_node() {
                if node.kind() == TARGETS {
                    targets_index = Some(idx);
                    break;
                }
            }
        }

        let targets_index = targets_index.ok_or_else(|| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "No TARGETS node found in rule".to_string(),
                    line: 1,
                    context: "rename_target".to_string(),
                }],
            })
        })?;

        // Build new targets node
        let new_targets_node = build_targets_node(&new_targets);

        // Replace the TARGETS node
        self.syntax().splice_children(
            targets_index..targets_index + 1,
            vec![new_targets_node.into()],
        );

        Ok(true)
    }

    /// Add a target to this rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "target1: dependency\n\tcommand".parse().unwrap();
    /// rule.add_target("target2").unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["target1", "target2"]);
    /// ```
    pub fn add_target(&mut self, target: &str) -> Result<(), Error> {
        let mut current_targets: Vec<String> = self.targets().collect();
        current_targets.push(target.to_string());
        self.set_targets(current_targets.iter().map(|s| s.as_str()).collect())
    }

    /// Set the targets for this rule, replacing any existing ones
    ///
    /// Returns an error if the targets list is empty (rules must have at least one target).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "old_target: dependency\n\tcommand".parse().unwrap();
    /// rule.set_targets(vec!["new_target1", "new_target2"]).unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["new_target1", "new_target2"]);
    /// ```
    pub fn set_targets(&mut self, targets: Vec<&str>) -> Result<(), Error> {
        // Ensure targets list is not empty
        if targets.is_empty() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot set empty targets list for a rule".to_string(),
                    line: 1,
                    context: "set_targets".to_string(),
                }],
            }));
        }

        // Find the TARGETS node
        let mut targets_index = None;
        for (idx, child) in self.syntax().children_with_tokens().enumerate() {
            if let Some(node) = child.as_node() {
                if node.kind() == TARGETS {
                    targets_index = Some(idx);
                    break;
                }
            }
        }

        let targets_index = targets_index.ok_or_else(|| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "No TARGETS node found in rule".to_string(),
                    line: 1,
                    context: "set_targets".to_string(),
                }],
            })
        })?;

        // Build new targets node
        let new_targets_node =
            build_targets_node(&targets.iter().map(|s| s.to_string()).collect::<Vec<_>>());

        // Replace the TARGETS node
        self.syntax().splice_children(
            targets_index..targets_index + 1,
            vec![new_targets_node.into()],
        );

        Ok(())
    }

    /// Check if this rule has a specific target
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "target1 target2: dependency\n\tcommand".parse().unwrap();
    /// assert!(rule.has_target("target1"));
    /// assert!(rule.has_target("target2"));
    /// assert!(!rule.has_target("target3"));
    /// ```
    pub fn has_target(&self, target: &str) -> bool {
        self.targets().any(|t| t == target)
    }

    /// Remove a target from this rule
    ///
    /// Returns `Ok(true)` if the target was found and removed, `Ok(false)` if the target was not found.
    /// Returns an error if attempting to remove the last target (rules must have at least one target).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "target1 target2: dependency\n\tcommand".parse().unwrap();
    /// rule.remove_target("target1").unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["target2"]);
    /// ```
    pub fn remove_target(&mut self, target_name: &str) -> Result<bool, Error> {
        // Collect current targets
        let current_targets: Vec<String> = self.targets().collect();

        // Check if the target exists
        if !current_targets.iter().any(|t| t == target_name) {
            return Ok(false);
        }

        // Filter out the target to remove
        let new_targets: Vec<String> = current_targets
            .into_iter()
            .filter(|t| t != target_name)
            .collect();

        // If no targets remain, return an error
        if new_targets.is_empty() {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Cannot remove all targets from a rule".to_string(),
                    line: 1,
                    context: "remove_target".to_string(),
                }],
            }));
        }

        // Find the TARGETS node
        let mut targets_index = None;
        for (idx, child) in self.syntax().children_with_tokens().enumerate() {
            if let Some(node) = child.as_node() {
                if node.kind() == TARGETS {
                    targets_index = Some(idx);
                    break;
                }
            }
        }

        let targets_index = targets_index.ok_or_else(|| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "No TARGETS node found in rule".to_string(),
                    line: 1,
                    context: "remove_target".to_string(),
                }],
            })
        })?;

        // Build new targets node
        let new_targets_node = build_targets_node(&new_targets);

        // Replace the TARGETS node
        self.syntax().splice_children(
            targets_index..targets_index + 1,
            vec![new_targets_node.into()],
        );

        Ok(true)
    }

    /// Remove this rule from its parent Makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// rule.remove().unwrap();
    /// assert_eq!(makefile.rules().count(), 1);
    /// ```
    ///
    /// This will also remove any preceding comments and up to 1 empty line before the rule.
    /// When removing the last rule in a makefile, this will also trim any trailing blank lines
    /// from the previous rule to avoid leaving extra whitespace at the end of the file.
    pub fn remove(self) -> Result<(), Error> {
        let parent = self.syntax().parent().ok_or_else(|| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    message: "Rule has no parent".to_string(),
                    line: 1,
                    context: "remove".to_string(),
                }],
            })
        })?;

        // Check if this is the last rule by seeing if there's any next sibling that's a RULE
        let is_last_rule = self
            .syntax()
            .siblings(rowan::Direction::Next)
            .skip(1) // Skip self
            .all(|sibling| sibling.kind() != RULE);

        remove_with_preceding_comments(self.syntax(), &parent);

        // If we removed the last rule, trim trailing newlines from the last remaining RULE
        if is_last_rule {
            // Find the last RULE node in the parent
            if let Some(last_rule_node) = parent
                .children()
                .filter(|child| child.kind() == RULE)
                .last()
            {
                trim_trailing_newlines(&last_rule_node);
            }
        }

        Ok(())
    }
}

impl Default for Makefile {
    fn default() -> Self {
        Self::new()
    }
}
