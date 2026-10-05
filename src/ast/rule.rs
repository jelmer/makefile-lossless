use super::collapse_continuations;
use super::makefile::MakefileItem;
use crate::lossless::{
    node_text, remove_with_preceding_comments, trim_trailing_newlines, Conditional, Error,
    ErrorInfo, Makefile, ParseError, Recipe, Rule, SyntaxElement, SyntaxNode,
};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::GreenNodeBuilder;

// Helper function to build a PREREQUISITES node containing PREREQUISITE nodes,
// optionally followed by trailing whitespace.
fn build_prerequisites_node(
    prereqs: &[String],
    include_leading_space: bool,
    trailing_space: Option<&str>,
) -> SyntaxNode {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(PREREQUISITES.into());

    for (i, prereq) in prereqs.iter().enumerate() {
        // Add space: before first prerequisite if requested, and between all prerequisites
        if (i == 0 && include_leading_space) || i > 0 {
            builder.token(WHITESPACE.into(), " ");
        }

        // Build each PREREQUISITE node
        builder.start_node(PREREQUISITE.into());
        builder.token(IDENTIFIER.into(), prereq);
        builder.finish_node();
    }

    if let Some(space) = trailing_space {
        builder.token(WHITESPACE.into(), space);
    }

    builder.finish_node();
    SyntaxNode::new_root_mut(builder.finish())
}

// Helper function to build targets section (TARGETS node)
fn build_targets_node(targets: &[String]) -> SyntaxNode {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(TARGETS.into());

    for (i, target) in targets.iter().enumerate() {
        if i > 0 {
            builder.token(WHITESPACE.into(), " ");
        }
        builder.token(IDENTIFIER.into(), target);
    }

    builder.finish_node();
    SyntaxNode::new_root_mut(builder.finish())
}

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
    /// let makefile: Makefile = "ifdef DEBUG\nall:\n\techo \"test\"\nendif\n"
    ///     .parse()
    ///     .unwrap();
    ///
    /// let cond = makefile.conditionals().next().unwrap();
    /// let rule = cond.if_items().next().unwrap();
    /// // Rule's parent is the conditional
    /// assert!(matches!(rule, makefile_lossless::MakefileItem::Rule(_)));
    /// ```
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }

    /// Check if this rule has grouped targets (`a b &: prereqs`), meaning
    /// that a single invocation of the recipe updates all of its targets.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "foo.h foo.c &: foo.y\n\tbison --defines=foo.h -o foo.c foo.y\n"
    ///     .parse()
    ///     .unwrap();
    /// assert!(rule.is_grouped());
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["foo.h", "foo.c"]);
    ///
    /// let rule: Rule = "foo.h foo.c: foo.y\n".parse().unwrap();
    /// assert!(!rule.is_grouped());
    /// ```
    pub fn is_grouped(&self) -> bool {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .any(|t| t.kind() == OPERATOR && matches!(t.text(), "&:" | "&::"))
    }

    /// Check if this is a double-colon rule (`target:: prereqs`).
    ///
    /// Double-colon rules allow multiple recipe blocks for the same target,
    /// each executed independently when its prerequisites are newer. This
    /// includes grouped double-colon rules (`a b &:: prereqs`).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "all:: dep1\n\techo first\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// assert!(rule.is_double_colon());
    /// ```
    pub fn is_double_colon(&self) -> bool {
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .any(|t| t.kind() == OPERATOR && matches!(t.text(), "::" | "&::"))
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
                    WHITESPACE | INDENT | BACKSLASH | NEWLINE => {
                        // Whitespace and line continuations (backslash-newline
                        // plus the continued line's indent) delimit targets,
                        // unless we're inside parentheses.
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
                current_target.push_str(&collapse_continuations(child_node));
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
                                            archive_target.push_str(&node_text(node));
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

    /// The PREREQUISITES node following the rule's operator, if any.
    fn prerequisites_node(&self) -> Option<SyntaxNode> {
        self.syntax()
            .children_with_tokens()
            .skip_while(|e| e.kind() != OPERATOR)
            .find_map(|e| e.into_node().filter(|n| n.kind() == PREREQUISITES))
    }

    /// The normal and order-only prerequisites of the rule.
    fn prerequisite_lists(&self) -> (Vec<String>, Vec<String>) {
        let mut normal = Vec::new();
        let mut order_only = Vec::new();
        let Some(node) = self.prerequisites_node() else {
            return (normal, order_only);
        };
        let mut seen_pipe = false;
        for element in node.children_with_tokens() {
            match element {
                rowan::NodeOrToken::Token(t) if t.kind() == OPERATOR && t.text() == "|" => {
                    seen_pipe = true;
                }
                rowan::NodeOrToken::Node(n) if n.kind() == PREREQUISITE => {
                    let text = collapse_continuations(&n).trim().to_string();
                    if seen_pipe {
                        order_only.push(text);
                    } else {
                        normal.push(text);
                    }
                }
                _ => {}
            }
        }
        (normal, order_only)
    }

    /// Get the normal prerequisites in the rule
    ///
    /// Order-only prerequisites (those after a `|`) are not included; see
    /// [`Rule::order_only_prerequisites`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency | dir\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
    /// ```
    pub fn prerequisites(&self) -> impl Iterator<Item = String> + '_ {
        self.prerequisite_lists().0.into_iter()
    }

    /// Get the order-only prerequisites in the rule, i.e. those after the
    /// first `|` in the prerequisite list.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "foo.o: foo.c | build\n\tcc -c foo.c".parse().unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["foo.c"]);
    /// assert_eq!(rule.order_only_prerequisites().collect::<Vec<_>>(), vec!["build"]);
    /// ```
    pub fn order_only_prerequisites(&self) -> impl Iterator<Item = String> + '_ {
        self.prerequisite_lists().1.into_iter()
    }

    /// Get the target pattern of a static pattern rule.
    ///
    /// For a rule like `$(OBJS): %.o: %.c`, this returns `%.o`, while
    /// [`Rule::prerequisites`] returns the prerequisite patterns. Returns
    /// `None` if this is not a static pattern rule.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "$(OBJS): %.o: %.c | build\n\t$(CC) -c $<\n".parse().unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["$(OBJS)"]);
    /// assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["%.c"]);
    /// assert_eq!(rule.order_only_prerequisites().collect::<Vec<_>>(), vec!["build"]);
    ///
    /// let rule: Rule = "foo.o: foo.c\n".parse().unwrap();
    /// assert_eq!(rule.static_pattern(), None);
    /// ```
    pub fn static_pattern(&self) -> Option<String> {
        self.syntax()
            .children()
            .find(|n| n.kind() == TARGET_PATTERN)
            .map(|n| collapse_continuations(&n).trim().to_string())
    }

    /// Get the commands in the rule
    ///
    /// A recipe given on the rule line after a `;` is the first command.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);
    ///
    /// let rule: Rule = "rule: dependency ; first\n\tsecond\n".parse().unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["first", "second"]);
    /// ```
    pub fn recipes(&self) -> impl Iterator<Item = String> {
        self.recipe_nodes().map(|r| r.text())
    }

    /// If this rule is actually a target-specific variable assignment
    /// (`target: VAR [op] value`), return the embedded [`VariableDefinition`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "all: CFLAGS = -O2\n".parse().unwrap();
    /// let var = rule.scoped_assignment().unwrap();
    /// assert_eq!(var.name(), Some("CFLAGS".to_string()));
    /// assert_eq!(var.assignment_operator(), Some("=".to_string()));
    /// ```
    pub fn scoped_assignment(&self) -> Option<crate::lossless::VariableDefinition> {
        self.syntax()
            .children()
            .find(|c| c.kind() == VARIABLE)
            .and_then(crate::lossless::VariableDefinition::cast)
    }

    /// Get recipe nodes with line/column information
    ///
    /// Returns an iterator over `Recipe` AST nodes, which support the `line()`, `column()`,
    /// and `line_col()` methods to get position information.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    ///
    /// let rule_text = "test:\n\techo line1\n\techo line2\n";
    /// let rule: Rule = rule_text.parse().unwrap();
    ///
    /// let recipe_nodes: Vec<_> = rule.recipe_nodes().collect();
    /// assert_eq!(recipe_nodes.len(), 2);
    /// assert_eq!(recipe_nodes[0].text(), "echo line1");
    /// assert_eq!(recipe_nodes[0].line(), 1); // 0-indexed
    /// assert_eq!(recipe_nodes[1].text(), "echo line2");
    /// assert_eq!(recipe_nodes[1].line(), 2);
    /// ```
    pub fn recipe_nodes(&self) -> impl Iterator<Item = Recipe> {
        self.syntax()
            .children()
            .filter(|it| it.kind() == RECIPE)
            .filter_map(Recipe::cast)
    }

    /// Get all items (recipe lines and conditionals) in the rule's body
    ///
    /// This method iterates through the rule's body and yields both recipe lines
    /// and any conditionals that appear within the rule.
    ///
    /// A conditional is part of the rule if a recipe line comes first in one of
    /// its branches. Recipe lines inside it are not returned by [`Rule::recipes`],
    /// and any other items in it (such as variable definitions) are not part of
    /// the rule, though `Makefile::rules()` and `Makefile::variable_definitions()`
    /// do include them.
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
        // Collect all RECIPE nodes (matching the indexing used by recipe_nodes())
        let recipes: Vec<_> = self
            .syntax()
            .children()
            .filter(|n| n.kind() == RECIPE)
            .collect();

        if i >= recipes.len() {
            return false;
        }

        // Get the target RECIPE node and its index among all siblings
        let target_node = &recipes[i];
        let target_index = target_node.index();

        if let Some(mut recipe) = Recipe::cast(target_node.clone()).filter(|r| r.is_inline()) {
            recipe.replace_text(line);
            return true;
        }

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

        if let Some(recipe) = Recipe::cast(recipes[index].clone()) {
            recipe.remove();
        }
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

        if let Some(recipe) = recipes.get(index).cloned().and_then(Recipe::cast) {
            recipe.insert_before(line);
            return true;
        }

        // Insert at the end - find position after last recipe
        let target_index = recipes.last().map(|n| n.index() + 1).unwrap_or_else(|| {
            // No recipes exist, insert after the rule header
            self.syntax().children_with_tokens().count()
        });

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
        for recipe in recipes.into_iter().rev().filter_map(Recipe::cast) {
            recipe.remove();
        }
    }

    /// Remove a prerequisite from this rule
    ///
    /// Returns `true` if the prerequisite was found and removed, `false` if it wasn't found.
    /// Only normal prerequisites are considered; order-only prerequisites are
    /// left alone.
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
        let current_prereqs: Vec<String> = self.prerequisites().collect();
        if !current_prereqs.iter().any(|p| p == target) {
            return Ok(false);
        }
        self.set_prerequisites(
            current_prereqs
                .iter()
                .map(|p| p.as_str())
                .filter(|p| *p != target)
                .collect(),
        )?;
        Ok(true)
    }

    /// Add a prerequisite to this rule
    ///
    /// The prerequisite is added to the end of the normal prerequisites,
    /// before any order-only prerequisites.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "target: dep1 | dir\n".parse().unwrap();
    /// rule.add_prerequisite("dep2").unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dep1", "dep2"]);
    /// assert_eq!(rule.to_string(), "target: dep1 dep2 | dir\n");
    /// ```
    pub fn add_prerequisite(&mut self, target: &str) -> Result<(), Error> {
        let mut current_prereqs: Vec<String> = self.prerequisites().collect();
        current_prereqs.push(target.to_string());
        self.set_prerequisites(current_prereqs.iter().map(|s| s.as_str()).collect())
    }

    /// Set the prerequisites for this rule, replacing any existing ones
    ///
    /// Only the normal prerequisites are replaced; order-only prerequisites
    /// (after a `|`) are kept.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "target: old_dep | dir\n".parse().unwrap();
    /// rule.set_prerequisites(vec!["new_dep1", "new_dep2"]).unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["new_dep1", "new_dep2"]);
    /// assert_eq!(rule.order_only_prerequisites().collect::<Vec<_>>(), vec!["dir"]);
    /// ```
    pub fn set_prerequisites(&mut self, prereqs: Vec<&str>) -> Result<(), Error> {
        let prereqs = prereqs.iter().map(|s| s.to_string()).collect::<Vec<_>>();

        if let Some(node) = self.prerequisites_node() {
            let has_external_whitespace = node
                .prev_sibling_or_token()
                .is_some_and(|e| e.kind() == WHITESPACE);
            let children: Vec<_> = node.children_with_tokens().collect();
            let normal_end = children
                .iter()
                .position(|e| e.kind() == OPERATOR && e.as_token().is_some_and(|t| t.text() == "|"))
                .unwrap_or(children.len());
            // Replace the normal prerequisites, keeping whatever follows them:
            // whitespace, a comment and any order-only prerequisites.
            let last_prereq = children[..normal_end]
                .iter()
                .rposition(|e| e.kind() == PREREQUISITE);
            let mut keep = last_prereq.map_or(0, |i| i + 1);
            let next_kind = match children.get(keep) {
                Some(e) => Some(e.kind()),
                None => node.next_sibling_or_token().map(|e| e.kind()),
            };
            let separator = if prereqs.is_empty() {
                // Avoid doubled whitespace before e.g. a `|`.
                if has_external_whitespace && keep < children.len() && next_kind == Some(WHITESPACE)
                {
                    keep += 1;
                }
                None
            } else if last_prereq.is_none()
                && !matches!(next_kind, None | Some(WHITESPACE | NEWLINE))
            {
                Some(" ")
            } else {
                None
            };
            let fresh = build_prerequisites_node(&prereqs, !has_external_whitespace, separator);
            let old_green = node.green();
            let rest = old_green.children().skip(keep).map(|c| c.to_owned());
            let green = rowan::GreenNode::new(
                PREREQUISITES.into(),
                fresh
                    .green()
                    .children()
                    .map(|c| c.to_owned())
                    .chain(rest)
                    .collect::<Vec<_>>(),
            );
            let index = node.index();
            self.syntax().splice_children(
                index..index + 1,
                vec![SyntaxNode::new_root_mut(green).into()],
            );
            return Ok(());
        }

        // Insert new PREREQUISITES (need leading space inside node)
        let new_prereqs = build_prerequisites_node(&prereqs, true, None);

        let insert_pos = self
            .syntax()
            .children_with_tokens()
            .position(|t| t.as_token().map(|t| t.kind() == OPERATOR).unwrap_or(false))
            .map(|p| p + 1)
            .ok_or_else(|| {
                Error::Parse(ParseError {
                    errors: vec![ErrorInfo {
                        kind: crate::ParseErrorKind::Other,
                        message: "No operator found in rule".to_string(),
                        line: 1,
                        context: "set_prerequisites".to_string(),
                    }],
                })
            })?;

        self.syntax()
            .splice_children(insert_pos..insert_pos, vec![new_prereqs.into()]);

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
                    kind: crate::ParseErrorKind::Other,
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
                    kind: crate::ParseErrorKind::Other,
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
                    kind: crate::ParseErrorKind::Other,
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
                    kind: crate::ParseErrorKind::Other,
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
                    kind: crate::ParseErrorKind::Other,
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
                    kind: crate::ParseErrorKind::Other,
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

#[cfg(test)]
mod tests {
    use crate::{Makefile, Rule};

    #[test]
    fn test_rules_with_pipe_in_shell_continuation() {
        let input = "VAR ?= $(shell cmd | \\\n\t\tsed -e 's/foo/bar/')\n\n%:\n\tdh $@\n";
        let (makefile, _errors) = Makefile::from_str_relaxed(input);
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 1, "Expected 1 rule");
    }

    #[test]
    fn test_roundtrip_with_backslash_in_variable_continuation() {
        let input = "DEB_UPSTREAM_VERSION ?= $(shell dpkg-parsechangelog | \\\n\
                     \t\t\t  sed -rne 's,^Version: ([^-]+).*,\\1,p')\n\
                     \n\
                     %:\n\
                     \tdh $@ --with autoreconf\n\
                     \n\
                     override_dh_strip:\n\
                     \tdh_strip --dbg-package=f2fs-tools-dbg\n";
        let (makefile, errors) = Makefile::from_str_relaxed(input);
        assert!(errors.is_empty(), "Unexpected parse errors: {:?}", errors);

        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 2, "Expected 2 rules, got {}", rules.len());

        let output = makefile.to_string();
        assert_eq!(input, output, "Round-trip failed");
    }

    #[test]
    fn test_targets_multiple() {
        let rule: Rule = "a b c: dep\n\tcmd".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a", "b", "c"]);
    }

    #[test]
    fn test_targets_archive_member_keeps_parens() {
        let rule: Rule = "lib.a(obj.o): dep\n\tcmd".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["lib.a(obj.o)"]);
    }

    #[test]
    fn test_targets_archive_member_keeps_inner_whitespace() {
        // Whitespace inside the parentheses must not split the target: the
        // in_parens depth counter keeps the whole member together.
        let rule: Rule = "lib.a(a.o b.o): dep\n\tcmd".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["lib.a(a.o b.o)"]);
    }

    #[test]
    fn test_targets_variable_reference() {
        let rule: Rule = "$(VAR): dep\n\tcmd".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["$(VAR)"]);
    }

    #[test]
    fn test_is_double_colon_true() {
        let rule: Rule = "all:: dep\n\tcmd".parse().unwrap();
        assert!(rule.is_double_colon());
    }

    #[test]
    fn test_is_double_colon_false() {
        let rule: Rule = "all: dep\n\tcmd".parse().unwrap();
        assert!(!rule.is_double_colon());
    }

    #[test]
    fn test_set_targets_multiple_separated_by_single_space() {
        let mut rule: Rule = "old: dep\n\tcmd\n".parse().unwrap();
        rule.set_targets(vec!["a", "b", "c"]).unwrap();
        assert_eq!(rule.to_string(), "a b c: dep\n\tcmd\n");
    }

    #[test]
    fn test_rule_item_recipe_debug() {
        let rule: Rule = "all:\n\techo hi\n".parse().unwrap();
        let items: Vec<_> = rule.items().collect();
        assert_eq!(format!("{:?}", items[0]), "Recipe(\"echo hi\")");
    }

    #[test]
    fn test_scoped_assignment_export() {
        let rule: Rule = "c: export SHOUT = loud\n".parse().unwrap();
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            Vec::<String>::new()
        );
        let var = rule.scoped_assignment().unwrap();
        assert_eq!(var.name(), Some("SHOUT".to_string()));
        assert_eq!(var.assignment_operator(), Some("=".to_string()));
        assert_eq!(var.raw_value(), Some("loud".to_string()));
        assert!(var.is_export());
        assert!(!var.is_override());
        assert!(!var.is_private());
        assert_eq!(rule.to_string(), "c: export SHOUT = loud\n");
    }

    #[test]
    fn test_scoped_assignment_override() {
        let rule: Rule = "d: override X := 1\n".parse().unwrap();
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            Vec::<String>::new()
        );
        let var = rule.scoped_assignment().unwrap();
        assert_eq!(var.name(), Some("X".to_string()));
        assert_eq!(var.assignment_operator(), Some(":=".to_string()));
        assert_eq!(var.raw_value(), Some("1".to_string()));
        assert!(!var.is_export());
        assert!(var.is_override());
        assert!(!var.is_private());
    }

    #[test]
    fn test_scoped_assignment_private() {
        let rule: Rule = "e: private Y += 2\n".parse().unwrap();
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            Vec::<String>::new()
        );
        let var = rule.scoped_assignment().unwrap();
        assert_eq!(var.name(), Some("Y".to_string()));
        assert_eq!(var.assignment_operator(), Some("+=".to_string()));
        assert_eq!(var.raw_value(), Some("2".to_string()));
        assert!(!var.is_export());
        assert!(!var.is_override());
        assert!(var.is_private());
    }

    #[test]
    fn test_scoped_assignment_combined_modifiers() {
        let rule: Rule = "f: private override export Z ?= 3\n".parse().unwrap();
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            Vec::<String>::new()
        );
        let var = rule.scoped_assignment().unwrap();
        assert_eq!(var.name(), Some("Z".to_string()));
        assert_eq!(var.assignment_operator(), Some("?=".to_string()));
        assert_eq!(var.raw_value(), Some("3".to_string()));
        assert!(var.is_export());
        assert!(var.is_override());
        assert!(var.is_private());
    }

    #[test]
    fn test_scoped_assignment_keyword_as_name() {
        // Without a following name, the keyword is the variable name itself.
        let rule: Rule = "g: private = 1\n".parse().unwrap();
        let var = rule.scoped_assignment().unwrap();
        assert_eq!(var.name(), Some("private".to_string()));
        assert_eq!(var.raw_value(), Some("1".to_string()));
        assert!(!var.is_private());
    }

    #[test]
    fn test_keyword_prerequisites_without_assignment() {
        let rule: Rule = "h: export private\n".parse().unwrap();
        assert!(rule.scoped_assignment().is_none());
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["export".to_string(), "private".to_string()]
        );
    }

    fn prereqs(rule: &Rule) -> (Vec<String>, Vec<String>) {
        (
            rule.prerequisites().collect(),
            rule.order_only_prerequisites().collect(),
        )
    }

    #[test]
    fn test_order_only_prerequisites() {
        let rule: Rule = "foo: a b | c d\n".parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (
                vec!["a".to_string(), "b".to_string()],
                vec!["c".to_string(), "d".to_string()]
            )
        );
        assert_eq!(rule.to_string(), "foo: a b | c d\n");
    }

    #[test]
    fn test_order_only_prerequisites_without_spaces() {
        let rule: Rule = "foo: a|b c\n".parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (
                vec!["a".to_string()],
                vec!["b".to_string(), "c".to_string()]
            )
        );
        assert_eq!(rule.to_string(), "foo: a|b c\n");
    }

    #[test]
    fn test_only_order_only_prerequisites() {
        let rule: Rule = "foo: | dir\n\tcmd\n".parse().unwrap();
        assert_eq!(prereqs(&rule), (vec![], vec!["dir".to_string()]));
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["cmd"]);
    }

    #[test]
    fn test_second_pipe_is_order_only_prerequisite() {
        // Like GNU make, only the first `|` separates the two lists.
        let rule: Rule = "foo: a | b | c\n".parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (
                vec!["a".to_string()],
                vec!["b".to_string(), "|".to_string(), "c".to_string()]
            )
        );
    }

    #[test]
    fn test_order_only_with_variable_reference() {
        let rule: Rule = "foo: $(A) | $(shell echo a|b) $(DIR)\n".parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (
                vec!["$(A)".to_string()],
                vec!["$(shell echo a|b)".to_string(), "$(DIR)".to_string()]
            )
        );
    }

    #[test]
    fn test_no_order_only_prerequisites() {
        let rule: Rule = "foo: a b\n".parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (vec!["a".to_string(), "b".to_string()], vec![])
        );
    }

    #[test]
    fn test_add_prerequisite_keeps_order_only() {
        let mut rule: Rule = "foo: a | c\n".parse().unwrap();
        rule.add_prerequisite("b").unwrap();
        assert_eq!(rule.to_string(), "foo: a b | c\n");
        assert_eq!(
            prereqs(&rule),
            (
                vec!["a".to_string(), "b".to_string()],
                vec!["c".to_string()]
            )
        );
    }

    #[test]
    fn test_add_prerequisite_before_order_only_only() {
        let mut rule: Rule = "foo: | c\n".parse().unwrap();
        rule.add_prerequisite("b").unwrap();
        assert_eq!(rule.to_string(), "foo: b | c\n");
    }

    #[test]
    fn test_add_prerequisite_without_spaces_around_pipe() {
        let mut rule: Rule = "foo: a|c\n".parse().unwrap();
        rule.add_prerequisite("b").unwrap();
        assert_eq!(rule.to_string(), "foo: a b|c\n");
    }

    #[test]
    fn test_remove_prerequisite_keeps_order_only() {
        let mut rule: Rule = "foo: a b | c\n".parse().unwrap();
        assert!(rule.remove_prerequisite("a").unwrap());
        assert_eq!(rule.to_string(), "foo: b | c\n");
        assert!(rule.remove_prerequisite("b").unwrap());
        assert_eq!(rule.to_string(), "foo: | c\n");
        // Order-only prerequisites are not removed.
        assert!(!rule.remove_prerequisite("c").unwrap());
        assert_eq!(rule.to_string(), "foo: | c\n");
    }

    #[test]
    fn test_set_prerequisites_keeps_order_only() {
        let mut rule: Rule = "foo: a b | c\n".parse().unwrap();
        rule.set_prerequisites(vec!["x"]).unwrap();
        assert_eq!(rule.to_string(), "foo: x | c\n");
        rule.set_prerequisites(vec![]).unwrap();
        assert_eq!(rule.to_string(), "foo: | c\n");
    }

    #[test]
    fn test_static_pattern_rule() {
        let rule: Rule = "$(OBJS): %.o: %.c | dir\n\t$(CC) -c $<\n".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["$(OBJS)"]);
        assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
        assert_eq!(
            prereqs(&rule),
            (vec!["%.c".to_string()], vec!["dir".to_string()])
        );
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["$(CC) -c $<"]);
        assert_eq!(rule.to_string(), "$(OBJS): %.o: %.c | dir\n\t$(CC) -c $<\n");
    }

    #[test]
    fn test_static_pattern_rule_without_spaces() {
        let rule: Rule = "a.o b.o:%.o:%.c %.h\n".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a.o", "b.o"]);
        assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
        assert_eq!(
            prereqs(&rule),
            (vec!["%.c".to_string(), "%.h".to_string()], vec![])
        );
        assert_eq!(rule.to_string(), "a.o b.o:%.o:%.c %.h\n");
    }

    #[test]
    fn test_static_pattern_rule_without_prerequisites() {
        let rule: Rule = "a.o: %.o:\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
        assert_eq!(prereqs(&rule), (vec![], vec![]));
    }

    #[test]
    fn test_static_pattern_with_variable_reference() {
        let rule: Rule = "$(OBJS): $(OBJDIR)/%.o: $(SRCS:.x=.y)\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), Some("$(OBJDIR)/%.o".to_string()));
        assert_eq!(prereqs(&rule), (vec!["$(SRCS:.x=.y)".to_string()], vec![]));
    }

    #[test]
    fn test_no_static_pattern() {
        let rule: Rule = "foo: $(X:a=b) ${Y:c=d}\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), None);
        assert_eq!(
            prereqs(&rule),
            (vec!["$(X:a=b)".to_string(), "${Y:c=d}".to_string()], vec![])
        );
    }

    #[test]
    fn test_escaped_colon_is_not_static_pattern() {
        let rule: Rule = "foo: a\\:b\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), None);
        assert_eq!(prereqs(&rule), (vec!["a\\:b".to_string()], vec![]));
    }

    #[test]
    fn test_target_specific_assignment_is_not_static_pattern() {
        let rule: Rule = "foo: X := a:b\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), None);
        assert_eq!(prereqs(&rule), (vec![], vec![]));
        assert_eq!(
            rule.scoped_assignment().unwrap().raw_value(),
            Some("a:b".to_string())
        );
    }

    #[test]
    fn test_set_prerequisites_static_pattern() {
        let mut rule: Rule = "$(OBJS): %.o: %.c\n".parse().unwrap();
        rule.add_prerequisite("%.h").unwrap();
        assert_eq!(rule.to_string(), "$(OBJS): %.o: %.c %.h\n");
        rule.set_prerequisites(vec!["%.cc"]).unwrap();
        assert_eq!(rule.to_string(), "$(OBJS): %.o: %.cc\n");
        assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
    }

    #[test]
    fn test_static_pattern_rule_with_continuation() {
        let rule: Rule = "a.o b.o: \\\n  %.o: %.c\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
        assert_eq!(prereqs(&rule), (vec!["%.c".to_string()], vec![]));
        assert_eq!(rule.to_string(), "a.o b.o: \\\n  %.o: %.c\n");
    }

    #[test]
    fn test_grouped_targets() {
        let rule: Rule = "a b &: c\n\tcmd\n".parse().unwrap();
        assert!(rule.is_grouped());
        assert!(!rule.is_double_colon());
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a", "b"]);
        assert_eq!(prereqs(&rule), (vec!["c".to_string()], vec![]));
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["cmd"]);
        assert_eq!(rule.to_string(), "a b &: c\n\tcmd\n");
    }

    #[test]
    fn test_grouped_targets_without_spaces() {
        let rule: Rule = "a b&:c|d\n".parse().unwrap();
        assert!(rule.is_grouped());
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a", "b"]);
        assert_eq!(
            prereqs(&rule),
            (vec!["c".to_string()], vec!["d".to_string()])
        );
    }

    #[test]
    fn test_grouped_double_colon() {
        let rule: Rule = "a b &:: c\n".parse().unwrap();
        assert!(rule.is_grouped());
        assert!(rule.is_double_colon());
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a", "b"]);
        assert_eq!(prereqs(&rule), (vec!["c".to_string()], vec![]));
    }

    #[test]
    fn test_not_grouped() {
        let rule: Rule = "a b: c\n".parse().unwrap();
        assert!(!rule.is_grouped());
        let rule: Rule = "a b:: c\n".parse().unwrap();
        assert!(!rule.is_grouped());
    }

    #[test]
    fn test_grouped_static_pattern_rule() {
        let rule: Rule = "a.x a.y &: %.x: %.c\n".parse().unwrap();
        assert!(rule.is_grouped());
        assert_eq!(rule.static_pattern(), Some("%.x".to_string()));
        assert_eq!(prereqs(&rule), (vec!["%.c".to_string()], vec![]));
    }

    fn recipes(rule: &Rule) -> Vec<String> {
        rule.recipes().collect()
    }

    #[test]
    fn test_inline_recipe() {
        let rule: Rule = "all: dep ; echo hi\n\techo there\n".parse().unwrap();
        assert_eq!(prereqs(&rule), (vec!["dep".to_string()], vec![]));
        assert_eq!(recipes(&rule), vec!["echo hi", "echo there"]);
        let first = rule.recipe_nodes().next().unwrap();
        assert_eq!(first.indent(), None);
        assert_eq!(first.line(), 0);
        assert_eq!(rule.to_string(), "all: dep ; echo hi\n\techo there\n");
    }

    #[test]
    fn test_inline_recipe_without_spaces() {
        let rule: Rule = "all:dep;@echo hi\n".parse().unwrap();
        assert_eq!(prereqs(&rule), (vec!["dep".to_string()], vec![]));
        assert_eq!(recipes(&rule), vec!["@echo hi"]);
        assert!(rule.recipe_nodes().next().unwrap().is_silent());
        assert_eq!(rule.to_string(), "all:dep;@echo hi\n");
    }

    #[test]
    fn test_inline_recipe_hash_is_recipe_text() {
        // Make passes the rest of the line to the shell, `#` included.
        let rule: Rule = "all: dep ; echo hi # there ; x\n".parse().unwrap();
        assert_eq!(recipes(&rule), vec!["echo hi # there ; x"]);
        let first = rule.recipe_nodes().next().unwrap();
        assert_eq!(first.comment(), None);
        assert_eq!(first.full(), "echo hi # there ; x");
    }

    #[test]
    fn test_inline_recipe_comment_only() {
        // Like a tab-indented `# comment` recipe line.
        let rule: Rule = "all: ; # nothing\n".parse().unwrap();
        assert_eq!(recipes(&rule), vec![""]);
        let first = rule.recipe_nodes().next().unwrap();
        assert_eq!(first.comment(), Some("# nothing".to_string()));
        assert_eq!(rule.to_string(), "all: ; # nothing\n");
    }

    #[test]
    fn test_empty_inline_recipe() {
        let rule: Rule = "all: ;\n".parse().unwrap();
        assert_eq!(prereqs(&rule), (vec![], vec![]));
        assert_eq!(recipes(&rule), vec![""]);
        assert_eq!(rule.to_string(), "all: ;\n");
    }

    #[test]
    fn test_inline_recipe_at_eof() {
        let rule: Rule = "all: ; echo hi".parse().unwrap();
        assert_eq!(recipes(&rule), vec!["echo hi"]);
        assert_eq!(rule.to_string(), "all: ; echo hi");
    }

    #[test]
    fn test_comment_before_semicolon() {
        let rule: Rule = "all: dep # c ; echo hi\n".parse().unwrap();
        assert_eq!(prereqs(&rule), (vec!["dep".to_string()], vec![]));
        assert_eq!(recipes(&rule), Vec::<String>::new());
    }

    #[test]
    fn test_semicolon_in_variable_reference() {
        let rule: Rule = "all: $(shell a;b) ; echo hi\n".parse().unwrap();
        assert_eq!(prereqs(&rule), (vec!["$(shell a;b)".to_string()], vec![]));
        assert_eq!(recipes(&rule), vec!["echo hi"]);
    }

    #[test]
    fn test_semicolon_in_target_specific_assignment() {
        let rule: Rule = "foo: X = a;b\n".parse().unwrap();
        assert_eq!(recipes(&rule), Vec::<String>::new());
        assert_eq!(
            rule.scoped_assignment().unwrap().raw_value(),
            Some("a;b".to_string())
        );
    }

    #[test]
    fn test_inline_recipe_with_continuation() {
        let input = "all: ; echo a \\\n\tb\n\techo c\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(recipes(&rule), vec!["echo a \\\nb", "echo c"]);
        assert_eq!(rule.to_string(), input);
    }

    #[test]
    fn test_inline_recipe_with_other_rule_forms() {
        let rule: Rule = "$(OBJS): %.o: %.c | dir ; $(CC) -c $<\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
        assert_eq!(
            prereqs(&rule),
            (vec!["%.c".to_string()], vec!["dir".to_string()])
        );
        assert_eq!(recipes(&rule), vec!["$(CC) -c $<"]);

        let rule: Rule = "all:: dep ; echo hi\n".parse().unwrap();
        assert!(rule.is_double_colon());
        assert_eq!(recipes(&rule), vec!["echo hi"]);

        let rule: Rule = "a b &: c ; touch a b\n".parse().unwrap();
        assert!(rule.is_grouped());
        assert_eq!(prereqs(&rule), (vec!["c".to_string()], vec![]));
        assert_eq!(recipes(&rule), vec!["touch a b"]);

        let rule: Rule = "foo: a:b ; echo hi\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), Some("a".to_string()));
        assert_eq!(prereqs(&rule), (vec!["b".to_string()], vec![]));

        let rule: Rule = "foo: a ; echo x:y\n".parse().unwrap();
        assert_eq!(rule.static_pattern(), None);
        assert_eq!(recipes(&rule), vec!["echo x:y"]);
    }

    #[test]
    fn test_inline_recipe_bsd_dependency_operator() {
        let makefile: Makefile = "a! b ; echo hi\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(prereqs(&rule), (vec!["b".to_string()], vec![]));
        assert_eq!(recipes(&rule), vec!["echo hi"]);
    }

    #[test]
    fn test_replace_inline_recipe() {
        let mut rule: Rule = "all: dep ; echo hi\n\techo 2\n".parse().unwrap();
        assert!(rule.replace_command(0, "echo bye"));
        assert_eq!(rule.to_string(), "all: dep ; echo bye\n\techo 2\n");
        let mut recipe = rule.recipe_nodes().next().unwrap();
        recipe.set_prefix("@");
        assert_eq!(rule.to_string(), "all: dep ; @echo bye\n\techo 2\n");
        assert_eq!(recipes(&rule), vec!["@echo bye", "echo 2"]);
    }

    #[test]
    fn test_push_command_after_inline_recipe() {
        let mut rule: Rule = "all: ; echo hi\n".parse().unwrap();
        rule.push_command("echo 2");
        assert_eq!(rule.to_string(), "all: ; echo hi\n\techo 2\n");
        assert_eq!(recipes(&rule), vec!["echo hi", "echo 2"]);
    }

    #[test]
    fn test_remove_inline_recipe() {
        let mut rule: Rule = "all: dep ; echo hi\n\techo 2\n".parse().unwrap();
        assert!(rule.remove_command(0));
        assert_eq!(rule.to_string(), "all: dep\n\techo 2\n");
        assert_eq!(recipes(&rule), vec!["echo 2"]);

        let rule: Rule = "all: ; echo hi\n".parse().unwrap();
        rule.recipe_nodes().next().unwrap().remove();
        assert_eq!(rule.to_string(), "all:\n");
    }

    #[test]
    fn test_insert_before_inline_recipe() {
        let mut rule: Rule = "all: dep ; echo hi\n".parse().unwrap();
        assert!(rule.insert_command(0, "echo 0"));
        assert_eq!(rule.to_string(), "all: dep\n\techo 0\n\techo hi\n");

        let rule: Rule = "all: ; echo hi\n".parse().unwrap();
        rule.recipe_nodes().next().unwrap().insert_before("echo 0");
        assert_eq!(rule.to_string(), "all:\n\techo 0\n\techo hi\n");
        assert_eq!(recipes(&rule), vec!["echo 0", "echo hi"]);
    }

    #[test]
    fn test_insert_after_inline_recipe() {
        let mut rule: Rule = "all: dep ; echo hi\n".parse().unwrap();
        assert!(rule.insert_command(1, "echo 2"));
        assert_eq!(rule.to_string(), "all: dep ; echo hi\n\techo 2\n");
    }

    #[test]
    fn test_clear_commands_with_inline_recipe() {
        let mut rule: Rule = "all: dep ; echo hi\n\techo 2\n".parse().unwrap();
        rule.clear_commands();
        assert_eq!(rule.to_string(), "all: dep\n");
        assert_eq!(rule.recipe_count(), 0);
    }

    #[test]
    fn test_set_prerequisites_with_inline_recipe() {
        let mut rule: Rule = "all: dep ; echo hi\n".parse().unwrap();
        rule.add_prerequisite("dep2").unwrap();
        assert_eq!(prereqs(&rule).0, vec!["dep", "dep2"]);
        assert_eq!(recipes(&rule), vec!["echo hi"]);
        assert_eq!(rule.to_string(), "all: dep dep2 ; echo hi\n");
    }

    #[test]
    fn test_set_prerequisites_keeps_comment() {
        let mut rule: Rule = "foo: a # c\n".parse().unwrap();
        rule.add_prerequisite("b").unwrap();
        assert_eq!(rule.to_string(), "foo: a b # c\n");
        rule.set_prerequisites(vec![]).unwrap();
        assert_eq!(rule.to_string(), "foo: # c\n");
    }

    #[test]
    fn test_inline_recipe_continuation_after_hash() {
        let input = "all: ; echo hi # x \\\n\techo more\n\techo next\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(
            recipes(&rule),
            vec!["echo hi # x \\\necho more", "echo next"]
        );
        assert_eq!(rule.to_string(), input);
    }

    #[test]
    fn test_inline_recipe_escaped_backslash() {
        let input = "all: ; echo a\\\\\n\techo b\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(recipes(&rule), vec!["echo a\\\\", "echo b"]);
        assert_eq!(rule.to_string(), input);
    }

    #[test]
    fn test_recipe_continues_after_blank_line_and_comment() {
        // Make runs both commands for `rule`.
        let makefile: Makefile = "rule:\n\tcommand\n\n# a comment\n\tmore\n".parse().unwrap();
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 1);
        assert_eq!(
            rules[0].recipes().collect::<Vec<_>>(),
            vec!["command", "more"]
        );
    }

    #[test]
    fn test_conditional_recipe_after_blank_line() {
        // As in Linux's arch/m68k/Makefile; both makes run the recipe lines
        // in the conditional for `vmlinux.gz`.
        for (text, variant) in [
            (
                "vmlinux.gz: vmlinux\n\nifndef X\n\tcp a b\nendif\n",
                crate::MakefileVariant::GNUMake,
            ),
            (
                "vmlinux.gz: vmlinux\n\n.if !defined(X)\n\tcp a b\n.endif\n",
                crate::MakefileVariant::BSDMake,
            ),
        ] {
            let parsed = Makefile::parse_with_variant(text, variant);
            assert!(parsed.ok());
            let makefile = parsed.tree();
            assert_eq!(makefile.conditionals().count(), 0, "{variant:?}");
            let rule = makefile.rules().next().unwrap();
            assert_eq!(rule.items().count(), 1, "{variant:?}");
        }
    }

    fn targets(rule: &Rule) -> Vec<String> {
        rule.targets().collect()
    }

    #[test]
    fn test_prerequisite_continuation_in_function_call() {
        let input = "all: $(addprefix x, \\\n  a b) c\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (
                vec!["$(addprefix x, a b)".to_string(), "c".to_string()],
                vec![]
            )
        );
        assert_eq!(rule.to_string(), input);
    }

    #[test]
    fn test_prerequisite_continuation_in_braced_reference() {
        let input = "all: ${addprefix x, \\\n\ta b}\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (vec!["${addprefix x, a b}".to_string()], vec![])
        );
    }

    #[test]
    fn test_prerequisite_continuation_in_braced_reference_bsd() {
        let input = "all: ${FOO:S/a/b/ \\\n\t:S/c/d/}\n";
        let makefile = Makefile::parse_with_variant(input, crate::MakefileVariant::BSDMake).tree();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            prereqs(&rule),
            (vec!["${FOO:S/a/b/ :S/c/d/}".to_string()], vec![])
        );
        assert_eq!(makefile.to_string(), input);
    }

    #[test]
    fn test_prerequisite_continuation_crlf() {
        let input = "all: $(addprefix x, \\\r\n  a b) \\\r\n  c\r\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (
                vec!["$(addprefix x, a b)".to_string(), "c".to_string()],
                vec![]
            )
        );
        assert_eq!(rule.to_string(), input);
    }

    #[test]
    fn test_prerequisite_escaped_backslash_after_reference() {
        let input = "all: $(X)\\\\\n\techo hi\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(prereqs(&rule), (vec!["$(X)\\\\".to_string()], vec![]));
        assert_eq!(recipes(&rule), vec!["echo hi"]);
    }

    #[test]
    fn test_order_only_prerequisite_continuation_in_function_call() {
        let input = "all: a | $(addprefix x, \\\n  a b)\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (
                vec!["a".to_string()],
                vec!["$(addprefix x, a b)".to_string()]
            )
        );
    }

    #[test]
    fn test_target_continuation_in_function_call() {
        let input = "$(addprefix x, \\\n  a b) c: d\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(targets(&rule), vec!["$(addprefix x, a b)", "c"]);
        assert_eq!(prereqs(&rule), (vec!["d".to_string()], vec![]));
        assert_eq!(rule.to_string(), input);
    }

    #[test]
    fn test_static_pattern_continuation_in_function_call() {
        let input = "a.o: $(patsubst %,%, \\\n  %.o): %.c\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(targets(&rule), vec!["a.o"]);
        assert_eq!(
            rule.static_pattern(),
            Some("$(patsubst %,%, %.o)".to_string())
        );
        assert_eq!(prereqs(&rule), (vec!["%.c".to_string()], vec![]));
    }
}
