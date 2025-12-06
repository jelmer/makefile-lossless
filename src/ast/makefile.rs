use crate::lossless::{
    matches_pattern, parse, Conditional, Error, ErrorInfo, Include,
    Makefile, MakefileItem, ParseError, Rule, SyntaxNode, VariableDefinition,
};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::GreenNodeBuilder;

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
}
