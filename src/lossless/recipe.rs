use super::*;
use crate::ast::{line_ending, terminate_line_before};
use rowan::{GreenNode, GreenToken};

type GreenElement = rowan::NodeOrToken<GreenNode, GreenToken>;

/// The elements of a recipe line holding the command `line`, between its
/// indentation and its line ending, as the parser reads them.
///
/// Returns an error if `line` can not be written as a single recipe line:
/// if it contains a newline outside of a line continuation, or ends in a
/// line continuation that would join it with the next line.
fn recipe_line_content(line: &str, context: &str) -> Result<Vec<GreenElement>, Error> {
    let parsed = parse(&format!("x:\n\t{line}\n\tz\n"), None);
    let mut rules = parsed.root().syntax().children();
    let recipes: Vec<_> = rules
        .next()
        .filter(|rule| rule.kind() == RULE && rules.next().is_none())
        .into_iter()
        .flat_map(|rule| rule.children().filter(|n| n.kind() == RECIPE))
        .collect();
    let [recipe, last] = recipes.as_slice() else {
        return Err(recipe_line_error(line, context));
    };
    if !parsed.errors.is_empty()
        || recipe.text() != format!("\t{line}\n").as_str()
        || last.text() != "\tz\n"
    {
        return Err(recipe_line_error(line, context));
    }
    let children: Vec<_> = recipe.green().children().map(|c| c.to_owned()).collect();
    Ok(children[1..children.len() - 1].to_vec())
}

fn recipe_line_error(line: &str, context: &str) -> Error {
    Error::Parse(ParseError {
        errors: vec![ErrorInfo {
            kind: crate::ParseErrorKind::Other,
            message: format!("Cannot write {line:?} as a single recipe line"),
            line: 1,
            context: context.to_string(),
        }],
    })
}

/// A RECIPE node for the command `line`, starting with `prefix` and ending
/// with the line ending `eol`.
fn build_recipe(
    prefix: Vec<GreenElement>,
    line: &str,
    eol: &str,
    context: &str,
) -> Result<SyntaxNode, Error> {
    let mut children = prefix;
    children.extend(recipe_line_content(line, context)?);
    children.push(GreenToken::new(NEWLINE.into(), eol).into());
    Ok(SyntaxNode::new_root_mut(GreenNode::new(
        RECIPE.into(),
        children,
    )))
}

fn tab() -> Vec<GreenElement> {
    vec![GreenToken::new(INDENT.into(), "\t").into()]
}

/// A tab-indented RECIPE node for the command `line`, as [`build_recipe`].
pub(crate) fn build_command(line: &str, eol: &str, context: &str) -> Result<SyntaxNode, Error> {
    build_recipe(tab(), line, eol, context)
}

impl Recipe {
    /// Get the text content of this recipe line (the command to execute)
    ///
    /// For single-line recipes, this returns the command text excluding the
    /// leading tab and trailing newline.
    ///
    /// For multi-line recipes (with backslash continuations), this returns the
    /// full text including the internal newlines and continuation-line indentation,
    /// but still excluding the leading tab of the first line and the final newline.
    /// This preserves the exact content needed for a lossless round-trip.
    ///
    /// For comment-only lines, this returns an empty string.
    pub fn text(&self) -> String {
        self.logical_text(false)
    }

    /// Get the text of this recipe line as GNU make hands it to the shell,
    /// before variable expansion.
    ///
    /// This is the line without its leading tab. Unlike [`Recipe::text`],
    /// lines starting with `#` are included: make does not treat `#` in a
    /// recipe as a comment, it passes it on to the shell. For lines split
    /// with backslash-newline, the backslash and newline are kept and a single
    /// leading tab is removed from each continuation line.
    ///
    /// Prefix characters (`@`, `-`, `+`) are not removed. make strips those
    /// after variable expansion, since they may come from a variable; see
    /// [`Recipe::is_silent`] and [`Recipe::is_ignore_errors`] for the literal
    /// ones.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\t# note\n\t@echo a \\\n\t\tb # c\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipes: Vec<_> = rule.recipe_nodes().collect();
    /// assert_eq!(recipes[0].shell_text(), "# note");
    /// assert_eq!(recipes[1].shell_text(), "@echo a \\\n\tb # c");
    /// ```
    pub fn shell_text(&self) -> String {
        self.logical_text(true)
    }

    fn logical_text(&self, include_comments: bool) -> String {
        let mut after_newline = false;
        let comment = self.comment_start();
        self.body_tokens()
            .filter_map(|t| {
                if !include_comments && comment.is_some_and(|c| t.text_range().start() >= c) {
                    return None;
                }
                // Tokens in a reference are all text.
                let nested = t.parent().as_ref() != Some(self.syntax());
                match t.kind() {
                    NEWLINE => {
                        after_newline = true;
                        Some(lf_line_endings(t.text()))
                    }
                    // Strip the leading tab from continuation-line indentation
                    INDENT if after_newline => {
                        after_newline = false;
                        let text = t.text();
                        Some(text.strip_prefix('\t').unwrap_or(text).to_string())
                    }
                    COMMENT if include_comments => {
                        after_newline = false;
                        Some(t.text().to_string())
                    }
                    // Other tokens directly in the node are the `;` and the
                    // whitespace before a recipe on the rule line.
                    _ if t.kind() == TEXT || nested => {
                        after_newline = false;
                        Some(t.text().to_string())
                    }
                    _ => None,
                }
            })
            .collect()
    }

    /// The start of the comment that this line consists of, if it starts
    /// with `#`. The references in it are parsed, as GNU make expands it,
    /// but [`Recipe::text`] leaves it out.
    fn comment_start(&self) -> Option<rowan::TextSize> {
        self.syntax()
            .children_with_tokens()
            .find(|it| it.kind() == COMMENT)
            .map(|it| it.text_range().start())
    }

    /// The tokens of this recipe without the leading indentation and the
    /// trailing newline.
    fn body_tokens(&self) -> impl Iterator<Item = SyntaxToken> {
        let first = self
            .syntax()
            .first_child_or_token()
            .and_then(|it| it.into_token())
            .filter(|t| t.kind() == INDENT);
        let last = self
            .syntax()
            .last_child_or_token()
            .and_then(|it| it.into_token())
            .filter(|t| t.kind() == NEWLINE);
        self.syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(move |t| Some(t) != first.as_ref() && Some(t) != last.as_ref())
    }

    /// The text of each line of the command, with its start: the runs of
    /// text between line breaks, indentation and comments.
    fn text_lines(&self) -> Vec<(rowan::TextSize, String)> {
        let mut lines: Vec<(rowan::TextSize, String)> = vec![];
        let mut in_line = false;
        let comment = self.comment_start();
        for token in self
            .syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
        {
            let nested = token.parent().as_ref() != Some(self.syntax());
            let is_text = !matches!(token.kind(), NEWLINE | INDENT)
                && (nested || token.kind() == TEXT)
                && comment.is_none_or(|c| token.text_range().start() < c);
            match lines.last_mut() {
                Some((_, line)) if is_text && in_line => line.push_str(token.text()),
                _ if is_text => lines.push((token.text_range().start(), token.text().to_string())),
                _ => {}
            }
            in_line = is_text;
        }
        lines
    }

    /// The text of the first line of the command, if any.
    pub(crate) fn first_line_text(&self) -> Option<String> {
        self.text_lines().into_iter().next().map(|(_, text)| text)
    }

    /// Iterate the variable references in this recipe, in source order.
    ///
    /// These are all references, as in [`Makefile::variable_references`]:
    /// variables, function calls, automatic variables such as `$@` and
    /// `$(@D)`, and references nested in others. A `$$` is not a reference.
    /// References are found as make finds them when it expands the recipe,
    /// so a reference may continue on the next line after a line
    /// continuation. An unterminated reference is left as text. Lines
    /// starting with `#` are searched too, as GNU make expands them, except
    /// for BSD make and nmake, which skip them.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\t$(CC) -o $@ $(addprefix -I,$(DIRS)) $$HOME\n"
    ///     .parse()
    ///     .unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipe = rule.recipe_nodes().next().unwrap();
    /// let refs: Vec<_> = recipe.references().map(|r| r.to_string()).collect();
    /// assert_eq!(refs, vec!["$(CC)", "$@", "$(addprefix -I,$(DIRS))", "$(DIRS)"]);
    /// ```
    pub fn references(&self) -> impl Iterator<Item = VariableReference> {
        self.syntax()
            .descendants()
            .filter_map(VariableReference::cast)
    }

    /// Get the indentation string of this recipe line.
    ///
    /// Returns the leading indentation (typically a tab character) of this recipe line,
    /// or `None` if no indent token is present, as for a recipe on the rule
    /// line after a `;`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipe = rule.recipe_nodes().next().unwrap();
    /// assert_eq!(recipe.indent(), Some("\t".to_string()));
    /// ```
    pub fn indent(&self) -> Option<String> {
        self.syntax().children_with_tokens().find_map(|it| {
            if let Some(token) = it.as_token() {
                if token.kind() == INDENT {
                    return Some(token.text().to_string());
                }
            }
            None
        })
    }

    /// Get the comment content of this recipe line, if any
    ///
    /// Returns the comment text (including the '#' character) if this recipe
    /// line contains a comment, or None if there is no comment.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\t# This is a comment\n\techo hello\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipes: Vec<_> = rule.recipe_nodes().collect();
    /// assert_eq!(recipes[0].comment(), Some("# This is a comment".to_string()));
    /// assert_eq!(recipes[1].comment(), None);
    /// ```
    pub fn comment(&self) -> Option<String> {
        let token = self
            .syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == COMMENT)?;
        let elements = comment_elements(&token)?;
        Some(elements.iter().map(|it| it.to_string()).collect())
    }

    /// Get the full content of this recipe line
    ///
    /// Returns all content including command text, comments, and internal whitespace,
    /// but excluding the leading indent. This is useful for getting the complete
    /// content of a recipe line regardless of whether it's a command, comment, or both.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\techo hello # inline comment\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipe = rule.recipe_nodes().next().unwrap();
    /// assert_eq!(recipe.full(), "echo hello # inline comment");
    /// ```
    pub fn full(&self) -> String {
        self.syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|token| match token.kind() {
                INDENT | NEWLINE => false,
                TEXT | COMMENT => true,
                // Anything in a reference is text.
                _ => token.parent().as_ref() != Some(self.syntax()),
            })
            .map(|token| token.text().to_string())
            .collect()
    }

    /// Get the parent rule containing this recipe
    ///
    /// For a recipe inside a conditional or BSD `.for` loop in a rule's body,
    /// this is that rule.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipe = rule.recipe_nodes().next().unwrap();
    /// let parent = recipe.parent().unwrap();
    /// assert_eq!(parent.targets().collect::<Vec<_>>(), vec!["all"]);
    /// ```
    pub fn parent(&self) -> Option<Rule> {
        // A recipe can be inside a conditional or `.for` loop in the rule.
        self.syntax().ancestors().find_map(Rule::cast)
    }

    /// Check if this recipe has the silent prefix (@)
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\t@echo hello\n\techo world\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipes: Vec<_> = rule.recipe_nodes().collect();
    /// assert!(recipes[0].is_silent());
    /// assert!(!recipes[1].is_silent());
    /// ```
    pub fn is_silent(&self) -> bool {
        let text = self.text();
        text.starts_with('@') || text.starts_with("-@") || text.starts_with("+@")
    }

    /// Check if this recipe has the ignore-errors prefix (-)
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\t-echo hello\n\techo world\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipes: Vec<_> = rule.recipe_nodes().collect();
    /// assert!(recipes[0].is_ignore_errors());
    /// assert!(!recipes[1].is_ignore_errors());
    /// ```
    pub fn is_ignore_errors(&self) -> bool {
        let text = self.text();
        text.starts_with('-') || text.starts_with("@-") || text.starts_with("+-")
    }

    /// Set the command prefix for this recipe
    ///
    /// The prefix can contain `@` (silent), `-` (ignore errors), and/or `+` (always execute).
    /// Pass an empty string to remove all prefixes.
    ///
    /// Panics if the prefix contains a newline, as [`Recipe::replace_text`]
    /// does.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let mut makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// recipe.set_prefix("@");
    /// assert_eq!(recipe.text(), "@echo hello");
    /// assert!(recipe.is_silent());
    /// ```
    pub fn set_prefix(&mut self, prefix: &str) {
        let text = self.text();

        // Strip existing prefix characters
        let stripped = text.trim_start_matches(['@', '-', '+']);

        // Build new text with the new prefix
        let new_text = format!("{}{}", prefix, stripped);

        self.replace_text(&new_text);
    }

    /// Replace the text content of this recipe line
    ///
    /// # Panics
    ///
    /// Panics if `new_text` can not be written as a single recipe line,
    /// such as text containing a newline that is not part of a line
    /// continuation. Use [`Recipe::try_replace_text`] to get an error
    /// instead.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let mut makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// recipe.replace_text("echo world");
    /// assert_eq!(recipe.text(), "echo world");
    /// ```
    pub fn replace_text(&mut self, new_text: &str) {
        self.try_replace_text(new_text)
            .unwrap_or_else(|e| panic!("invalid recipe line: {e}"))
    }

    /// Replace the text content of this recipe line, like
    /// [`Recipe::replace_text`]
    ///
    /// Returns an error, leaving the recipe unchanged, if `new_text` can
    /// not be written as a single recipe line. A line continuation is
    /// allowed, but a newline not preceded by a backslash or a trailing
    /// backslash that would join the line with the next one is not.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let mut makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// recipe.try_replace_text("echo a \\\n\tb").unwrap();
    /// assert!(recipe.try_replace_text("echo a\necho b").is_err());
    /// assert_eq!(makefile.to_string(), "all:\n\techo a \\\n\tb\n");
    /// ```
    pub fn try_replace_text(&mut self, new_text: &str) -> Result<(), Error> {
        let node = self.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");
        let node_index = node.index();

        let inline_prefix = self.inline_prefix();
        let prefix: Vec<GreenElement> = if !inline_prefix.is_empty() {
            inline_prefix
                .iter()
                .map(|t| GreenToken::new(t.kind().into(), t.text()).into())
                .collect()
        } else if let Some(indent_token) = node
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == INDENT)
        {
            // Preserve the existing INDENT token
            vec![GreenToken::new(INDENT.into(), indent_token.text()).into()]
        } else {
            tab()
        };

        // Preserve the existing NEWLINE token if present
        let eol = node
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == NEWLINE)
            .last()
            .map_or_else(|| line_ending(node), |t| t.text().to_string());

        let new_syntax = build_recipe(prefix, new_text, &eol, "replace_text")?;

        // Replace the old node with the new one
        parent.splice_children(node_index..node_index + 1, vec![new_syntax.into()]);

        // Update self to point to the new node
        // Note: index() returns position among all siblings (nodes + tokens)
        // so we need to use children_with_tokens() and filter for the node
        *self = parent
            .children_with_tokens()
            .nth(node_index)
            .and_then(|element| element.into_node())
            .and_then(Recipe::cast)
            .expect("New recipe node should exist at the same index");
        Ok(())
    }

    /// Insert a new recipe line before this one
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let mut makefile: Makefile = "all:\n\techo world\n".parse().unwrap();
    /// let mut rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// recipe.insert_before("echo hello");
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo hello", "echo world"]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `text` can not be written as a single recipe line. Use
    /// [`Recipe::try_insert_before`] to get an error instead.
    pub fn insert_before(&self, text: &str) {
        self.try_insert_before(text)
            .unwrap_or_else(|e| panic!("invalid recipe line: {e}"))
    }

    /// Insert a new recipe line before this one, like
    /// [`Recipe::insert_before`]
    ///
    /// Returns an error, leaving the rule unchanged, if `text` can not be
    /// written as a single recipe line, as for [`Recipe::try_replace_text`].
    pub fn try_insert_before(&self, text: &str) -> Result<(), Error> {
        let new_syntax = build_command(text, &line_ending(self.syntax()), "insert_before")?;
        // A recipe on the rule line has to move to its own line first.
        let this = self.move_to_own_line().unwrap_or_else(|| self.clone());
        let node = this.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");
        let node_index = node.index();

        parent.splice_children(node_index..node_index, vec![new_syntax.into()]);
        Ok(())
    }

    /// Insert a new recipe line after this one
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let mut makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    /// let mut rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// recipe.insert_after("echo world");
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo hello", "echo world"]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `text` can not be written as a single recipe line. Use
    /// [`Recipe::try_insert_after`] to get an error instead.
    pub fn insert_after(&self, text: &str) {
        self.try_insert_after(text)
            .unwrap_or_else(|e| panic!("invalid recipe line: {e}"))
    }

    /// Insert a new recipe line after this one, like [`Recipe::insert_after`]
    ///
    /// Returns an error, leaving the rule unchanged, if `text` can not be
    /// written as a single recipe line, as for [`Recipe::try_replace_text`].
    pub fn try_insert_after(&self, text: &str) -> Result<(), Error> {
        let node = self.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");
        let eol = line_ending(node);
        let new_syntax = build_command(text, &eol, "insert_after")?;

        let index = terminate_line_before(&parent, node.index() + 1, &eol);
        parent.splice_children(index..index, vec![new_syntax.into()]);
        Ok(())
    }

    /// Remove this recipe line from its parent
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let mut makefile: Makefile = "all:\n\techo hello\n\techo world\n".parse().unwrap();
    /// let mut rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// recipe.remove();
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo world"]);
    /// ```
    pub fn remove(&self) {
        let node = self.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");

        if !self.is_inline() {
            let node_index = node.index();
            parent.splice_children(node_index..node_index + 1, vec![]);
            return;
        }

        // A recipe on the rule line also holds the rule line's newline,
        // which has to stay.
        self.trim_preceding_whitespace();
        let newline = node
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == NEWLINE)
            .map(|t| t.text().to_string());
        let mut replacement = Vec::new();
        if let Some(newline) = newline {
            replacement.extend(detached_elements(&[(NEWLINE, &newline)], None));
        }
        let node_index = node.index();
        parent.splice_children(node_index..node_index + 1, replacement);
    }

    /// Whether this recipe is on the rule line, after a `;`.
    pub(crate) fn is_inline(&self) -> bool {
        self.syntax()
            .first_token()
            .is_some_and(|t| t.kind() == OPERATOR && t.text() == ";")
    }

    /// For a recipe on the rule line, the `;` and the whitespace after it.
    fn inline_prefix(&self) -> Vec<SyntaxToken> {
        if !self.is_inline() {
            return Vec::new();
        }
        self.syntax()
            .children_with_tokens()
            .map_while(|it| it.into_token())
            .enumerate()
            .take_while(|(i, t)| *i == 0 || t.kind() == WHITESPACE)
            .map(|(_, t)| t)
            .collect()
    }

    /// Remove whitespace at the end of the rule line, before a recipe on
    /// the rule line.
    fn trim_preceding_whitespace(&self) {
        // Walk the siblings rather than using prev_token(), which stops at
        // an empty node such as the PREREQUISITES of `all: ; cmd`.
        let mut current = self.syntax().prev_sibling_or_token();
        while let Some(element) = current {
            current = element.prev_sibling_or_token();
            match element {
                rowan::NodeOrToken::Token(token) if token.kind() == WHITESPACE => token.detach(),
                rowan::NodeOrToken::Node(node) => {
                    while let Some(token) = node.last_token().filter(|t| t.kind() == WHITESPACE) {
                        token.detach();
                    }
                    if node.first_token().is_some() {
                        break;
                    }
                }
                rowan::NodeOrToken::Token(_) => break,
            }
        }
    }

    /// Move a recipe on the rule line to a line of its own, returning the
    /// new recipe node, or `None` if this recipe is not on the rule line.
    fn move_to_own_line(&self) -> Option<Recipe> {
        if !self.is_inline() {
            return None;
        }
        let node = self.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");
        let skip = self.inline_prefix().len();
        self.trim_preceding_whitespace();

        let mut recipe = vec![GreenToken::new(INDENT.into(), "\t").into()];
        recipe.extend(
            node.green()
                .children()
                .skip(skip)
                .map(|child| child.to_owned()),
        );
        let newline = line_ending(node);
        let elements = detached_elements(
            &[(NEWLINE, &newline)],
            Some(GreenNode::new(RECIPE.into(), recipe)),
        );

        let node_index = node.index();
        parent.splice_children(node_index..node_index + 1, elements);
        parent
            .children_with_tokens()
            .nth(node_index + 1)
            .and_then(|it| it.into_node())
            .and_then(Recipe::cast)
    }

    /// Iterate `$(VAR)` and `${VAR}` variable references inside this recipe.
    ///
    /// This scans the text of each line of the recipe and yields each
    /// reference with the source range of its name. [`Recipe::references`]
    /// gives the reference nodes in the syntax tree instead, which also cover
    /// references continued on the next line.
    ///
    /// Function calls (`$(shell ...)`, anything with whitespace or commas after
    /// the name) and automatic variables (`$@`, `$<`, numeric `$1`) are skipped;
    /// only plain variable references are returned, including those inside
    /// function calls. Modifiers are not part of the name, so the name of
    /// `${SRCS:M*.c}` is `SRCS`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = "all:\n\techo $(FOO) ${BAR}\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let recipe = rule.recipe_nodes().next().unwrap();
    /// let names: Vec<_> = recipe
    ///     .variable_references()
    ///     .iter()
    ///     .map(|r| r.name().to_string())
    ///     .collect();
    /// assert_eq!(names, vec!["FOO", "BAR"]);
    /// ```
    #[deprecated(
        note = "use Recipe::references, which also finds function calls, automatic variables and references continued on the next line"
    )]
    pub fn variable_references(&self) -> Vec<RecipeVariableReference> {
        let mut out = Vec::new();
        for (start, text) in self.text_lines() {
            scan_recipe_variable_refs(&text, start.into(), &mut out);
        }
        out
    }
}

/// A `$(VAR)` or `${VAR}` reference found inside a recipe or `define` body.
///
/// These are found by scanning text rather than in the syntax tree, so this
/// type carries just the variable name and its absolute source range.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecipeVariableReference {
    name: String,
    range: rowan::TextRange,
}

impl RecipeVariableReference {
    /// The referenced variable name (without the surrounding `$(...)`).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The absolute source range covering just the variable name.
    pub fn text_range(&self) -> rowan::TextRange {
        self.range
    }
}

/// Scan `text` for `$(VAR)` / `${VAR}` references, pushing each onto `out` with
/// ranges offset by `base` (the absolute start of `text` in the source).
///
/// As in [`VariableReference::name`], the name ends before any modifiers, as
/// in `${SRCS:M*.c}`, and may contain nested references, as in `${VAR.${M}}`.
/// References inside other references, such as in modifiers or function
/// arguments, are reported too.
pub(crate) fn scan_recipe_variable_refs(
    text: &str,
    base: u32,
    out: &mut Vec<RecipeVariableReference>,
) {
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'$' || i + 1 >= bytes.len() {
            i += 1;
            continue;
        }
        let close = match bytes[i + 1] {
            b'(' => b')',
            b'{' => b'}',
            _ => {
                i += 2;
                continue;
            }
        };
        let name_start = i + 2;
        let Some((name_end, terminator)) = find_name_end(bytes, name_start, close) else {
            i += 2;
            continue;
        };
        let name = &text[name_start..name_end];
        // Function calls like $(shell ...) have whitespace after the name;
        // pure-numeric names are automatic variables ($1, $2, ...).
        let is_variable = !name.is_empty()
            && !matches!(terminator, b' ' | b'\t' | b',')
            && !name.chars().all(|c| c.is_ascii_digit());
        if is_variable {
            out.push(RecipeVariableReference {
                name: name.to_owned(),
                range: rowan::TextRange::new(
                    rowan::TextSize::from(base + name_start as u32),
                    rowan::TextSize::from(base + name_end as u32),
                ),
            });
        }
        // Continue inside the reference to find nested ones.
        i = name_start;
    }
}

/// Find the end of the variable name starting at `start` in a reference
/// closed by `close`, skipping nested references. Returns the end and the
/// byte that ended the name, or `None` if the reference is not closed.
fn find_name_end(bytes: &[u8], start: usize, close: u8) -> Option<(usize, u8)> {
    let mut i = start;
    while i < bytes.len() {
        match bytes[i] {
            b'$' if matches!(bytes.get(i + 1), Some(b'(' | b'{')) => {
                let nested_close = if bytes[i + 1] == b'(' { b')' } else { b'}' };
                i = find_reference_end(bytes, i + 2, nested_close)? + 1;
            }
            c if c == close || matches!(c, b':' | b' ' | b'\t' | b',') => return Some((i, c)),
            b'\n' => return None,
            _ => i += 1,
        }
    }
    None
}

/// Find the delimiter closing a reference whose contents start at `start`.
fn find_reference_end(bytes: &[u8], start: usize, close: u8) -> Option<usize> {
    let open = if close == b')' { b'(' } else { b'{' };
    let mut depth = 0usize;
    for (i, &c) in bytes.iter().enumerate().skip(start) {
        if c == open {
            depth += 1;
        } else if c == close {
            if depth == 0 {
                return Some(i);
            }
            depth -= 1;
        } else if c == b'\n' {
            return None;
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_comment_line_references() {
        // GNU make expands a recipe line starting with `#` before passing it
        // to the shell.
        let text = "all:\n\t# $(info a) $(X:.c=$(Y)) b\n\t@# $(Z)\nb: ; # ${W}\n";
        let makefile: Makefile = text.parse().unwrap();
        let recipes: Vec<_> = makefile.rules().flat_map(|r| r.recipe_nodes()).collect();
        let refs: Vec<Vec<_>> = recipes
            .iter()
            .map(|r| r.references().map(|x| x.to_string()).collect())
            .collect();
        assert_eq!(
            refs,
            vec![
                vec!["$(info a)", "$(X:.c=$(Y))", "$(Y)"],
                vec!["$(Z)"],
                vec!["${W}"]
            ]
        );
        let accessors: Vec<_> = recipes
            .iter()
            .map(|r| (r.text(), r.comment(), r.full(), r.shell_text()))
            .collect();
        assert_eq!(
            accessors,
            vec![
                (
                    String::new(),
                    Some("# $(info a) $(X:.c=$(Y)) b".to_string()),
                    "# $(info a) $(X:.c=$(Y)) b".to_string(),
                    "# $(info a) $(X:.c=$(Y)) b".to_string()
                ),
                (
                    "@# $(Z)".to_string(),
                    None,
                    "@# $(Z)".to_string(),
                    "@# $(Z)".to_string()
                ),
                (
                    String::new(),
                    Some("# ${W}".to_string()),
                    "# ${W}".to_string(),
                    "# ${W}".to_string()
                ),
            ]
        );
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["", "@# $(Z)"]);
        assert_eq!(makefile.to_string(), text);
    }

    #[test]
    fn test_comment_line_references_bsd_nmake() {
        // BSD make and nmake skip such lines.
        for variant in [
            crate::MakefileVariant::BSDMake,
            crate::MakefileVariant::NMake,
        ] {
            let makefile = Makefile::parse_with_variant("all:\n\t# $(X)\n", variant).tree();
            let recipe = makefile
                .rules()
                .next()
                .unwrap()
                .recipe_nodes()
                .next()
                .unwrap();
            assert_eq!(recipe.references().count(), 0, "{variant:?}");
            assert_eq!(recipe.comment(), Some("# $(X)".to_string()));
        }
    }

    #[test]
    fn test_recipe_is_silent_various_prefixes() {
        let makefile: Makefile = r#"test:
	@echo silent
	-echo ignore
	+echo always
	@-echo silent_ignore
	-@echo ignore_silent
	+@echo always_silent
	echo normal
"#
        .parse()
        .unwrap();

        let rule = makefile.rules().next().unwrap();
        let recipes: Vec<_> = rule.recipe_nodes().collect();

        assert_eq!(recipes.len(), 7);
        assert!(recipes[0].is_silent(), "@echo should be silent");
        assert!(!recipes[1].is_silent(), "-echo should not be silent");
        assert!(!recipes[2].is_silent(), "+echo should not be silent");
        assert!(recipes[3].is_silent(), "@-echo should be silent");
        assert!(recipes[4].is_silent(), "-@echo should be silent");
        assert!(recipes[5].is_silent(), "+@echo should be silent");
        assert!(!recipes[6].is_silent(), "echo should not be silent");
    }

    #[test]
    fn test_recipe_is_ignore_errors_various_prefixes() {
        let makefile: Makefile = r#"test:
	@echo silent
	-echo ignore
	+echo always
	@-echo silent_ignore
	-@echo ignore_silent
	+-echo always_ignore
	echo normal
"#
        .parse()
        .unwrap();

        let rule = makefile.rules().next().unwrap();
        let recipes: Vec<_> = rule.recipe_nodes().collect();

        assert_eq!(recipes.len(), 7);
        assert!(
            !recipes[0].is_ignore_errors(),
            "@echo should not ignore errors"
        );
        assert!(recipes[1].is_ignore_errors(), "-echo should ignore errors");
        assert!(
            !recipes[2].is_ignore_errors(),
            "+echo should not ignore errors"
        );
        assert!(recipes[3].is_ignore_errors(), "@-echo should ignore errors");
        assert!(recipes[4].is_ignore_errors(), "-@echo should ignore errors");
        assert!(recipes[5].is_ignore_errors(), "+-echo should ignore errors");
        assert!(
            !recipes[6].is_ignore_errors(),
            "echo should not ignore errors"
        );
    }

    #[test]
    fn test_recipe_set_prefix_add() {
        let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();

        recipe.set_prefix("@");
        assert_eq!(recipe.text(), "@echo hello");
        assert!(recipe.is_silent());
    }

    #[test]
    fn test_recipe_set_prefix_change() {
        let makefile: Makefile = "all:\n\t@echo hello\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();

        recipe.set_prefix("-");
        assert_eq!(recipe.text(), "-echo hello");
        assert!(!recipe.is_silent());
        assert!(recipe.is_ignore_errors());
    }

    #[test]
    fn test_recipe_set_prefix_remove() {
        let makefile: Makefile = "all:\n\t@-echo hello\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();

        recipe.set_prefix("");
        assert_eq!(recipe.text(), "echo hello");
        assert!(!recipe.is_silent());
        assert!(!recipe.is_ignore_errors());
    }

    #[test]
    fn test_recipe_set_prefix_combinations() {
        let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();

        recipe.set_prefix("@-");
        assert_eq!(recipe.text(), "@-echo hello");
        assert!(recipe.is_silent());
        assert!(recipe.is_ignore_errors());

        recipe.set_prefix("-@");
        assert_eq!(recipe.text(), "-@echo hello");
        assert!(recipe.is_silent());
        assert!(recipe.is_ignore_errors());
    }

    #[test]
    fn test_recipe_replace_text_basic() {
        let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();

        recipe.replace_text("echo world");
        assert_eq!(recipe.text(), "echo world");

        // Verify it's still accessible from the rule
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo world"]);
    }

    #[test]
    fn test_recipe_replace_text_with_prefix() {
        let makefile: Makefile = "all:\n\t@echo hello\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();

        recipe.replace_text("@echo goodbye");
        assert_eq!(recipe.text(), "@echo goodbye");
        assert!(recipe.is_silent());
    }

    #[test]
    fn test_recipe_multiple_operations() {
        let makefile: Makefile = "all:\n\techo one\n\techo two\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();

        // Replace text
        recipe.replace_text("echo modified");
        assert_eq!(recipe.text(), "echo modified");

        // Add prefix
        recipe.set_prefix("@");
        assert_eq!(recipe.text(), "@echo modified");

        // Insert after
        recipe.insert_after("echo three");

        // Verify all changes
        let rule = makefile.rules().next().unwrap();
        let recipes: Vec<_> = rule.recipes().collect();
        assert_eq!(recipes, vec!["@echo modified", "echo three", "echo two"]);
    }
}
