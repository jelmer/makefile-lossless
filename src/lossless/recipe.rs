use super::*;
use crate::ast::{
    line_ending, recipe_prefix_before, replace_children, replace_recipe_prefix,
    terminate_line_before,
};
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

/// A RECIPE node for the command `line` whose lines start with the recipe
/// prefix `prefix`, as [`build_recipe`].
pub(crate) fn build_command(
    prefix: char,
    line: &str,
    eol: &str,
    context: &str,
) -> Result<SyntaxNode, Error> {
    let recipe = build_recipe(tab(), line, eol, context)?;
    replace_recipe_prefix(&recipe, '\t', prefix);
    Ok(recipe)
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
        self.logical_text(false, None)
    }

    /// Get the text of this recipe line as GNU make hands it to the shell,
    /// before variable expansion.
    ///
    /// This is the line without its leading tab. Unlike [`Recipe::text`],
    /// lines starting with `#` are included: make does not treat `#` in a
    /// recipe as a comment, it passes it on to the shell. For lines split
    /// with backslash-newline, the backslash and newline are kept and the
    /// recipe prefix, a tab unless set with `.RECIPEPREFIX`, is removed from
    /// the start of each continuation line.
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
        self.logical_text(true, None)
    }

    /// The text of the line from `from`, or from its start, with line
    /// continuations as make passes them to the shell.
    fn logical_text(&self, include_comments: bool, from: Option<rowan::TextSize>) -> String {
        let mut after_newline = false;
        let mut prefix = None;
        let comment = self.comment_start();
        self.body_tokens()
            .filter_map(|t| {
                if !include_comments && comment.is_some_and(|c| t.text_range().start() >= c) {
                    return None;
                }
                if from.is_some_and(|from| t.text_range().start() < from) {
                    return None;
                }
                // Tokens in a reference are all text.
                let nested = t.parent().as_ref() != Some(self.syntax());
                match t.kind() {
                    NEWLINE => {
                        after_newline = true;
                        Some(lf_line_endings(t.text()))
                    }
                    // make strips the recipe prefix from continuation lines.
                    // In a reference it keeps it, but turns the line break
                    // and the whitespace after it into a space, so a tab
                    // goes either way.
                    INDENT if after_newline => {
                        after_newline = false;
                        let prefix = *prefix.get_or_insert_with(|| self.recipe_prefix());
                        let text = t.text();
                        let text = match text.strip_prefix(prefix) {
                            Some(rest) if !nested || prefix == '\t' => rest,
                            _ => text,
                        };
                        Some(text.to_string())
                    }
                    // In a recipe after `;` on the rule line, the parser
                    // leaves a prefix other than a tab in the text.
                    TEXT if after_newline && !nested && !self.starts_with_indent() => {
                        after_newline = false;
                        let prefix = *prefix.get_or_insert_with(|| self.recipe_prefix());
                        let text = t.text();
                        let text = match text.strip_prefix(prefix) {
                            Some(rest) if prefix != '\t' => rest,
                            _ => text,
                        };
                        Some(text.to_string())
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

    /// Whether this recipe starts with indentation, unlike one after `;` on
    /// the rule line.
    fn starts_with_indent(&self) -> bool {
        self.syntax()
            .first_token()
            .is_some_and(|t| t.kind() == INDENT)
    }

    /// The recipe prefix in effect for this recipe: the character that
    /// starts its first line, or for a recipe after `;` on the rule line,
    /// the one set with GNU make's `.RECIPEPREFIX` before it.
    fn recipe_prefix(&self) -> char {
        let node = self.syntax();
        match node.first_token().filter(|t| t.kind() == INDENT) {
            // TODO: Handle a `.RECIPEPREFIX` set to a space, which make
            // strips from continuation lines too.
            Some(indent) => indent
                .text()
                .chars()
                .next()
                .filter(|c| *c != ' ')
                .unwrap_or('\t'),
            None => node
                .parent()
                .map_or('\t', |parent| recipe_prefix_before(&parent, node.index())),
        }
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
    /// line contains a comment, or None if there is no comment. A comment
    /// ending in a backslash takes in the lines it is continued onto, except
    /// for nmake, with the recipe prefix removed from each as in
    /// [`Recipe::shell_text`].
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
        let start = self.comment_start()?;
        Some(self.logical_text(true, Some(start)))
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

    /// Whether `flag` is among the `@`, `-` and `+` characters at the start
    /// of the command, which make reads in any order.
    fn has_prefix_flag(&self, flag: char) -> bool {
        self.text()
            .chars()
            .take_while(|c| matches!(c, '@' | '-' | '+'))
            .any(|c| c == flag)
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
        self.has_prefix_flag('@')
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
        self.has_prefix_flag('-')
    }

    /// Set the command prefix for this recipe
    ///
    /// The prefix can contain `@` (silent), `-` (ignore errors), and/or `+` (always execute).
    /// Pass an empty string to remove all prefixes.
    ///
    /// # Panics
    ///
    /// Panics if `prefix` contains any other character. Use
    /// [`Recipe::try_set_prefix`] to get an error instead.
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
        self.try_set_prefix(prefix)
            .unwrap_or_else(|e| panic!("invalid recipe prefix: {e}"))
    }

    /// Set the command prefix for this recipe, like [`Recipe::set_prefix`]
    ///
    /// Returns an error, leaving the recipe unchanged, if `prefix` contains
    /// anything other than `@`, `-` and `+`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let mut makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// assert!(recipe.try_set_prefix("x").is_err());
    /// recipe.try_set_prefix("-@").unwrap();
    /// assert_eq!(recipe.text(), "-@echo hello");
    /// ```
    pub fn try_set_prefix(&mut self, prefix: &str) -> Result<(), Error> {
        // TODO: nmake's `!` and `-NUMBER` prefixes are not supported.
        if !prefix.chars().all(|c| matches!(c, '@' | '-' | '+')) {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: format!("{prefix:?} is not a recipe prefix"),
                    line: 1,
                    context: "set_prefix".to_string(),
                }],
            }));
        }
        const PREFIX_CHARS: [char; 3] = ['@', '-', '+'];
        let node = self.syntax();
        let skip = if self.is_inline() {
            self.inline_prefix().len()
        } else {
            usize::from(self.starts_with_indent())
        };
        // The tokens with just prefix characters at the start of the
        // command, and the token after them, if it is text.
        let mut prefix_tokens = vec![];
        let mut first_text = None;
        let mut insert_at = node.children_with_tokens().count();
        for element in node.children_with_tokens().skip(skip) {
            let Some(token) = element
                .as_token()
                .filter(|t| matches!(t.kind(), TEXT | COMMENT))
            else {
                insert_at = element.index();
                break;
            };
            if token.text().trim_start_matches(PREFIX_CHARS).is_empty() {
                prefix_tokens.push(token.clone());
            } else {
                first_text = Some(token.clone());
                break;
            }
        }
        // TODO: splice them out once rowan's splice_children removes more
        // than the first child of the range, as it does from 0.17 on.
        // A recipe line starting with `#` is a comment, and one starting
        // with a prefix character is text.
        let replace = |token: &SyntaxToken, text: &str| {
            let index = token.index();
            token.detach();
            if !text.is_empty() {
                let kind = if text.starts_with('#') { COMMENT } else { TEXT };
                node.splice_children(index..index, detached_elements(&[(kind, text)], None));
            }
        };
        match (first_text, prefix_tokens.split_first()) {
            (Some(token), _) => {
                for old in &prefix_tokens {
                    old.detach();
                }
                let rest = token.text().trim_start_matches(PREFIX_CHARS);
                let text = format!("{prefix}{rest}");
                if text != token.text() {
                    replace(&token, &text);
                }
            }
            (None, Some((first, others))) => {
                for old in others {
                    old.detach();
                }
                if first.text() != prefix {
                    replace(first, prefix);
                }
            }
            (None, None) if !prefix.is_empty() => {
                node.splice_children(
                    insert_at..insert_at,
                    detached_elements(&[(TEXT, prefix)], None),
                );
            }
            (None, None) => {}
        }
        Ok(())
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
        let indent = node
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == INDENT);
        let prefix: Vec<GreenElement> = if !inline_prefix.is_empty() {
            inline_prefix
                .iter()
                .map(|t| GreenToken::new(t.kind().into(), t.text()).into())
                .collect()
        } else if let Some(indent_token) = &indent {
            // Preserve the existing INDENT token
            vec![GreenToken::new(INDENT.into(), indent_token.text()).into()]
        } else {
            let prefix = recipe_prefix_before(&parent, node_index).to_string();
            vec![GreenToken::new(INDENT.into(), &prefix).into()]
        };

        // Preserve the existing NEWLINE token if present
        let eol = node
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == NEWLINE)
            .last()
            .map_or_else(|| line_ending(node), |t| t.text().to_string());

        let new_syntax = build_recipe(prefix, new_text, &eol, "replace_text")?;
        // Continuation lines start with the same recipe prefix as the first.
        let recipe_prefix = new_syntax
            .first_token()
            .filter(|t| t.kind() == INDENT)
            .and_then(|t| t.text().chars().next())
            .filter(|c| *c != ' ');
        if let Some(recipe_prefix) = recipe_prefix {
            replace_recipe_prefix(&new_syntax, '\t', recipe_prefix);
        }

        replace_children(
            node,
            new_syntax
                .green()
                .children()
                .map(|c| c.to_owned())
                .collect(),
        );
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
        let node = self.syntax();
        let prefix = recipe_prefix_before(
            &node.parent().expect("Recipe node must have a parent"),
            node.index(),
        );
        let new_syntax = build_command(prefix, text, &line_ending(node), "insert_before")?;
        // A recipe on the rule line has to move to its own line first.
        self.move_to_own_line();
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
        let prefix = recipe_prefix_before(&parent, node.index() + 1);
        let new_syntax = build_command(prefix, text, &eol, "insert_after")?;

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
            .find(|t| t.kind() == NEWLINE);
        let replacement: Vec<_> = newline.map(Into::into).into_iter().collect();
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

    /// Move this recipe to a line of its own if it is on the rule line.
    fn move_to_own_line(&self) {
        if !self.is_inline() {
            return;
        }
        let node = self.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");
        let inline_prefix = self.inline_prefix();
        self.trim_preceding_whitespace();

        let prefix = recipe_prefix_before(&parent, node.index()).to_string();
        let newline = line_ending(node);
        for token in inline_prefix {
            token.detach();
        }
        node.splice_children(0..0, detached_elements(&[(INDENT, &prefix)], None));
        let index = node.index();
        parent.splice_children(
            index..index,
            detached_elements(&[(NEWLINE, &newline)], None),
        );
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
    fn test_text_custom_recipe_prefix() {
        // make strips the recipe prefix, and only that, from the start of
        // each continuation line.
        let cases = [
            (
                ".RECIPEPREFIX = >\nall:\n>echo a \\\n>b \\\n>>c \\\n\td\n",
                "echo a \\\nb \\\n>c \\\n\td",
            ),
            (
                ".RECIPEPREFIX = >\nall: ; echo a \\\n>b \\\n\tc\n",
                "echo a \\\nb \\\n\tc",
            ),
            (
                ".RECIPEPREFIX = >\nall:\n>echo \"$(subst x,y,a\\\n>x)\"\n",
                "echo \"$(subst x,y,a\\\n>x)\"",
            ),
        ];
        for (text, expected) in cases {
            let makefile: Makefile = text.parse().unwrap();
            let recipe = makefile
                .rules()
                .next()
                .unwrap()
                .recipe_nodes()
                .next()
                .unwrap();
            assert_eq!(recipe.text(), expected, "{text:?}");
            assert_eq!(recipe.shell_text(), expected, "{text:?}");
        }

        let makefile: Makefile = ".RECIPEPREFIX = >\nall:\n># a \\\n>b\n".parse().unwrap();
        let recipe = makefile
            .rules()
            .next()
            .unwrap()
            .recipe_nodes()
            .next()
            .unwrap();
        assert_eq!(recipe.text(), "");
        assert_eq!(recipe.shell_text(), "# a \\\nb");
        assert_eq!(recipe.comment(), Some("# a \\\nb".to_string()));
    }

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

    fn parse_variant(text: &str, variant: Option<crate::MakefileVariant>) -> Makefile {
        let makefile = match variant {
            None => Makefile::parse(text),
            Some(variant) => Makefile::parse_with_variant(text, variant),
        }
        .tree();
        assert_eq!(makefile.to_string(), text);
        makefile
    }

    #[test]
    fn test_comment_line_continuation() {
        // GNU and BSD make continue a line starting with `#` like any other
        // recipe line. GNU make passes the lines to the shell together, BSD
        // make skips them all.
        use crate::MakefileVariant::*;
        let text = "all:\n\t# a \\\n\techo $(X)\n\t# b \\\nc: d\n\t# e \\\\\n\techo x\n";
        for variant in [None, Some(GNUMake), Some(BSDMake), Some(POSIXMake)] {
            let makefile = parse_variant(text, variant);
            assert_eq!(makefile.rules().count(), 1, "{variant:?}");
            let recipes: Vec<_> = makefile.rules().flat_map(|r| r.recipe_nodes()).collect();
            let accessors: Vec<_> = recipes
                .iter()
                .map(|r| (r.text(), r.comment(), r.shell_text()))
                .collect();
            let comment = |c: &str| (String::new(), Some(c.to_string()), c.to_string());
            assert_eq!(
                accessors,
                vec![
                    comment("# a \\\necho $(X)"),
                    comment("# b \\\nc: d"),
                    comment("# e \\\\"),
                    ("echo x".to_string(), None, "echo x".to_string()),
                ],
                "{variant:?}"
            );
            let references: Vec<_> = recipes[0].references().map(|r| r.to_string()).collect();
            let expected: &[&str] = if variant == Some(BSDMake) {
                &[]
            } else {
                &["$(X)"]
            };
            assert_eq!(references, expected, "{variant:?}");
            assert_eq!(
                makefile.comment_ranges().collect::<Vec<_>>(),
                vec![
                    rowan::TextRange::new(6.into(), 22.into()),
                    rowan::TextRange::new(24.into(), 34.into()),
                    rowan::TextRange::new(36.into(), 42.into()),
                ],
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_comment_line_continuation_nmake() {
        // nmake ends a comment at the end of the line.
        let makefile = parse_variant(
            "all:\n\t# a \\\n\techo x\n",
            Some(crate::MakefileVariant::NMake),
        );
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["", "echo x"]);
    }

    #[test]
    fn test_comment_after_continuation() {
        // A line starting with `#` that continues a command is part of the
        // command, which GNU make passes to the shell with the `#` line in it
        // and BSD make joins into one line.
        use crate::MakefileVariant::*;
        let text = "all:\n\techo a \\\n\t# b $(X) \\\n\techo c\n\techo d\n";
        for variant in [None, Some(GNUMake), Some(BSDMake), Some(POSIXMake)] {
            let makefile = parse_variant(text, variant);
            let recipes: Vec<_> = makefile.rules().flat_map(|r| r.recipe_nodes()).collect();
            let accessors: Vec<_> = recipes
                .iter()
                .map(|r| (r.text(), r.comment(), r.shell_text()))
                .collect();
            assert_eq!(
                accessors,
                vec![
                    (
                        "echo a \\\n# b $(X) \\\necho c".to_string(),
                        None,
                        "echo a \\\n# b $(X) \\\necho c".to_string()
                    ),
                    ("echo d".to_string(), None, "echo d".to_string()),
                ],
                "{variant:?}"
            );
            let rule = makefile.rules().next().unwrap();
            assert_eq!(
                rule.recipes().collect::<Vec<_>>(),
                vec!["echo a \\\n# b $(X) \\\necho c", "echo d"],
                "{variant:?}"
            );
            assert_eq!(makefile.comment_ranges().count(), 0, "{variant:?}");
            let references: Vec<_> = recipes[0].references().map(|r| r.to_string()).collect();
            assert_eq!(references, vec!["$(X)"], "{variant:?}");
        }
    }

    #[test]
    fn test_inline_comment_continuation() {
        use crate::MakefileVariant::*;
        for variant in [None, Some(GNUMake), Some(BSDMake)] {
            let makefile = parse_variant("a: ; # x \\\n\techo $(Y)\nb:\n", variant);
            let recipes: Vec<_> = makefile.rules().flat_map(|r| r.recipe_nodes()).collect();
            assert_eq!(recipes.len(), 1);
            assert_eq!(recipes[0].comment(), Some("# x \\\necho $(Y)".to_string()));
            assert_eq!(recipes[0].text(), "");
            assert_eq!(
                recipes[0].references().count(),
                usize::from(variant != Some(BSDMake)),
                "{variant:?}"
            );
            assert_eq!(makefile.comment_ranges().count(), 1);
        }
    }

    #[test]
    fn test_recipe_prefix_flags_after_two_others() {
        let makefile: Makefile = "all:\n\t+-@echo a\n\t@+-false\n\t+@echo b\n"
            .parse()
            .unwrap();
        let rule = makefile.rules().next().unwrap();
        let flags: Vec<_> = rule
            .recipe_nodes()
            .map(|r| (r.is_silent(), r.is_ignore_errors()))
            .collect();
        assert_eq!(flags, vec![(true, true), (true, true), (true, false)]);
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
    fn test_recipe_try_set_prefix_rejects_invalid() {
        let makefile: Makefile = "all:\n\t@echo hello\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();

        for prefix in ["x", "@x", " ", "@ ", "\n", "!", "\\"] {
            assert!(recipe.try_set_prefix(prefix).is_err(), "{prefix:?}");
            assert_eq!(recipe.text(), "@echo hello");
        }
        recipe.try_set_prefix("+-@").unwrap();
        assert_eq!(recipe.text(), "+-@echo hello");
    }

    #[test]
    #[should_panic(expected = "invalid recipe prefix")]
    fn test_recipe_set_prefix_panics_on_invalid() {
        let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();
        recipe.set_prefix("x");
    }

    #[test]
    fn test_recipe_set_prefix_unusual_formatting() {
        let cases = [
            ("all:\n\t@-echo  hi\t# c\n", "+", "all:\n\t+echo  hi\t# c\n"),
            (
                "all:\n\techo a \\\n\t  b # c\n",
                "@",
                "all:\n\t@echo a \\\n\t  b # c\n",
            ),
            ("all:\n\t@$(X) y\n", "-", "all:\n\t-$(X) y\n"),
            ("all:\n\t$(X) y\n", "@", "all:\n\t@$(X) y\n"),
            ("all:\n\t+$(X) y\n", "", "all:\n\t$(X) y\n"),
            ("all:\n\t@\n", "-", "all:\n\t-\n"),
            ("all:\n\t@\n", "", "all:\n\t\n"),
            ("all:  ;\t@echo x # c\n", "-@", "all:  ;\t-@echo x # c\n"),
            ("all: ;echo x\n", "@", "all: ;@echo x\n"),
            (
                ".RECIPEPREFIX = >\nall:\n>@echo x\n",
                "-",
                ".RECIPEPREFIX = >\nall:\n>-echo x\n",
            ),
        ];
        for (code, prefix, expected) in cases {
            let makefile: Makefile = code.parse().unwrap();
            let rule = makefile.rules().next().unwrap();
            let mut recipe = rule.recipe_nodes().next().unwrap();
            let text = recipe.text();
            recipe.try_set_prefix(prefix).unwrap();
            assert_eq!(makefile.to_string(), expected, "{code:?}");
            assert_eq!(
                recipe.text(),
                format!("{prefix}{}", text.trim_start_matches(['@', '-', '+'])),
                "{code:?}"
            );
            crate::test_util::assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_recipe_set_prefix_keeps_other_tokens() {
        let makefile: Makefile = "all:\n\t@echo $(X) # c\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();
        let node = recipe.syntax().clone();
        let children: Vec<_> = node.children_with_tokens().collect();
        recipe.set_prefix("-");
        assert_eq!(makefile.to_string(), "all:\n\t-echo $(X) # c\n");
        assert_eq!(recipe.syntax(), &node);
        assert_eq!(node.parent(), Some(rule.syntax().clone()));
        let after: Vec<_> = node.children_with_tokens().collect();
        assert_eq!(after.len(), children.len());
        for (i, (before, after)) in children.iter().zip(&after).enumerate() {
            if i != 1 {
                assert_eq!(before, after);
            }
        }
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

    /// The tokens of `recipe`, with the RECIPE node they are in.
    fn tokens_in(recipe: &Recipe) -> Vec<(SyntaxToken, SyntaxNode)> {
        recipe
            .syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .map(|t| (t, recipe.syntax().clone()))
            .collect()
    }

    /// Whether `token` is still in `makefile`, in the RECIPE node `node`.
    fn is_kept(makefile: &Makefile, token: &SyntaxToken, node: &SyntaxNode) -> bool {
        token
            .parent_ancestors()
            .find(|n| n.kind() == RECIPE)
            .as_ref()
            == Some(node)
            && token.parent_ancestors().last().as_ref() == Some(makefile.syntax())
    }

    #[test]
    fn test_replace_text_keeps_recipe_node() {
        let makefile: Makefile = "all:\n\t  echo a \\\n\t  b\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();
        let other = rule.recipe_nodes().next().unwrap();
        let tokens = tokens_in(&recipe);
        recipe.try_replace_text("  echo a \\\n\t  c").unwrap();
        assert_eq!(makefile.code(), "all:\n\t  echo a \\\n\t  c\n");
        assert_eq!(other.text(), "  echo a \\\n  c");
        assert_eq!(recipe.syntax(), other.syntax());
        // Only the last line's text changes.
        let kept: Vec<_> = tokens
            .iter()
            .filter(|(t, node)| is_kept(&makefile, t, node))
            .map(|(t, _)| t.text().to_string())
            .collect();
        assert_eq!(kept, vec!["\t", "  echo a \\", "\n", "\t", "\n"]);
        crate::test_util::assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_set_prefix_keeps_rest_of_recipe() {
        let makefile: Makefile = "all:\n\t@$(CC) -o $@ \\\n\t  x.c # c\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();
        let tokens = tokens_in(&recipe);
        recipe.set_prefix("-");
        assert_eq!(makefile.code(), "all:\n\t-$(CC) -o $@ \\\n\t  x.c # c\n");
        let replaced: Vec<_> = tokens
            .iter()
            .filter(|(t, node)| !is_kept(&makefile, t, node))
            .map(|(t, _)| t.text().to_string())
            .collect();
        assert_eq!(replaced, vec!["@"]);
        crate::test_util::assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_replace_command_keeps_recipe_node() {
        let makefile: Makefile = "all:\n\techo a\n\techo b\n".parse().unwrap();
        let mut rule = makefile.rules().next().unwrap();
        let recipe = rule.recipe_nodes().next().unwrap();
        assert!(rule.try_replace_command(0, "echo c").unwrap());
        assert_eq!(makefile.code(), "all:\n\techo c\n\techo b\n");
        assert_eq!(recipe.text(), "echo c");
        crate::test_util::assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_insert_before_inline_recipe_keeps_recipe_node() {
        let makefile: Makefile = "all: b ;  echo $(X)  # c\nZ = 1\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let recipe = rule.recipe_nodes().next().unwrap();
        let tokens = tokens_in(&recipe);
        recipe.try_insert_before("echo y").unwrap();
        assert_eq!(
            makefile.code(),
            "all: b\n\techo y\n\techo $(X)  # c\nZ = 1\n"
        );
        assert_eq!(recipe.text(), "echo $(X)  # c");
        let kept: Vec<_> = tokens
            .iter()
            .filter(|(t, node)| is_kept(&makefile, t, node))
            .map(|(t, _)| t.text().to_string())
            .collect();
        assert_eq!(kept, vec!["echo ", "$", "(", "X", ")", "  # c", "\n"]);
        crate::test_util::assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_remove_inline_recipe_keeps_line_break() {
        let makefile: Makefile = "all: b ; echo x\r\nZ = 1\r\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        let recipe = rule.recipe_nodes().next().unwrap();
        let newline = recipe.syntax().last_token().unwrap();
        recipe.remove();
        assert_eq!(makefile.code(), "all: b\r\nZ = 1\r\n");
        assert_eq!(newline.parent().as_ref(), Some(rule.syntax()));
        crate::test_util::assert_matches_reparse(&makefile);
    }

    #[test]
    fn test_set_prefix_comment_line() {
        for (text, prefix, expected) in [
            ("all:\n\t-# note\n", "", "all:\n\t# note\n"),
            ("all:\n\t@-# note\n", "", "all:\n\t# note\n"),
            ("all:\n\t-# note\n", "@", "all:\n\t@# note\n"),
        ] {
            let makefile: Makefile = text.parse().unwrap();
            let mut recipe = makefile
                .rules()
                .next()
                .unwrap()
                .recipe_nodes()
                .next()
                .unwrap();
            recipe.set_prefix(prefix);
            assert_eq!(makefile.code(), expected);
            crate::test_util::assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_set_prefix_keeps_continuation_lines() {
        let cases = [
            ("all:\n\t@echo a \\\n\t  b\n", "all:\n\t-echo a \\\n\t  b\n"),
            (
                ".RECIPEPREFIX = >\nall:\n>@echo a \\\n>  b\n",
                ".RECIPEPREFIX = >\nall:\n>-echo a \\\n>  b\n",
            ),
            ("all: ; @echo a \\\n\t  b\n", "all: ; -echo a \\\n\t  b\n"),
            ("all:\n\t# note\n", "all:\n\t-# note\n"),
        ];
        for (text, expected) in cases {
            let makefile: Makefile = text.parse().unwrap();
            let mut recipe = makefile
                .rules()
                .next()
                .unwrap()
                .recipe_nodes()
                .next()
                .unwrap();
            recipe.set_prefix("-");
            assert_eq!(makefile.code(), expected);
            crate::test_util::assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_recipe_edits_in_makefile_with_errors() {
        let parsed = Makefile::parse("all: ; @echo a\n\techo b\nifdef X\nY = 1\n");
        assert!(!parsed.ok());
        let makefile = parsed.tree();
        let mut rule = makefile.rules().next().unwrap();
        let mut recipes: Vec<_> = rule.recipe_nodes().collect();
        recipes[0].set_prefix("");
        recipes[0].try_insert_before("echo c").unwrap();
        assert!(rule.try_replace_command(2, "echo d").unwrap());
        assert_eq!(
            makefile.code(),
            "all:\n\techo c\n\techo a\n\techo d\nifdef X\nY = 1\n"
        );
        assert_eq!(recipes[1].text(), "echo d");
        let reparsed = Makefile::parse(&makefile.code()).tree();
        assert_eq!(
            format!("{:#?}", makefile.syntax()),
            format!("{:#?}", reparsed.syntax())
        );
    }
}
