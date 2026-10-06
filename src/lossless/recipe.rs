use super::*;
use crate::ast::{line_ending, terminate_line_before};

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
        let tokens: Vec<_> = self
            .syntax()
            .children_with_tokens()
            .filter_map(|it| it.as_token().cloned())
            .collect();

        if tokens.is_empty() {
            return String::new();
        }

        // Skip the first token if it's the leading INDENT
        let start = if tokens.first().map(|t| t.kind()) == Some(INDENT) {
            1
        } else {
            0
        };

        // Skip the last token if it's the trailing NEWLINE
        let end = if tokens.last().map(|t| t.kind()) == Some(NEWLINE) {
            tokens.len() - 1
        } else {
            tokens.len()
        };

        // For INDENT tokens after a continuation newline, strip the leading tab character.
        let mut after_newline = false;
        tokens[start..end]
            .iter()
            .filter_map(|t| match t.kind() {
                TEXT => {
                    after_newline = false;
                    Some(t.text().to_string())
                }
                COMMENT if include_comments => {
                    after_newline = false;
                    Some(t.text().to_string())
                }
                NEWLINE => {
                    after_newline = true;
                    Some(lf_line_endings(t.text()))
                }
                INDENT if after_newline => {
                    after_newline = false;
                    // Strip the leading tab from continuation-line indentation
                    let text = t.text();
                    Some(text.strip_prefix('\t').unwrap_or(text).to_string())
                }
                _ => None,
            })
            .collect()
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
        self.syntax()
            .children_with_tokens()
            .filter_map(|it| {
                if let Some(token) = it.as_token() {
                    if token.kind() == COMMENT {
                        return Some(token.text().to_string());
                    }
                }
                None
            })
            .next()
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
            .children_with_tokens()
            .filter_map(|it| {
                if let Some(token) = it.as_token() {
                    // Include TEXT and COMMENT tokens, but skip INDENT and NEWLINE
                    if token.kind() == TEXT || token.kind() == COMMENT {
                        return Some(token.text().to_string());
                    }
                }
                None
            })
            .collect::<Vec<_>>()
            .join("")
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

    /// Get the source range of this recipe node.
    pub fn text_range(&self) -> rowan::TextRange {
        self.syntax().text_range()
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
        let node = self.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");
        let node_index = node.index();

        // Build a new RECIPE node with the new text
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());

        let inline_prefix = self.inline_prefix();
        if !inline_prefix.is_empty() {
            for token in &inline_prefix {
                builder.token(token.kind().into(), token.text());
            }
        } else if let Some(indent_token) = node
            .children_with_tokens()
            .find(|it| it.as_token().map(|t| t.kind() == INDENT).unwrap_or(false))
        {
            // Preserve the existing INDENT token
            builder.token(INDENT.into(), indent_token.as_token().unwrap().text());
        } else {
            builder.token(INDENT.into(), "\t");
        }

        builder.token(TEXT.into(), new_text);

        // Preserve the existing NEWLINE token if present
        if let Some(newline_token) = node
            .children_with_tokens()
            .find(|it| it.as_token().map(|t| t.kind() == NEWLINE).unwrap_or(false))
        {
            builder.token(NEWLINE.into(), newline_token.as_token().unwrap().text());
        } else {
            builder.token(NEWLINE.into(), &line_ending(node));
        }

        builder.finish_node();
        let new_syntax = SyntaxNode::new_root_mut(builder.finish());

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
    pub fn insert_before(&self, text: &str) {
        // A recipe on the rule line has to move to its own line first.
        let this = self.move_to_own_line().unwrap_or_else(|| self.clone());
        let node = this.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");
        let node_index = node.index();

        // Build a new RECIPE node
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), text);
        builder.token(NEWLINE.into(), &line_ending(node));
        builder.finish_node();
        let new_syntax = SyntaxNode::new_root_mut(builder.finish());

        // Insert before this recipe
        parent.splice_children(node_index..node_index, vec![new_syntax.into()]);
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
    pub fn insert_after(&self, text: &str) {
        let node = self.syntax();
        let parent = node.parent().expect("Recipe node must have a parent");
        let eol = line_ending(node);

        // Build a new RECIPE node
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), text);
        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();
        let new_syntax = SyntaxNode::new_root_mut(builder.finish());

        // Insert after this recipe
        let index = terminate_line_before(&parent, node.index() + 1, &eol);
        parent.splice_children(index..index, vec![new_syntax.into()]);
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
            .filter_map(|it| it.into_token())
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

        let body: Vec<(SyntaxKind, String)> = node
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .skip(skip)
            .map(|t| (t.kind(), t.text().to_string()))
            .collect();
        let newline = line_ending(node);
        let mut recipe = vec![(INDENT, "\t")];
        recipe.extend(body.iter().map(|(kind, text)| (*kind, text.as_str())));
        let elements = detached_elements(&[(NEWLINE, &newline)], Some(&recipe));

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
    /// Recipe bodies are stored as raw text, so [`Makefile::variable_references`]
    /// does not descend into them. This method scans the recipe's text directly
    /// and yields each reference with its absolute source range.
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
    pub fn variable_references(&self) -> Vec<RecipeVariableReference> {
        let mut out = Vec::new();
        for token in self
            .syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == TEXT)
        {
            let base: u32 = token.text_range().start().into();
            scan_recipe_variable_refs(token.text(), base, &mut out);
        }
        out
    }
}

/// A `$(VAR)` or `${VAR}` reference found inside a recipe or `define` body.
///
/// Recipes and `define` bodies are stored as raw text, so these references
/// have no backing syntax node; this type carries just the variable name and
/// its absolute source range.
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
