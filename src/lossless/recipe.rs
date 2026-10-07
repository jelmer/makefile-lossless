use super::*;
use crate::ast::{
    detach_elements, line_ending, recipe_prefix_before, replace_children, replace_range,
    terminate_line_before,
};
use rowan::{GreenNode, GreenToken};

type GreenElement = rowan::NodeOrToken<GreenNode, GreenToken>;

/// The RECIPE node holding the command `line` as the parser reads it
/// where the recipe prefix is `prefix`: after `;` on the rule line if
/// `inline`, and otherwise on a line of its own.
///
/// Returns an error if `line` can not be written as a single recipe line:
/// if it contains a newline outside of a line continuation, or ends in a
/// line continuation that would join it with the next line. Other parse
/// errors in it are left for the caller to check, and `true` returned with
/// the node if there are any.
fn parse_recipe_line(
    line: &str,
    prefix: char,
    inline: bool,
    context: &str,
) -> Result<(SyntaxNode, bool), Error> {
    let header = if prefix == '\t' {
        String::new()
    } else {
        format!("define .RECIPEPREFIX\n{prefix}\nendef\n")
    };
    let start = if inline {
        String::from(": ;")
    } else {
        format!(":\n{prefix}")
    };
    let parsed = parse(&format!("{header}x{start}{line}\n{prefix}z\n"), None);
    let mut rules = parsed
        .root()
        .syntax()
        .children()
        .filter(|n| n.kind() != VARIABLE);
    let recipes: Vec<_> = rules
        .next()
        .filter(|rule| rule.kind() == RULE && rules.next().is_none())
        .into_iter()
        .flat_map(|rule| rule.children().filter(|n| n.kind() == RECIPE))
        .collect();
    let [recipe, last] = recipes.as_slice() else {
        return Err(recipe_line_error(line, context));
    };
    let first = if inline { ";" } else { &start[2..] };
    if recipe.text() != format!("{first}{line}\n").as_str()
        || last.text() != format!("{prefix}z\n").as_str()
    {
        return Err(recipe_line_error(line, context));
    }
    Ok((recipe.clone(), !parsed.errors.is_empty()))
}

/// The text of `recipe`, whose continuation lines start with the recipe
/// prefix `old`, without the prefix of its first line or the `;` before a
/// recipe on a rule line, and without its final line ending, written for
/// the recipe prefix `new` so that make reads the same command: the prefix
/// of each continuation line becomes `new`, and one that starts with `new`
/// without the prefix gets another `new`, for make to strip. Line breaks
/// inside references are left alone, since make keeps the recipe prefix
/// there and takes a tab as whitespace.
fn text_for_prefix(recipe: &SyntaxNode, old: char, new: char) -> String {
    let mut text = String::new();
    let mut line_start = false;
    for (i, element) in recipe.children_with_tokens().enumerate() {
        let element_text = element.to_string();
        match element.kind() {
            INDENT if i == 0 => {
                text.push_str(element_text.strip_prefix(old).unwrap_or(&element_text))
            }
            OPERATOR if i == 0 => {}
            _ if line_start && element_text.starts_with(old) => {
                text.push(new);
                text.push_str(&element_text[old.len_utf8()..]);
            }
            _ if line_start && element_text.starts_with(new) => {
                text.push(new);
                text.push_str(&element_text);
            }
            _ => text.push_str(&element_text),
        }
        line_start = element.kind() == NEWLINE;
    }
    if let Some(eol) = recipe.last_token().filter(|t| t.kind() == NEWLINE) {
        text.truncate(text.len() - eol.text().len());
    }
    text
}

/// Rewrite `recipe`, whose lines start with the recipe prefix `old`, for
/// the recipe prefix `new`, as described for [`text_for_prefix`].
pub(crate) fn change_recipe_prefix(recipe: &SyntaxNode, old: char, new: char) {
    if old == new {
        return;
    }
    let inline = recipe.first_token().is_some_and(|t| t.kind() == OPERATOR);
    let text = text_for_prefix(recipe, old, new);
    let (parsed, _) = parse_recipe_line(&text, new, inline, "change_recipe_prefix")
        .expect("a recipe line reads the same with another recipe prefix");
    let mut children: Vec<GreenElement> = parsed.green().children().map(|c| c.to_owned()).collect();
    children.pop();
    if let Some(eol) = recipe.last_token().filter(|t| t.kind() == NEWLINE) {
        children.push(GreenToken::new(NEWLINE.into(), eol.text()).into());
    }
    replace_children(recipe, children);
}

/// The elements of a recipe line holding the command `line`, between its
/// indentation or the `;` before it and its line ending, as the parser reads
/// them where the recipe prefix is `prefix`.
///
/// `line` is written as for a tab as the recipe prefix: a tab at the start
/// of a continuation line is the recipe prefix, which make strips, and any
/// other text there is part of the command. With another recipe prefix, it
/// is rewritten as described for [`text_for_prefix`].
fn recipe_line_content(
    line: &str,
    prefix: char,
    inline: bool,
    context: &str,
) -> Result<Vec<GreenElement>, Error> {
    let (mut recipe, errors) = parse_recipe_line(line, '\t', false, context)?;
    if errors {
        return Err(recipe_line_error(line, context));
    }
    if prefix != '\t' || inline {
        let text = text_for_prefix(&recipe, '\t', prefix);
        (recipe, _) = parse_recipe_line(&text, prefix, inline, context)?;
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

/// A RECIPE node for the command `line`, starting with `start`, the
/// indentation or the `;` and whitespace of a recipe on the rule line, and
/// ending with the line ending `eol`, where the recipe prefix is `prefix`.
/// See [`recipe_line_content`] for how `line` is written.
fn build_recipe(
    start: Vec<GreenElement>,
    prefix: char,
    line: &str,
    eol: &str,
    context: &str,
) -> Result<SyntaxNode, Error> {
    let inline = start.first().is_some_and(|it| it.kind() == OPERATOR.into());
    let mut children = start;
    children.extend(recipe_line_content(line, prefix, inline, context)?);
    children.push(GreenToken::new(NEWLINE.into(), eol).into());
    Ok(SyntaxNode::new_root_mut(GreenNode::new(
        RECIPE.into(),
        children,
    )))
}

/// A RECIPE node for the command `line` on a line of its own, where the
/// recipe prefix is `prefix`, as [`build_recipe`].
pub(crate) fn build_command(
    prefix: char,
    line: &str,
    eol: &str,
    context: &str,
) -> Result<SyntaxNode, Error> {
    let indent = vec![GreenToken::new(INDENT.into(), &prefix.to_string()).into()];
    build_recipe(indent, prefix, line, eol, context)
}

/// The rest of `text` after the nmake command modifiers at its start: `@`,
/// `!` and `-` with an optional number, which may be separated by spaces
/// or tabs.
fn strip_nmake_modifiers(text: &str) -> &str {
    let mut rest = text;
    loop {
        let modifier = rest.trim_start_matches(BLANKS);
        rest = match modifier.chars().next() {
            Some('@' | '!') => &modifier[1..],
            Some('-') => modifier[1..].trim_start_matches(|c: char| c.is_ascii_digit()),
            _ => return rest,
        };
    }
}

const PREFIX_CHARS: [char; 3] = ['@', '-', '+'];
const BLANKS: [char; 2] = [' ', '\t'];

/// The rest of `text` after the command modifiers at its start, as
/// `variant` reads them, keeping the whitespace after the last one.
///
/// GNU make reads `@`, `-` and `+` with spaces or tabs before and between
/// them. BSD make allows spaces or tabs only before them. Without a variant
/// GNU make's modifiers are used, which include BSD make's.
fn strip_modifiers(text: &str, variant: Option<crate::MakefileVariant>) -> &str {
    match variant {
        Some(crate::MakefileVariant::NMake) => strip_nmake_modifiers(text),
        Some(crate::MakefileVariant::BSDMake) => {
            let after = text.trim_start_matches(BLANKS);
            let rest = after.trim_start_matches(PREFIX_CHARS);
            if rest.len() == after.len() {
                text
            } else {
                rest
            }
        }
        _ => {
            let run = text.trim_start_matches(|c| PREFIX_CHARS.contains(&c) || BLANKS.contains(&c));
            let modifiers = text[..text.len() - run.len()].trim_end_matches(BLANKS);
            &text[modifiers.len()..]
        }
    }
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
                    TEXT | COMMENT
                        if after_newline
                            && !nested
                            && !self.starts_with_indent()
                            && (t.kind() == TEXT || include_comments) =>
                    {
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
        let prefix_before = || {
            node.parent()
                .map_or('\t', |parent| recipe_prefix_before(&parent, node.index()))
        };
        match node
            .first_token()
            .filter(|t| t.kind() == INDENT)
            .and_then(|t| t.text().chars().next())
        {
            // A line indented with spaces is a recipe line in some makes, so
            // the space is only the prefix if `.RECIPEPREFIX` says so.
            Some(' ') if prefix_before() == ' ' => ' ',
            Some(' ') => '\t',
            Some(c) => c,
            None => prefix_before(),
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

    /// Whether `flag` is among the command modifiers at the start of the
    /// command, as `variant` reads them, which make reads in any order.
    fn has_prefix_flag(&self, flag: char, variant: Option<crate::MakefileVariant>) -> bool {
        let text = self.text();
        let rest = strip_modifiers(&text, variant);
        text[..text.len() - rest.len()].contains(flag)
    }

    /// Check if this recipe has the silent prefix (@)
    ///
    /// This follows GNU make, which also reads modifiers after spaces or
    /// tabs, as in `- @echo`; see [`Recipe::is_silent_for`] for other
    /// variants.
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
        self.has_prefix_flag('@', None)
    }

    /// Check if this recipe has the silent prefix (@), as `variant` reads
    /// the command modifiers
    ///
    /// GNU make reads modifiers separated by spaces or tabs, BSD make only
    /// reads them before any, and nmake also has `!` and `-NUMBER`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    ///
    /// let makefile: Makefile = "all:\n\t- @echo hello\n".parse().unwrap();
    /// let recipe = makefile.rules().next().unwrap().recipe_nodes().next().unwrap();
    /// assert!(recipe.is_silent_for(MakefileVariant::GNUMake));
    /// assert!(!recipe.is_silent_for(MakefileVariant::BSDMake));
    /// ```
    pub fn is_silent_for(&self, variant: crate::MakefileVariant) -> bool {
        self.has_prefix_flag('@', Some(variant))
    }

    /// Check if this recipe has the ignore-errors prefix (-)
    ///
    /// This follows GNU make, which also reads modifiers after spaces or
    /// tabs, as in `@ -false`; see [`Recipe::is_ignore_errors_for`] for
    /// other variants.
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
        self.has_prefix_flag('-', None)
    }

    /// Check if this recipe has the ignore-errors prefix (-), as `variant`
    /// reads the command modifiers, like [`Recipe::is_silent_for`]
    ///
    /// For nmake, `-NUMBER` counts too.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    ///
    /// let makefile: Makefile = "all:\n\t@ -false\n".parse().unwrap();
    /// let recipe = makefile.rules().next().unwrap().recipe_nodes().next().unwrap();
    /// assert!(recipe.is_ignore_errors_for(MakefileVariant::GNUMake));
    /// assert!(!recipe.is_ignore_errors_for(MakefileVariant::BSDMake));
    /// ```
    pub fn is_ignore_errors_for(&self, variant: crate::MakefileVariant) -> bool {
        self.has_prefix_flag('-', Some(variant))
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
        // TODO: accept nmake's command modifiers and reject `+` once the
        // tree records the variant it was parsed as. Until then,
        // try_set_prefix_for does.
        self.set_prefix_with(prefix, None)
    }

    /// Set the command prefix for this recipe, like [`Recipe::set_prefix`],
    /// with the command modifiers that `variant` has.
    ///
    /// GNU, POSIX and BSD make have `@`, `-` and `+`. nmake has `@`
    /// (silent), `!` (run for each dependent file) and `-` (ignore
    /// errors), which may be followed by a number to only ignore exit
    /// codes up to it, and may separate them with spaces or tabs; it has no
    /// `+`. A number has to be followed by a space or tab before the
    /// command.
    ///
    /// # Panics
    ///
    /// Panics if `variant` does not read `prefix` back as the command
    /// modifiers, as described for [`Recipe::try_set_prefix_for`], which
    /// returns an error instead.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    ///
    /// let makefile = Makefile::parse_with_variant("all:\n\t@echo hello\n", MakefileVariant::NMake).tree();
    /// let rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// recipe.set_prefix_for("-2 !", MakefileVariant::NMake);
    /// assert_eq!(makefile.code(), "all:\n\t-2 !echo hello\n");
    /// ```
    pub fn set_prefix_for(&mut self, prefix: &str, variant: crate::MakefileVariant) {
        self.try_set_prefix_for(prefix, variant)
            .unwrap_or_else(|e| panic!("invalid recipe prefix: {e}"))
    }

    /// Set the command prefix for this recipe, like
    /// [`Recipe::set_prefix_for`]
    ///
    /// Returns an error, leaving the recipe unchanged, if `prefix` contains
    /// anything other than the command modifiers of `variant`, or for
    /// nmake, whitespace between them. For nmake, also returns an error if
    /// the command would be read as part of the modifiers, as with `-` and
    /// a command starting with a digit, or if a number is not followed by a
    /// space or tab.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    ///
    /// let makefile = Makefile::parse_with_variant("all:\n\techo hello\n", MakefileVariant::NMake).tree();
    /// let rule = makefile.rules().next().unwrap();
    /// let mut recipe = rule.recipe_nodes().next().unwrap();
    /// assert!(recipe.try_set_prefix_for("+", MakefileVariant::NMake).is_err());
    /// assert!(recipe.try_set_prefix_for("-1", MakefileVariant::NMake).is_err());
    /// recipe.try_set_prefix_for("-1 ", MakefileVariant::NMake).unwrap();
    /// assert_eq!(makefile.code(), "all:\n\t-1 echo hello\n");
    /// ```
    pub fn try_set_prefix_for(
        &mut self,
        prefix: &str,
        variant: crate::MakefileVariant,
    ) -> Result<(), Error> {
        self.set_prefix_with(prefix, Some(variant))
    }

    /// Internal: set the command prefix, with the command modifiers of
    /// `variant`, or of GNU make without one.
    fn set_prefix_with(
        &mut self,
        prefix: &str,
        variant: Option<crate::MakefileVariant>,
    ) -> Result<(), Error> {
        let error = |message: String| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message,
                    line: 1,
                    context: "set_prefix".to_string(),
                }],
            })
        };
        let strip = |text: &str| strip_modifiers(text, variant).to_string();
        // Without a variant, only write modifiers that GNU and BSD make
        // both read.
        let valid = match variant {
            None | Some(crate::MakefileVariant::BSDMake) => {
                prefix.chars().all(|c| PREFIX_CHARS.contains(&c))
            }
            _ => strip(prefix).trim_start_matches(BLANKS).is_empty(),
        };
        if !valid {
            let message = match variant {
                Some(variant) => format!("{prefix:?} is not a recipe prefix in {variant:?}"),
                None => format!("{prefix:?} is not a recipe prefix"),
            };
            return Err(error(message));
        }
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
            if strip(token.text()).is_empty() {
                prefix_tokens.push(token.clone());
            } else {
                first_text = Some(token.clone());
                break;
            }
        }
        // nmake reads digits after `-` as part of the modifier, and needs a
        // space or tab after them.
        let rest = first_text
            .as_ref()
            .map(|t| strip(t.text()))
            .unwrap_or_default();
        let followed = node
            .children_with_tokens()
            .nth(insert_at)
            .is_some_and(|it| it.kind() != NEWLINE);
        let separated = rest.starts_with(BLANKS) || (rest.is_empty() && !followed);
        let combined = format!("{prefix}{rest}");
        let modifiers = prefix.trim_end_matches(BLANKS);
        if combined.len() - strip(&combined).len() != modifiers.len()
            || (prefix.ends_with(|c: char| c.is_ascii_digit()) && !separated)
        {
            return Err(error(format!(
                "Cannot write {prefix:?} as the prefix of {:?}",
                self.text()
            )));
        }
        let mut old = prefix_tokens;
        old.extend(first_text);
        let text = combined;
        if let Some(same) = old.iter().position(|t| t.text() == text) {
            old.remove(same);
            detach_elements(old.into_iter().map(Into::into));
            return Ok(());
        }
        // A recipe line starting with `#` is a comment, and one starting
        // with a prefix character is text.
        let kind = if text.starts_with('#') { COMMENT } else { TEXT };
        let new = if text.is_empty() {
            vec![]
        } else {
            detached_elements(&[(kind, &text)], None)
        };
        let start = old.first().map_or(insert_at, |t| t.index());
        replace_range(node, start..start + old.len(), new);
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

        let new_syntax =
            build_recipe(prefix, self.recipe_prefix(), new_text, &eol, "replace_text")?;

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
        let rule = self.syntax().ancestors().find(|n| n.kind() == RULE);
        self.remove_node();
        if let Some(rule) = rule {
            move_out_trailing_lines(&rule);
        }
    }

    /// Remove this recipe line, as [`Recipe::remove`], leaving the rest of
    /// the rule as it is.
    fn remove_node(&self) {
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
        // After a BSD make target-local assignment, the line break goes in
        // the VARIABLE node, as the parser has it without a command.
        if let Some(variable) = node.prev_sibling().filter(|n| n.kind() == VARIABLE) {
            parent.splice_children(node_index..node_index + 1, vec![]);
            let len = variable.children_with_tokens().count();
            variable.splice_children(len..len, replacement);
            return;
        }
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
        replace_range(
            node,
            0..inline_prefix.len(),
            detached_elements(&[(INDENT, &prefix)], None),
        );
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

    /// The text of the recipe each edit that takes a command writes,
    /// after `header`, which may set `.RECIPEPREFIX`.
    fn edited_commands(header: &str, prefix: char, line: &str) -> Vec<String> {
        let parse = |text: &str| -> Makefile {
            format!("{header}{}", text.replace('\t', &prefix.to_string()))
                .parse()
                .unwrap()
        };
        let mut results = vec![];
        let mut check = |makefile: &Makefile, recipe: &Recipe| {
            crate::test_util::assert_matches_reparse(makefile);
            results.push(recipe.shell_text());
        };

        let makefile = parse("all:\n\techo x\n");
        let mut rule = makefile.rules().next().unwrap();
        rule.try_push_command(line).unwrap();
        check(&makefile, &rule.recipe_nodes().nth(1).unwrap());

        let makefile = parse("all:\n\techo x\n");
        let mut rule = makefile.rules().next().unwrap();
        rule.try_replace_command(0, line).unwrap();
        check(&makefile, &rule.recipe_nodes().next().unwrap());

        for text in ["all:\n\techo x\n", "all: ; echo x\n"] {
            let makefile = parse(text);
            let mut recipe = makefile
                .rules()
                .next()
                .unwrap()
                .recipe_nodes()
                .next()
                .unwrap();
            recipe.try_replace_text(line).unwrap();
            check(&makefile, &recipe);
        }

        let makefile = parse("all:\n\techo x\n");
        let recipe = makefile
            .rules()
            .next()
            .unwrap()
            .recipe_nodes()
            .next()
            .unwrap();
        recipe.try_insert_before(line).unwrap();
        recipe.try_insert_after(line).unwrap();
        let recipes: Vec<_> = makefile.rules().next().unwrap().recipe_nodes().collect();
        check(&makefile, &recipes[0]);
        check(&makefile, &recipes[2]);
        results
    }

    #[test]
    fn test_insert_rule_custom_recipe_prefix() {
        let source: Makefile = "all:\n\techo a \\\n b \\\n\tc \\\n>d\n".parse().unwrap();
        let rule = source.rules().next().unwrap();
        let expected = rule.recipe_nodes().next().unwrap().shell_text();
        for (text, code) in [
            (
                "define .RECIPEPREFIX\n \nendef\nX = 1\n",
                "all:\n echo a \\\n  b \\\n c \\\n>d\n",
            ),
            (
                ".RECIPEPREFIX = >\nX = 1\n",
                "all:\n>echo a \\\n b \\\n>c \\\n>>d\n",
            ),
        ] {
            let makefile: Makefile = text.parse().unwrap();
            let mut item = makefile.items().last().unwrap();
            item.insert_after(crate::MakefileItem::Rule(rule.clone()))
                .unwrap();
            assert_eq!(makefile.code(), format!("{text}{code}"));
            let inserted = makefile.rules().next().unwrap();
            assert_eq!(
                inserted.recipe_nodes().next().unwrap().shell_text(),
                expected
            );
            crate::test_util::assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_insert_rule_custom_recipe_prefix_rule_line() {
        // The prefix of continuation lines of a recipe after `;` is
        // rewritten like that of a recipe on a line of its own.
        let tab_source = "all: ; echo a \\\n\tb \\\n c \\\n\t>d \\\n>e\n";
        let custom_source = ".RECIPEPREFIX = >\nall: ; echo a \\\n>b \\\n\tc \\\n >d\n";
        for (source, text, code) in [
            (
                tab_source,
                ".RECIPEPREFIX = >\nX = 1\n",
                "all: ; echo a \\\n>b \\\n c \\\n>>d \\\n>>e\n",
            ),
            (
                tab_source,
                "define .RECIPEPREFIX\n \nendef\nX = 1\n",
                "all: ; echo a \\\n b \\\n  c \\\n >d \\\n>e\n",
            ),
            (
                custom_source,
                "X = 1\n",
                "all: ; echo a \\\n\tb \\\n\t\tc \\\n >d\n",
            ),
            (
                custom_source.strip_suffix('\n').unwrap(),
                "X = 1\n",
                "all: ; echo a \\\n\tb \\\n\t\tc \\\n >d\n",
            ),
            (
                ".RECIPEPREFIX = >\nall:\n>echo a \\\n>b \\\n\tc \\\n >d\n",
                "X = 1\n",
                "all:\n\techo a \\\n\tb \\\n\t\tc \\\n >d\n",
            ),
        ] {
            let source_makefile: Makefile = source.parse().unwrap();
            let rule = source_makefile.rules().next().unwrap();
            let expected = rule.recipe_nodes().next().unwrap().shell_text();
            let makefile: Makefile = text.parse().unwrap();
            let mut item = makefile.items().last().unwrap();
            item.insert_after(crate::MakefileItem::Rule(rule.clone()))
                .unwrap();
            assert_eq!(makefile.code(), format!("{text}{code}"), "{source:?}");
            let inserted = makefile.rules().next().unwrap();
            assert_eq!(
                inserted.recipe_nodes().next().unwrap().shell_text(),
                expected
            );
            crate::test_util::assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_edit_commands_custom_recipe_prefix() {
        // Each edit writes the command so that make reads it the same way
        // whatever the recipe prefix.
        let lines = [
            "echo a \\\n b",
            "echo a \\\n\tb",
            "echo a \\\n>b",
            "echo a \\\n  b",
            "echo a \\\n\t>b",
            "echo a \\\n\t b",
            "echo \"$(subst x,y,a\\\n x)\"",
            "# c \\\n>d",
        ];
        for line in lines {
            let expected = edited_commands("", '\t', line);
            for (header, prefix) in [
                (".RECIPEPREFIX = >\n", '>'),
                ("define .RECIPEPREFIX\n \nendef\n", ' '),
            ] {
                assert_eq!(
                    edited_commands(header, prefix, line),
                    expected,
                    "{header:?} {line:?}"
                );
            }
        }
    }

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
            (
                "define .RECIPEPREFIX\n \nendef\nall:\n echo a \\\n  b\n",
                "echo a \\\n b",
            ),
            (
                "define .RECIPEPREFIX\n \nendef\nall:\n echo \"c \\\n d\"\n",
                "echo \"c \\\nd\"",
            ),
            (
                "define .RECIPEPREFIX\n \nendef\nall: ; echo a \\\n b \\\n\tc\n",
                "echo a \\\nb \\\n\tc",
            ),
            (
                "define .RECIPEPREFIX\n \nendef\nall:\n echo \"$(subst x,y,a\\\n x)\"\n",
                "echo \"$(subst x,y,a\\\n x)\"",
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

        // As GNU make passes it to the shell.
        let makefile: Makefile = ".RECIPEPREFIX = >\nall: ; # c \\\n>>d\n".parse().unwrap();
        let recipe = makefile
            .rules()
            .next()
            .unwrap()
            .recipe_nodes()
            .next()
            .unwrap();
        assert_eq!(recipe.shell_text(), "# c \\\n>d");

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

    /// Set the prefix of the first recipe in `code`, parsed as `variant`.
    fn set_prefix_for(
        code: &str,
        prefix: &str,
        variant: crate::MakefileVariant,
    ) -> Result<String, Error> {
        let makefile = Makefile::parse_with_variant(code, variant).tree();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();
        if let Err(e) = recipe.try_set_prefix_for(prefix, variant) {
            assert_eq!(makefile.code(), code);
            return Err(e);
        }
        let reparsed = Makefile::parse_with_variant(&makefile.code(), variant);
        assert_eq!(reparsed.errors(), &[]);
        assert_eq!(
            format!("{:#?}", makefile.syntax()),
            format!("{:#?}", reparsed.tree().syntax())
        );
        Ok(makefile.code())
    }

    #[test]
    fn test_recipe_set_prefix_for_nmake() {
        use crate::MakefileVariant::NMake;
        for (code, prefix, expected) in [
            ("x:\n\techo hi\n", "@", "x:\n\t@echo hi\n"),
            ("x:\n\techo hi\n", "!", "x:\n\t!echo hi\n"),
            ("x:\n\techo hi\n", "-3 ", "x:\n\t-3 echo hi\n"),
            ("x:\n\techo hi\n", "@ -12\t! ", "x:\n\t@ -12\t! echo hi\n"),
            ("x:\n\t@ -3 ! echo hi\n", "-", "x:\n\t- echo hi\n"),
            ("x:\n\t@ -3 ! echo hi\n", "-3", "x:\n\t-3 echo hi\n"),
            ("x:\n\t@ -3 ! echo hi\n", "", "x:\n\t echo hi\n"),
            ("x:\n\t-5\techo\n", "@ !", "x:\n\t@ !\techo\n"),
            ("x:\n\t @echo  hi # c\n", "!@", "x:\n\t!@echo  hi # c\n"),
            ("x:\n\t@$(X)\n", "-", "x:\n\t-$(X)\n"),
            ("x:\n\t@\n", "-3", "x:\n\t-3\n"),
        ] {
            assert_eq!(
                set_prefix_for(code, prefix, NMake).unwrap(),
                expected,
                "{code:?} {prefix:?}"
            );
        }
        for (code, prefix) in [
            ("x:\n\techo hi\n", "+"),
            ("x:\n\techo hi\n", "x"),
            ("x:\n\techo hi\n", "-a"),
            ("x:\n\techo hi\n", "\n"),
            // A number after `-` has to be followed by a space or tab.
            ("x:\n\techo hi\n", "-3"),
            ("x:\n\t@$(X)\n", "-3"),
            // The command would be read as part of the modifier.
            ("x:\n\t@123.exe\n", "-"),
        ] {
            assert!(
                set_prefix_for(code, prefix, NMake).is_err(),
                "{code:?} {prefix:?}"
            );
        }
    }

    #[test]
    fn test_recipe_set_prefix_for_gnu_bsd() {
        use crate::MakefileVariant::*;
        for variant in [GNUMake, POSIXMake, BSDMake] {
            assert_eq!(
                set_prefix_for("x:\n\t@echo  hi # c\n", "+-", variant).unwrap(),
                "x:\n\t+-echo  hi # c\n"
            );
            for prefix in ["!", "-3 "] {
                assert!(set_prefix_for("x:\n\techo hi\n", prefix, variant).is_err());
            }
        }
    }

    #[test]
    fn test_recipe_set_prefix_for_whitespace() {
        use crate::MakefileVariant::*;
        // GNU make allows whitespace between modifiers, BSD make only before
        // them.
        for variant in [GNUMake, POSIXMake] {
            for (code, prefix, expected) in [
                ("x:\n\techo hi\n", "@ -", "x:\n\t@ -echo hi\n"),
                ("x:\n\techo hi\n", "@ ", "x:\n\t@ echo hi\n"),
                ("x:\n\t@ -false\n", "-\t@ ", "x:\n\t-\t@ false\n"),
                ("x:\n\t@ -false # c\n", "", "x:\n\tfalse # c\n"),
                ("x:\n\t @ - echo  hi\n", "+", "x:\n\t+ echo  hi\n"),
            ] {
                assert_eq!(
                    set_prefix_for(code, prefix, variant).unwrap(),
                    expected,
                    "{code:?} {prefix:?} {variant:?}"
                );
            }
        }
        for (code, prefix, expected) in [
            ("x:\n\t@ -false\n", "+", "x:\n\t+ -false\n"),
            ("x:\n\t @echo hi\n", "-", "x:\n\t-echo hi\n"),
            ("x:\n\t- @echo hi\n", "-+", "x:\n\t-+ @echo hi\n"),
        ] {
            assert_eq!(set_prefix_for(code, prefix, BSDMake).unwrap(), expected);
        }
        for (code, prefix) in [
            ("x:\n\techo hi\n", "@ "),
            ("x:\n\techo hi\n", "@ -"),
            // BSD make would read the `-` as a modifier.
            ("x:\n\t@ -false\n", ""),
        ] {
            assert!(
                set_prefix_for(code, prefix, BSDMake).is_err(),
                "{code:?} {prefix:?}"
            );
        }
    }

    #[test]
    fn test_recipe_set_prefix_whitespace() {
        // Without a variant, the modifiers are those GNU make reads, which
        // include BSD make's.
        for (code, prefix, expected) in [
            ("all:\n\t@ -false\n", "", "all:\n\tfalse\n"),
            ("all:\n\t@ -false # c\n", "+", "all:\n\t+false # c\n"),
            ("all:\n\t @ - echo x\n", "@", "all:\n\t@ echo x\n"),
            ("all: ; @ -echo x\n", "-", "all: ; -echo x\n"),
            ("all:\n\t- $(X)\n", "@", "all:\n\t@ $(X)\n"),
            ("all:\n\t@\t+-echo\n", "", "all:\n\techo\n"),
        ] {
            let makefile: Makefile = code.parse().unwrap();
            let rule = makefile.rules().next().unwrap();
            let mut recipe = rule.recipe_nodes().next().unwrap();
            recipe.try_set_prefix(prefix).unwrap();
            assert_eq!(makefile.code(), expected, "{code:?}");
            crate::test_util::assert_matches_reparse(&makefile);
        }
    }

    #[test]
    fn test_recipe_modifiers_after_whitespace() {
        use crate::MakefileVariant::*;
        let flags = |code: &str, variant: Option<crate::MakefileVariant>| {
            let parsed = match variant {
                Some(variant) => Makefile::parse_with_variant(code, variant),
                None => Makefile::parse(code),
            };
            let recipe = parsed
                .tree()
                .rules()
                .next()
                .unwrap()
                .recipe_nodes()
                .next()
                .unwrap();
            match variant {
                Some(variant) => (
                    recipe.is_silent_for(variant),
                    recipe.is_ignore_errors_for(variant),
                ),
                None => (recipe.is_silent(), recipe.is_ignore_errors()),
            }
        };
        for (code, variant, expected) in [
            ("all:\n\t@ -false\n", None, (true, true)),
            ("all:\n\t@ -false\n", Some(GNUMake), (true, true)),
            ("all:\n\t@ -false\n", Some(POSIXMake), (true, true)),
            ("all:\n\t@ -false\n", Some(BSDMake), (true, false)),
            ("all:\n\t- @echo\n", None, (true, true)),
            ("all:\n\t- @echo\n", Some(BSDMake), (false, true)),
            ("all:\n\t @echo\n", None, (true, false)),
            ("all:\n\t @echo\n", Some(BSDMake), (true, false)),
            ("all:\n\t@\t+-echo\n", Some(GNUMake), (true, true)),
            ("all:\n\techo -@\n", None, (false, false)),
            ("all:\n\t-3 ! @echo\n", Some(NMake), (true, true)),
            ("all:\n\t!echo -@\n", Some(NMake), (false, false)),
        ] {
            assert_eq!(flags(code, variant), expected, "{code:?} {variant:?}");
        }
    }

    #[test]
    #[should_panic(expected = "\"+\" is not a recipe prefix in NMake")]
    fn test_recipe_set_prefix_for_panics_on_invalid() {
        let makefile =
            Makefile::parse_with_variant("x:\n\techo\n", crate::MakefileVariant::NMake).tree();
        let rule = makefile.rules().next().unwrap();
        let mut recipe = rule.recipe_nodes().next().unwrap();
        recipe.set_prefix_for("+", crate::MakefileVariant::NMake);
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
    fn test_remove_last_recipe_moves_trailing_lines() {
        // The parser only puts comments after a blank line, and conditionals,
        // in a rule if more recipe lines follow them.
        let cases = [
            ("a:\n\techo\n\n# c\n\tcmd\n", 1, "a:\n\techo\n\n# c\n"),
            (
                "a:\n\techo\n\n  # c\n\n  \n# d\n\tcmd\nX = 1\n",
                1,
                "a:\n\techo\n\n  # c\n\n  \n# d\nX = 1\n",
            ),
            (
                "a:\n\techo\n# c\n# d\n\n# e\n\n\tcmd\n",
                1,
                "a:\n\techo\n# c\n# d\n\n# e\n\n",
            ),
            (
                "a:\n\techo\n\n# c\nifdef X\n\tcmd\nendif\n\n# d\n",
                1,
                "a:\n\techo\n\n# c\nifdef X\nendif\n\n# d\n",
            ),
            (
                "a:\n\techo\nifdef X\n\tcmd\nendif\n",
                1,
                "a:\n\techo\nifdef X\nendif\n",
            ),
            ("a: ; echo\n\n# c\n\tcmd\n", 1, "a: ; echo\n\n# c\n"),
            ("a:\n\n# c\n\tcmd\n", 0, "a:\n\n# c\n"),
            ("a: ; cmd\n\n# c\n\tcmd\n", 0, "a:\n\n# c\n\tcmd\n"),
            // Comments directly after the last recipe line stay in the rule.
            ("a:\n\techo\n\tcmd\n# c\n", 1, "a:\n\techo\n# c\n"),
            // Recipe lines after the comment keep it in the rule.
            (
                "a:\n\techo\n\n# c\n\tcmd\n\tlast\n",
                1,
                "a:\n\techo\n\n# c\n\tlast\n",
            ),
        ];
        for (text, index, expected) in cases {
            let makefile: Makefile = text.parse().unwrap();
            let rule = makefile.rules().next().unwrap();
            let comment = rule
                .syntax()
                .descendants_with_tokens()
                .filter_map(|it| it.into_token())
                .find(|t| t.kind() == COMMENT);
            rule.recipe_nodes().nth(index).unwrap().remove();
            assert_eq!(makefile.code(), expected, "{text:?}");
            crate::test_util::assert_matches_reparse(&makefile);
            // The comment is moved, not rebuilt.
            if let Some(comment) = comment {
                assert_eq!(
                    comment.parent_ancestors().last().as_ref(),
                    Some(makefile.syntax()),
                    "{text:?}"
                );
            }
        }
    }

    #[test]
    fn test_remove_last_recipe_moves_trailing_lines_bsd() {
        let cases = [
            (
                "a:\n\techo\n\n# c\n.if 1\n\tcmd\n.endif\n",
                "a:\n\techo\n\n# c\n.if 1\n.endif\n",
            ),
            (
                "a:\n\techo\n.include \"x.mk\"\n\n# c\n\tcmd\n",
                "a:\n\techo\n.include \"x.mk\"\n\n# c\n",
            ),
            (
                "a:\n\techo\ninclude x.mk\n\n# c\n\tcmd\n",
                "a:\n\techo\ninclude x.mk\n\n# c\n",
            ),
            (
                "a:\n\techo\n\n.include \"x.mk\"\n\tcmd\n",
                "a:\n\techo\n\n.include \"x.mk\"\n",
            ),
        ];
        for (text, expected) in cases {
            let parse = |text: &str| {
                let parsed = Makefile::parse_with_variant(text, crate::MakefileVariant::BSDMake);
                assert_eq!(parsed.errors(), &[], "{text:?}");
                parsed.tree()
            };
            let makefile = parse(text);
            let rule = makefile.rules().next().unwrap();
            rule.recipe_nodes().last().unwrap().remove();
            assert_eq!(makefile.code(), expected, "{text:?}");
            assert_eq!(
                format!("{:#?}", makefile.syntax()),
                format!("{:#?}", parse(expected).syntax()),
                "{text:?}"
            );
        }
    }

    #[test]
    fn test_clear_commands_moves_trailing_lines() {
        let makefile: Makefile = "a:\n\techo\n\n# c\nifdef X\n\tcmd\nendif\n\tz\n"
            .parse()
            .unwrap();
        let mut rule = makefile.rules().next().unwrap();
        rule.clear_commands();
        assert_eq!(makefile.code(), "a:\n\n# c\nifdef X\nendif\n");
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
