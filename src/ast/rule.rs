use super::conditional::ConditionalItem;
use super::makefile::MakefileItem;
use super::{
    escape_hashes, is_continuation, line_ending, logical_text, terminate_line_before, LineSyntax,
};
use crate::lossless::{
    node_text, remove_with_preceding_comments, trim_trailing_newlines, Conditional, Error,
    ErrorInfo, Makefile, ParseError, Recipe, Rule, SyntaxElement, SyntaxNode, SyntaxToken,
};
use crate::MakefileVariant;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use rowan::{GreenNode, GreenNodeBuilder, GreenToken};

/// The text of a target or prerequisite as make reads it: line
/// continuations are collapsed and `\#` is unescaped as described by
/// `syntax`, while other backslashes are kept as written.
fn name_text(
    root: &SyntaxNode,
    tokens: impl IntoIterator<Item = SyntaxToken>,
    syntax: LineSyntax,
) -> String {
    // nmake has no `\#` escape, so a `#` after a backslash starts a comment
    // there, but the parser does not know that and keeps it in the name.
    // TODO: Stop at `\#` for nmake once the parser does.
    logical_text(root, tokens, syntax, syntax != LineSyntax::NMake)
}

fn node_name_text(node: &SyntaxNode, syntax: LineSyntax) -> String {
    let tokens = node
        .descendants_with_tokens()
        .filter_map(|it| it.into_token());
    name_text(node, tokens, syntax)
}

/// `name` escaped so that GNU make reads it back as a target or
/// prerequisite name, as [`Rule::targets`] returns it.
fn escape_name(name: &str, before_comment: bool) -> String {
    escape_hashes(name, false, before_comment)
}

fn name_error(context: &str, message: String) -> Error {
    Error::Parse(ParseError {
        errors: vec![ErrorInfo {
            kind: crate::ParseErrorKind::Other,
            message,
            line: 1,
            context: context.to_string(),
        }],
    })
}

/// Parse `line` as a makefile consisting of a single rule.
fn parse_rule_line(line: &str) -> Option<Rule> {
    let parsed = crate::lossless::parse(line, None);
    let mut items = parsed.root().syntax().children();
    items
        .next()
        .and_then(Rule::cast)
        .filter(|_| parsed.errors.is_empty() && items.next().is_none())
}

/// A PREREQUISITES node containing PREREQUISITE nodes, optionally followed
/// by trailing whitespace. With `before_comment`, the node is directly
/// followed by a comment.
///
/// The prerequisites are escaped as needed, and an error is returned if
/// [`Rule::prerequisites`] would not read them back.
fn build_prerequisites_node(
    prereqs: &[String],
    include_leading_space: bool,
    trailing_space: Option<&str>,
    before_comment: bool,
) -> Result<SyntaxNode, Error> {
    let mut children = Vec::new();
    if !prereqs.is_empty() {
        let before_comment = before_comment && trailing_space.is_none();
        let mut line = String::from("x:");
        for (i, prereq) in prereqs.iter().enumerate() {
            line.push(' ');
            line.push_str(&escape_name(
                prereq,
                before_comment && i + 1 == prereqs.len(),
            ));
        }
        line.push_str(if before_comment { "#\n" } else { "\n" });
        let parsed = parse_rule_line(&line)
            .filter(|rule| rule.prerequisites().eq(prereqs.iter().cloned()))
            .and_then(|rule| rule.prerequisites_node())
            .ok_or_else(|| {
                name_error(
                    "set_prerequisites",
                    format!("Cannot write {prereqs:?} as prerequisites"),
                )
            })?;
        for (i, node) in parsed
            .children()
            .filter(|n| n.kind() == PREREQUISITE)
            .enumerate()
        {
            if i > 0 || include_leading_space {
                children.push(GreenToken::new(WHITESPACE.into(), " ").into());
            }
            children.push(node.green().into_owned().into());
        }
    }
    if let Some(space) = trailing_space {
        children.push(GreenToken::new(WHITESPACE.into(), space).into());
    }
    Ok(SyntaxNode::new_root_mut(GreenNode::new(
        PREREQUISITES.into(),
        children,
    )))
}

/// A TARGETS node for `targets`, escaped as needed. Returns an error if
/// [`Rule::targets`] would not read them back.
pub(crate) fn build_targets_node(targets: &[String], context: &str) -> Result<SyntaxNode, Error> {
    let escaped: Vec<_> = targets.iter().map(|t| escape_name(t, false)).collect();
    parse_rule_line(&format!("{}:\n", escaped.join(" ")))
        .filter(|rule| rule.targets().eq(targets.iter().cloned()))
        .and_then(|rule| rule.syntax().children().find(|n| n.kind() == TARGETS))
        .map(|node| SyntaxNode::new_root_mut(node.green().into_owned()))
        .ok_or_else(|| name_error(context, format!("Cannot write {targets:?} as targets")))
}

/// Represents different types of items that can appear in a Rule's body
#[derive(Clone)]
#[non_exhaustive]
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

/// The dependency operator separating a rule's targets from its
/// prerequisites, as returned by [`Rule::operator`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuleOperator {
    /// `:`
    Colon,
    /// `::`, a double-colon rule.
    DoubleColon,
    /// `&:`, GNU make grouped targets.
    GroupedColon,
    /// `&::`, GNU make grouped targets of a double-colon rule.
    GroupedDoubleColon,
    /// `!`, a BSD make rule whose targets are always remade.
    Bang,
}

impl RuleOperator {
    fn from_text(text: &str) -> Option<Self> {
        match text {
            ":" => Some(RuleOperator::Colon),
            "::" => Some(RuleOperator::DoubleColon),
            "&:" => Some(RuleOperator::GroupedColon),
            "&::" => Some(RuleOperator::GroupedDoubleColon),
            "!" => Some(RuleOperator::Bang),
            _ => None,
        }
    }

    /// The operator as written in a makefile, e.g. `"&::"`.
    pub fn as_str(&self) -> &'static str {
        match self {
            RuleOperator::Colon => ":",
            RuleOperator::DoubleColon => "::",
            RuleOperator::GroupedColon => "&:",
            RuleOperator::GroupedDoubleColon => "&::",
            RuleOperator::Bang => "!",
        }
    }

    /// Whether this is a double-colon operator (`::` or `&::`).
    pub fn is_double_colon(&self) -> bool {
        matches!(
            self,
            RuleOperator::DoubleColon | RuleOperator::GroupedDoubleColon
        )
    }

    /// Whether this is a grouped targets operator (`&:` or `&::`).
    pub fn is_grouped(&self) -> bool {
        matches!(
            self,
            RuleOperator::GroupedColon | RuleOperator::GroupedDoubleColon
        )
    }
}

impl std::fmt::Display for RuleOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
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
    /// Targets and prerequisites are escaped as by [`Rule::set_targets`]
    /// and [`Rule::set_prerequisites`].
    ///
    /// # Panics
    ///
    /// Panics if there are no targets, or if a target or prerequisite can
    /// not be written so that it reads back the same.
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
        let owned = |names: &[&str]| names.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        let targets = build_targets_node(&owned(targets), "Rule::new")
            .unwrap_or_else(|e| panic!("invalid targets: {e}"));
        let mut children: Vec<rowan::NodeOrToken<GreenNode, GreenToken>> = vec![
            targets.green().into_owned().into(),
            GreenToken::new(OPERATOR.into(), ":").into(),
        ];
        if !prerequisites.is_empty() {
            let prerequisites = build_prerequisites_node(&owned(prerequisites), false, None, false)
                .unwrap_or_else(|e| panic!("invalid prerequisites: {e}"));
            children.push(GreenToken::new(WHITESPACE.into(), " ").into());
            children.push(prerequisites.green().into_owned().into());
        }
        children.push(GreenToken::new(NEWLINE.into(), "\n").into());
        for recipe in recipes {
            let recipe = GreenNode::new(
                RECIPE.into(),
                [
                    GreenToken::new(INDENT.into(), "\t").into(),
                    GreenToken::new(TEXT.into(), recipe).into(),
                    GreenToken::new(NEWLINE.into(), "\n").into(),
                ],
            );
            children.push(recipe.into());
        }
        let syntax = SyntaxNode::new_root_mut(GreenNode::new(RULE.into(), children));
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
        self.operator().is_some_and(|op| op.is_grouped())
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
        self.operator().is_some_and(|op| op.is_double_colon())
    }

    /// Get the dependency operator that separates the targets from the
    /// prerequisites.
    ///
    /// For a static pattern rule such as `a.o: %.o: %.c` this is the
    /// operator after the targets, not the colon after the target pattern.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant, RuleOperator};
    /// let makefile: Makefile = "a b &:: c\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// assert_eq!(rule.operator(), Some(RuleOperator::GroupedDoubleColon));
    ///
    /// let makefile = Makefile::parse_with_variant("a ! b\n", MakefileVariant::BSDMake).tree();
    /// let rule = makefile.rules().next().unwrap();
    /// assert_eq!(rule.operator(), Some(RuleOperator::Bang));
    /// ```
    pub fn operator(&self) -> Option<RuleOperator> {
        let token = self
            .syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == OPERATOR)?;
        RuleOperator::from_text(token.text())
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

    /// The tokens of each target in a TARGETS node, in order.
    fn target_tokens(node: &SyntaxNode) -> Vec<Vec<SyntaxToken>> {
        let mut result = Vec::new();
        let mut current = Vec::new();

        for child in node.children_with_tokens() {
            // Whitespace and line continuations (backslash-newline plus the
            // continued line's indent) delimit targets. The parser keeps an
            // escaped space as TEXT, and whitespace inside archive member
            // parentheses is part of the nested ARCHIVE_MEMBERS node.
            if child.kind() == WHITESPACE || is_continuation(&child) {
                if !current.is_empty() {
                    result.push(std::mem::take(&mut current));
                }
                continue;
            }
            match child {
                rowan::NodeOrToken::Token(token) => current.push(token),
                rowan::NodeOrToken::Node(n) => {
                    current.extend(n.descendants_with_tokens().filter_map(|it| it.into_token()))
                }
            }
        }

        if !current.is_empty() {
            result.push(current);
        }

        result
    }

    fn extract_targets_from_node(node: &SyntaxNode, syntax: LineSyntax) -> Vec<String> {
        Self::target_tokens(node)
            .into_iter()
            .map(|tokens| name_text(node, tokens, syntax))
            .collect()
    }

    fn targets_node(&self) -> Option<SyntaxNode> {
        self.syntax().children().find(|n| n.kind() == TARGETS)
    }

    /// The source ranges of the targets of this rule, in the same order as
    /// [`Self::targets`].
    ///
    /// Each range covers the target as written, including any escapes and
    /// variable references. A target split by a line continuation inside a
    /// variable reference has a range that spans the continuation.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Rule, TextRange};
    ///
    /// let rule: Rule = "a  $(B): c\n".parse().unwrap();
    /// assert_eq!(
    ///     rule.target_ranges().collect::<Vec<_>>(),
    ///     vec![
    ///         TextRange::new(0.into(), 1.into()),
    ///         TextRange::new(3.into(), 7.into()),
    ///     ]
    /// );
    /// ```
    pub fn target_ranges(&self) -> impl Iterator<Item = rowan::TextRange> + '_ {
        self.targets_node()
            .map(|node| Self::target_tokens(&node))
            .unwrap_or_default()
            .into_iter()
            .filter_map(|tokens| {
                let first = tokens.first()?.text_range();
                let last = tokens.last()?.text_range();
                Some(first.cover(last))
            })
    }

    /// Targets of this rule
    ///
    /// GNU make removes the backslash from `\#` when reading the line, so
    /// `a\#b` is the target `a#b`; as for [`VariableDefinition::value`],
    /// the backslashes before it are halved. Other backslashes are kept as
    /// written, as for variable names: `a\ b` is the single target `a\ b`,
    /// which GNU make reads as `a b`. Line continuations are collapsed as
    /// GNU make does; see [`Self::targets_for`] for other variants.
    ///
    /// [`VariableDefinition::value`]: crate::VariableDefinition::value
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    ///
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
    ///
    /// let rule: Rule = "a\\#b: c\n".parse().unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a#b"]);
    /// ```
    pub fn targets(&self) -> impl Iterator<Item = String> + '_ {
        self.targets_with(LineSyntax::Gnu)
    }

    /// Targets of this rule, with line continuations collapsed and `\#`
    /// unescaped as `variant` does.
    ///
    /// GNU make drops the whitespace before a line continuation, while
    /// POSIX make (and GNU make after `.POSIX:`) and BSD make keep it. This
    /// matters inside variable references, such as in function arguments
    /// or BSD make modifiers. BSD make also unescapes `\#` inside variable
    /// references, and does not halve the backslashes before it. nmake
    /// has no `\#` escape, so it is kept as written.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{MakefileVariant, Rule};
    ///
    /// let rule: Rule = "$(subst a \\\n  b,c,a  b): x\n".parse().unwrap();
    /// assert_eq!(
    ///     rule.targets_for(MakefileVariant::GNUMake).collect::<Vec<_>>(),
    ///     vec!["$(subst a b,c,a  b)"]
    /// );
    /// assert_eq!(
    ///     rule.targets_for(MakefileVariant::POSIXMake).collect::<Vec<_>>(),
    ///     vec!["$(subst a  b,c,a  b)"]
    /// );
    /// ```
    pub fn targets_for(&self, variant: MakefileVariant) -> impl Iterator<Item = String> + '_ {
        self.targets_with(variant.into())
    }

    fn targets_with(&self, syntax: LineSyntax) -> std::vec::IntoIter<String> {
        // First check if there's a TARGETS node
        for child in self.syntax().children_with_tokens() {
            if let Some(node) = child.as_node() {
                if node.kind() == TARGETS {
                    // Extract targets from the TARGETS node
                    return Self::extract_targets_from_node(node, syntax).into_iter();
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

    /// The normal and order-only prerequisites of the rule, with line
    /// continuations collapsed as described by `syntax`.
    fn prerequisite_lists(&self, syntax: LineSyntax) -> (Vec<String>, Vec<String>) {
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
                    let text = node_name_text(&n, syntax).trim().to_string();
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
    /// [`Rule::order_only_prerequisites`]. As with [`Rule::targets`], `\#`
    /// is unescaped and other backslashes are kept as written. Line
    /// continuations are collapsed as GNU make does; see
    /// [`Self::prerequisites_for`] for other variants.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency | dir\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
    /// ```
    pub fn prerequisites(&self) -> impl Iterator<Item = String> + '_ {
        self.prerequisite_lists(LineSyntax::Gnu).0.into_iter()
    }

    /// Get the normal prerequisites in the rule, with line continuations
    /// collapsed and `\#` unescaped as `variant` does; see
    /// [`Self::targets_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{MakefileVariant, Rule};
    /// let rule: Rule = "all: $(subst a \\\n  b,c,a  b)\n".parse().unwrap();
    /// assert_eq!(
    ///     rule.prerequisites_for(MakefileVariant::POSIXMake).collect::<Vec<_>>(),
    ///     vec!["$(subst a  b,c,a  b)"]
    /// );
    /// ```
    pub fn prerequisites_for(&self, variant: MakefileVariant) -> impl Iterator<Item = String> + '_ {
        self.prerequisite_lists(variant.into()).0.into_iter()
    }

    /// Get the order-only prerequisites in the rule, i.e. those after the
    /// first `|` in the prerequisite list. These are read as for
    /// [`Rule::prerequisites`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "foo.o: foo.c | build\n\tcc -c foo.c".parse().unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["foo.c"]);
    /// assert_eq!(rule.order_only_prerequisites().collect::<Vec<_>>(), vec!["build"]);
    /// ```
    pub fn order_only_prerequisites(&self) -> impl Iterator<Item = String> + '_ {
        self.prerequisite_lists(LineSyntax::Gnu).1.into_iter()
    }

    /// Get the order-only prerequisites in the rule, with line
    /// continuations collapsed and `\#` unescaped as `variant` does; see
    /// [`Self::targets_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{MakefileVariant, Rule};
    /// let rule: Rule = "all: | $(subst a \\\n  b,c,a  b)\n".parse().unwrap();
    /// assert_eq!(
    ///     rule.order_only_prerequisites_for(MakefileVariant::POSIXMake)
    ///         .collect::<Vec<_>>(),
    ///     vec!["$(subst a  b,c,a  b)"]
    /// );
    /// ```
    pub fn order_only_prerequisites_for(
        &self,
        variant: MakefileVariant,
    ) -> impl Iterator<Item = String> + '_ {
        self.prerequisite_lists(variant.into()).1.into_iter()
    }

    /// Get the target pattern of a static pattern rule.
    ///
    /// For a rule like `$(OBJS): %.o: %.c`, this returns `%.o`, while
    /// [`Rule::prerequisites`] returns the prerequisite patterns. Returns
    /// `None` if this is not a static pattern rule. The pattern is read as
    /// for [`Rule::prerequisites`]; see [`Self::static_pattern_for`] for
    /// other variants.
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
        self.static_pattern_with(LineSyntax::Gnu)
    }

    /// Get the target pattern of a static pattern rule, with line
    /// continuations collapsed and `\#` unescaped as `variant` does; see
    /// [`Self::targets_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{MakefileVariant, Rule};
    /// let rule: Rule = "$(OBJS): $(X:a \\\n  b=%.o): %.c\n".parse().unwrap();
    /// assert_eq!(
    ///     rule.static_pattern_for(MakefileVariant::POSIXMake),
    ///     Some("$(X:a  b=%.o)".to_string())
    /// );
    /// ```
    pub fn static_pattern_for(&self, variant: MakefileVariant) -> Option<String> {
        self.static_pattern_with(variant.into())
    }

    fn static_pattern_with(&self, syntax: LineSyntax) -> Option<String> {
        self.syntax()
            .children()
            .find(|n| n.kind() == TARGET_PATTERN)
            .map(|n| node_name_text(&n, syntax).trim().to_string())
    }

    /// Get the commands in the rule
    ///
    /// A recipe given on the rule line after a `;` is the first command.
    /// Commands inside conditionals and BSD `.for` loops in the rule's body
    /// are included, see [`Rule::recipe_nodes`].
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
    /// (`target: VAR [op] value`), return the embedded [`VariableDefinition`](crate::VariableDefinition).
    ///
    /// In BSD make, such a target-local assignment may follow other sources,
    /// as in `prog: .USE VAR=value`, and the rule may have commands. BSD make
    /// only assigns the variable if `.MAKE.TARGET_LOCAL_VARIABLES` is true,
    /// as it is by default; otherwise the words are sources. That setting is
    /// not tracked by the parser.
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
    /// Like [`Makefile::rules`], this descends into conditionals, so recipe
    /// lines inside conditionals and BSD `.for` loops in the rule's body are
    /// included, in source order, whichever branch they are in. Recipes of
    /// other rules inside such a conditional are not. Use [`Rule::body_items`]
    /// to see the structure of the body.
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
    ///
    /// let rule: Rule = "test:\nifdef V\n\techo verbose\nelse\n\techo quiet\nendif\n"
    ///     .parse()
    ///     .unwrap();
    /// let texts: Vec<_> = rule.recipe_nodes().map(|r| r.text()).collect();
    /// assert_eq!(texts, vec!["echo verbose", "echo quiet"]);
    /// ```
    pub fn recipe_nodes(&self) -> impl Iterator<Item = Recipe> {
        let root = self.syntax().clone();
        let mut preorder = self.syntax().preorder();
        std::iter::from_fn(move || {
            while let Some(event) = preorder.next() {
                let rowan::WalkEvent::Enter(node) = event else {
                    continue;
                };
                match node.kind() {
                    RECIPE => {
                        preorder.skip_subtree();
                        return Recipe::cast(node);
                    }
                    CONDITIONAL | FOR_LOOP => {}
                    _ if node == root => {}
                    _ => preorder.skip_subtree(),
                }
            }
            None
        })
    }

    /// The index in the rule's children at which to append a recipe line:
    /// after the last recipe line or conditional in the body.
    fn recipe_end_index(&self) -> usize {
        self.syntax()
            .children()
            .filter(|n| matches!(n.kind(), RECIPE | CONDITIONAL | FOR_LOOP))
            .last()
            .map_or_else(
                || self.syntax().children_with_tokens().count(),
                |n| n.index() + 1,
            )
    }

    /// Get all items (recipe lines and conditionals) in the rule's body
    ///
    /// This method iterates through the rule's body and yields both recipe lines
    /// and any conditionals that appear within the rule.
    ///
    /// A conditional is part of the rule if a recipe line comes first in one of
    /// its branches. Recipe lines inside it are returned by [`Rule::recipes`],
    /// but not as items here. Any other items in it (such as variable
    /// definitions) are not part of the rule, though `Makefile::rules()` and
    /// `Makefile::variable_definitions()` do include them.
    ///
    /// Use [`Rule::body_items`] to get the [`Recipe`] nodes rather than just
    /// their text, as well as BSD `.for` loops, which this skips.
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

    /// Get the items in the rule's body in source order, with recipe lines
    /// as [`Recipe`] nodes.
    ///
    /// This is like [`Rule::items`], but yields the [`Recipe`] node rather
    /// than just its text, so that position information, prefixes and
    /// [`Recipe::shell_text`] are available. It also includes the other
    /// items the parser places in a rule's body, such as GNU conditionals
    /// and BSD `.if` and `.for` blocks. A recipe given on the rule line
    /// after a `;` is the first item.
    ///
    /// The items of a conditional are available through
    /// [`ConditionalBranch::items`](crate::ConditionalBranch::items), and
    /// those of a `.for` loop through
    /// [`ForLoop::body_items`](crate::ForLoop::body_items).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{ConditionalItem, MakefileItem, Rule};
    ///
    /// let rule: Rule = "test: ; @echo start\nifdef V\n\techo verbose\nendif\n".parse().unwrap();
    /// let items: Vec<_> = rule.body_items().collect();
    /// assert_eq!(items.len(), 2);
    ///
    /// let ConditionalItem::Recipe(first) = &items[0] else { panic!() };
    /// assert_eq!(first.shell_text(), "@echo start");
    /// assert!(first.is_silent());
    /// assert_eq!(first.line(), 0);
    ///
    /// let ConditionalItem::Item(MakefileItem::Conditional(cond)) = &items[1] else { panic!() };
    /// assert_eq!(cond.conditional_type(), Some("ifdef".to_string()));
    /// ```
    pub fn body_items(&self) -> impl Iterator<Item = ConditionalItem> {
        self.syntax()
            .children()
            // A VARIABLE child is a target-specific assignment on the rule
            // line, not part of the body.
            .filter(|n| n.kind() != VARIABLE)
            .filter_map(ConditionalItem::cast)
    }

    /// Replace the command at index i with a new line
    ///
    /// Commands are indexed as returned by [`Rule::recipe_nodes`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// rule.replace_command(0, "new command");
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["new command"]);
    /// ```
    pub fn replace_command(&mut self, i: usize, line: &str) -> bool {
        let Some(mut recipe) = self.recipe_nodes().nth(i) else {
            return false;
        };
        if recipe.is_inline() {
            recipe.replace_text(line);
            return true;
        }
        let target_node = recipe.syntax();
        let target_index = target_node.index();
        let parent = target_node
            .parent()
            .expect("Recipe node must have a parent");

        let eol = line_ending(self.syntax());
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), line);
        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());

        parent.splice_children(target_index..target_index + 1, vec![syntax.into()]);

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
        let index = self.recipe_end_index();
        let eol = line_ending(self.syntax());
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), line);
        builder.token(NEWLINE.into(), &eol);
        builder.finish_node();
        let syntax = SyntaxNode::new_root_mut(builder.finish());

        let index = terminate_line_before(self.syntax(), index, &eol);
        self.syntax()
            .splice_children(index..index, vec![syntax.into()]);
    }

    /// Remove command at given index
    ///
    /// Commands are indexed as returned by [`Rule::recipe_nodes`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "rule:\n\tcommand1\n\tcommand2\n".parse().unwrap();
    /// rule.remove_command(0);
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command2"]);
    /// ```
    pub fn remove_command(&mut self, index: usize) -> bool {
        let Some(recipe) = self.recipe_nodes().nth(index) else {
            return false;
        };
        recipe.remove();
        true
    }

    /// Insert command at given index
    ///
    /// Commands are indexed as returned by [`Rule::recipe_nodes`]. An index
    /// equal to the number of commands appends the command, as
    /// [`Rule::push_command`] does.
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
        let recipes: Vec<_> = self.recipe_nodes().collect();
        match recipes.get(index) {
            Some(recipe) => recipe.insert_before(line),
            None if index == recipes.len() => self.push_command(line),
            None => return false,
        }
        true
    }

    /// Get the number of commands/recipes in this rule
    ///
    /// This counts the commands returned by [`Rule::recipe_nodes`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule:\n\tcommand1\n\tcommand2\n".parse().unwrap();
    /// assert_eq!(rule.recipe_count(), 2);
    /// ```
    pub fn recipe_count(&self) -> usize {
        self.recipe_nodes().count()
    }

    /// Clear all commands from this rule
    ///
    /// This removes the commands returned by [`Rule::recipe_nodes`], so
    /// conditionals in the rule's body are kept, without their commands.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let mut rule: Rule = "rule:\n\tcommand1\n\tcommand2\n".parse().unwrap();
    /// rule.clear_commands();
    /// assert_eq!(rule.recipe_count(), 0);
    /// ```
    pub fn clear_commands(&mut self) {
        let recipes: Vec<_> = self.recipe_nodes().collect();
        // Remove all recipes in reverse order to maintain correct indices
        for recipe in recipes.into_iter().rev() {
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
    /// The prerequisites are taken as [`Rule::prerequisites`] returns them,
    /// and `#` is escaped. Returns an error if a prerequisite can not be
    /// written so that it reads back the same, such as one containing
    /// whitespace or a `|`.
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
            let fresh = build_prerequisites_node(
                &prereqs,
                !has_external_whitespace,
                separator,
                next_kind == Some(COMMENT),
            )?;
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

        let before_comment = self
            .syntax()
            .children_with_tokens()
            .nth(insert_pos)
            .is_some_and(|e| e.kind() == COMMENT);
        let new_prereqs = build_prerequisites_node(&prereqs, true, None, before_comment)?;
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
        let new_targets_node = build_targets_node(&new_targets, "rename_target")?;

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
    /// The targets are taken as [`Rule::targets`] returns them, and `#` is
    /// escaped. Returns an error if a target can not be written so that it
    /// reads back the same, such as one containing whitespace or a `:`.
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
        let new_targets_node = build_targets_node(
            &targets.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
            "set_targets",
        )?;

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
        let new_targets_node = build_targets_node(&new_targets, "remove_target")?;

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
    use crate::{
        ConditionalItem, Makefile, MakefileItem, MakefileVariant, Rule, RuleItem, RuleOperator,
    };

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
        // Whitespace inside the parentheses must not split the target: it is
        // part of the nested ARCHIVE_MEMBERS node.
        let rule: Rule = "lib.a(a.o b.o): dep\n\tcmd".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["lib.a(a.o b.o)"]);
    }

    #[test]
    fn test_targets_variable_reference() {
        let rule: Rule = "$(VAR): dep\n\tcmd".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["$(VAR)"]);
    }

    fn target_range_texts(text: &str) -> Vec<String> {
        let rule: Rule = text.parse().unwrap();
        rule.target_ranges()
            .map(|range| text[range].to_string())
            .collect()
    }

    #[test]
    fn test_target_ranges_multiple() {
        let rule: Rule = "a bb  ccc: dep\n".parse().unwrap();
        assert_eq!(
            rule.target_ranges().collect::<Vec<_>>(),
            vec![
                rowan::TextRange::new(0.into(), 1.into()),
                rowan::TextRange::new(2.into(), 4.into()),
                rowan::TextRange::new(6.into(), 9.into()),
            ]
        );
    }

    #[test]
    fn test_target_ranges_texts() {
        assert_eq!(
            target_range_texts("$(VAR) x$(Y)z lib.a(a.o b.o) a\\ b: dep\n"),
            vec!["$(VAR)", "x$(Y)z", "lib.a(a.o b.o)", "a\\ b"]
        );
    }

    #[test]
    fn test_target_ranges_continuation() {
        assert_eq!(target_range_texts("a \\\n  b: dep\n"), vec!["a", "b"]);
    }

    #[test]
    fn test_target_ranges_continuation_in_reference() {
        assert_eq!(
            target_range_texts("$(subst a \\\n  b,c,x) y: dep\n"),
            vec!["$(subst a \\\n  b,c,x)", "y"]
        );
    }

    #[test]
    fn test_target_ranges_escaped_hash() {
        assert_eq!(target_range_texts("a\\#b c: dep\n"), vec!["a\\#b", "c"]);
    }

    #[test]
    fn test_target_ranges_empty() {
        assert_eq!(target_range_texts(": dep\n"), Vec::<String>::new());
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

    fn operators(text: &str, variant: Option<MakefileVariant>) -> Vec<Option<RuleOperator>> {
        let parsed = match variant {
            Some(variant) => Makefile::parse_with_variant(text, variant),
            None => Makefile::parse(text),
        };
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        assert_eq!(makefile.to_string(), text);
        makefile.rules().map(|r| r.operator()).collect()
    }

    #[test]
    fn test_operator_gnu() {
        for variant in [None, Some(MakefileVariant::GNUMake)] {
            assert_eq!(
                operators("a: b\nc:: d\ne f &: g\nh i &:: j\n:\n", variant),
                vec![
                    Some(RuleOperator::Colon),
                    Some(RuleOperator::DoubleColon),
                    Some(RuleOperator::GroupedColon),
                    Some(RuleOperator::GroupedDoubleColon),
                    Some(RuleOperator::Colon),
                ]
            );
        }
    }

    #[test]
    fn test_operator_bsd() {
        for variant in [None, Some(MakefileVariant::BSDMake)] {
            assert_eq!(
                operators("a: b\nc:: d\ne ! f\ng!h\n", variant),
                vec![
                    Some(RuleOperator::Colon),
                    Some(RuleOperator::DoubleColon),
                    Some(RuleOperator::Bang),
                    Some(RuleOperator::Bang),
                ]
            );
        }
    }

    #[test]
    fn test_operator_posix_and_nmake() {
        for variant in [MakefileVariant::POSIXMake, MakefileVariant::NMake] {
            assert_eq!(
                operators("a: b\nc:: d\n", Some(variant)),
                vec![Some(RuleOperator::Colon), Some(RuleOperator::DoubleColon)]
            );
        }
    }

    #[test]
    fn test_operator_static_pattern_rule() {
        assert_eq!(
            operators(
                "a.o: %.o: %.c\nb.o:: %.o: %.c\nc.x c.y &: %.x: %.c\n",
                Some(MakefileVariant::GNUMake)
            ),
            vec![
                Some(RuleOperator::Colon),
                Some(RuleOperator::DoubleColon),
                Some(RuleOperator::GroupedColon),
            ]
        );
    }

    #[test]
    fn test_operator_ignores_later_operators() {
        assert_eq!(
            operators(
                "a: VAR ::= x\nb: c | d\ne: ; echo\n",
                Some(MakefileVariant::GNUMake)
            ),
            vec![
                Some(RuleOperator::Colon),
                Some(RuleOperator::Colon),
                Some(RuleOperator::Colon),
            ]
        );
    }

    #[test]
    fn test_operator_bsd_split_assignment() {
        // BSD make reads `a b:::=c` as `::` followed by a target-local `:=`
        // assignment, and `d e!=f` as `!` followed by `=`.
        assert_eq!(
            operators("a b:::=c\nd e!=f\n", Some(MakefileVariant::BSDMake)),
            vec![Some(RuleOperator::DoubleColon), Some(RuleOperator::Bang)]
        );
    }

    #[test]
    fn test_rule_operator_as_str() {
        assert_eq!(
            [
                RuleOperator::Colon,
                RuleOperator::DoubleColon,
                RuleOperator::GroupedColon,
                RuleOperator::GroupedDoubleColon,
                RuleOperator::Bang,
            ]
            .map(|op| op.as_str()),
            [":", "::", "&:", "&::", "!"]
        );
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
    fn test_quotes_in_rule() {
        // Make does not group quoted words, and `#` starts a comment even
        // inside quotes.
        let code = "x\"y\": 'p q' \"r#s\"\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.code(), code);
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["x\"y\""]);
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["'p", "q'", "\"r"]
        );
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
    fn test_double_colon_static_pattern_rule() {
        let rule: Rule = "a.o b.o:: %.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a.o", "b.o"]);
        assert!(rule.is_double_colon());
        assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
        assert_eq!(prereqs(&rule), (vec!["%.c".to_string()], vec![]));
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["$(CC) -c $<"]);
        assert_eq!(rule.to_string(), "a.o b.o:: %.o: %.c\n\t$(CC) -c $<\n");
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
    fn test_recipe_nodes_in_conditional() {
        let text = "all:\nifdef X\n\techo $(FOO)\nendif\n";
        let makefile: Makefile = text.parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            rule.recipe_nodes()
                .map(|r| (r.text(), r.text_range().into()))
                .collect::<Vec<(String, std::ops::Range<usize>)>>(),
            vec![("echo $(FOO)".to_string(), 13..26)]
        );
    }

    const NESTED: &str =
        "all:\n\ta\nifdef X\n\tb\nelse\nifdef Y\n\tc\nendif\nfoo:\n\td\nendif\n\te\n";

    #[test]
    fn test_recipes_in_nested_conditionals() {
        let makefile: Makefile = NESTED.parse().unwrap();
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(recipes(&rules[0]), vec!["a", "b", "c", "e"]);
        assert_eq!(rules[0].recipe_count(), 4);
        assert_eq!(recipes(&rules[1]), vec!["d"]);
        assert_eq!(
            rules[0]
                .recipe_nodes()
                .map(|r| r.parent().unwrap().targets().collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![vec!["all"]; 4]
        );
        assert_eq!(
            rules[1]
                .recipe_nodes()
                .next()
                .unwrap()
                .parent()
                .unwrap()
                .targets()
                .collect::<Vec<_>>(),
            vec!["foo"]
        );
    }

    #[test]
    fn test_commands_in_conditional() {
        let text = "all:\n\ta\nifdef X\n\tb\nendif\n";

        let mut rule: Rule = text.parse().unwrap();
        assert!(rule.replace_command(1, "B"));
        assert_eq!(rule.to_string(), "all:\n\ta\nifdef X\n\tB\nendif\n");

        let mut rule: Rule = text.parse().unwrap();
        assert!(rule.remove_command(1));
        assert_eq!(rule.to_string(), "all:\n\ta\nifdef X\nendif\n");
        assert!(!rule.remove_command(1));

        let mut rule: Rule = text.parse().unwrap();
        assert!(rule.insert_command(1, "x"));
        assert_eq!(rule.to_string(), "all:\n\ta\nifdef X\n\tx\n\tb\nendif\n");

        let mut rule: Rule = text.parse().unwrap();
        assert!(rule.insert_command(2, "c"));
        assert_eq!(rule.to_string(), "all:\n\ta\nifdef X\n\tb\nendif\n\tc\n");
        assert!(!rule.insert_command(4, "d"));

        let mut rule: Rule = text.parse().unwrap();
        rule.push_command("c");
        assert_eq!(rule.to_string(), "all:\n\ta\nifdef X\n\tb\nendif\n\tc\n");
        assert_eq!(recipes(&rule), vec!["a", "b", "c"]);

        let mut rule: Rule = text.parse().unwrap();
        rule.clear_commands();
        assert_eq!(rule.to_string(), "all:\nifdef X\nendif\n");
        assert_eq!(rule.recipe_count(), 0);
    }

    fn describe_body_item(item: ConditionalItem) -> String {
        match item {
            ConditionalItem::Recipe(r) => format!("{}: {}", r.line(), r.text()),
            ConditionalItem::Item(MakefileItem::Conditional(c)) => {
                let branches: Vec<String> = c
                    .branches()
                    .map(|b| {
                        let items: Vec<String> = b.items().map(describe_body_item).collect();
                        format!(
                            "{} [{}]",
                            b.conditional_type().unwrap_or_else(|| "else".to_string()),
                            items.join(", ")
                        )
                    })
                    .collect();
                branches.join(" ")
            }
            ConditionalItem::Item(MakefileItem::ForLoop(f)) => {
                let items: Vec<String> = f.body_items().map(describe_body_item).collect();
                format!(".for [{}]", items.join(", "))
            }
            ConditionalItem::Item(_) => "other".to_string(),
        }
    }

    fn body(rule: &Rule) -> Vec<String> {
        rule.body_items().map(describe_body_item).collect()
    }

    #[test]
    fn test_body_items_plain_recipes() {
        let rule: Rule = "all: dep\n\techo a\n\t@echo b\n".parse().unwrap();
        assert_eq!(body(&rule), vec!["1: echo a", "2: @echo b"]);
    }

    #[test]
    fn test_body_items_empty() {
        let rule: Rule = "all: dep\n".parse().unwrap();
        assert_eq!(body(&rule), Vec::<String>::new());
    }

    #[test]
    fn test_body_items_scoped_assignment() {
        let rule: Rule = "all: CFLAGS = -O2\n".parse().unwrap();
        assert_eq!(body(&rule), Vec::<String>::new());
    }

    #[test]
    fn test_body_items_inline_recipe() {
        let rule: Rule = "all: dep ; echo a\n\techo b\n".parse().unwrap();
        assert_eq!(body(&rule), vec!["0: echo a", "1: echo b"]);
        let first = match rule.body_items().next() {
            Some(ConditionalItem::Recipe(r)) => r,
            _ => panic!("expected recipe"),
        };
        assert_eq!(first.indent(), None);
    }

    #[test]
    fn test_body_items_conditional() {
        let rule: Rule = "all:\n\techo a\nifdef X\n\techo b\nelse\n\t@echo c\nendif\n\techo d\n"
            .parse()
            .unwrap();
        assert_eq!(
            body(&rule),
            vec![
                "1: echo a",
                "ifdef [3: echo b] else [5: @echo c]",
                "7: echo d"
            ]
        );
        assert_eq!(
            rule.items()
                .map(|item| match item {
                    RuleItem::Recipe(text) => text,
                    RuleItem::Conditional(_) => "conditional".to_string(),
                })
                .collect::<Vec<_>>(),
            vec!["echo a", "conditional", "echo d"]
        );
    }

    #[test]
    fn test_body_items_nested_conditionals() {
        let rule: Rule =
            "all: ; echo a\nifdef X\n\techo b\nifeq ($(Y),1)\n\techo c\nendif\nendif\n\techo d\n"
                .parse()
                .unwrap();
        assert_eq!(
            body(&rule),
            vec![
                "0: echo a",
                "ifdef [2: echo b, ifeq [4: echo c]]",
                "7: echo d"
            ]
        );
    }

    #[test]
    fn test_body_items_bsd() {
        let makefile = Makefile::parse_with_variant(
            "all:\n\techo a\n.if defined(X)\n\techo b\n.endif\n.for f in a b\n\techo ${f}\n.endfor\n\techo c\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            body(&rule),
            vec![
                "1: echo a",
                ".if [3: echo b]",
                ".for [6: echo ${f}]",
                "8: echo c"
            ]
        );
    }

    #[test]
    fn test_body_items_bsd_directives() {
        let makefile = Makefile::parse_with_variant(
            "all:\n\techo a\n.info hi\n\techo b\n.include \"x.mk\"\n\techo c\n",
            MakefileVariant::BSDMake,
        )
        .tree();
        let rule = makefile.rules().next().unwrap();
        let items: Vec<String> = rule
            .body_items()
            .map(|item| match item {
                ConditionalItem::Item(MakefileItem::Directive(d)) => d.keyword().unwrap(),
                ConditionalItem::Item(MakefileItem::Include(i)) => i.path().unwrap(),
                item => describe_body_item(item),
            })
            .collect();
        assert_eq!(
            items,
            vec!["1: echo a", ".info", "3: echo b", "x.mk", "5: echo c"]
        );
        assert_eq!(recipes(&rule), vec!["echo a", "echo b", "echo c"]);
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
    fn test_target_literal_text_around_reference() {
        let cases: &[(&str, &[&str])] = &[
            ("pre${X}}: dep\n", &["pre${X}}"]),
            ("${:Ua}}: dep\n", &["${:Ua}}"]),
            ("pre$(X)): dep\n", &["pre$(X))"]),
            ("${X}}x y: dep\n", &["${X}}x", "y"]),
            ("a) b: dep\n", &["a)", "b"]),
            ("a}b x: dep\n", &["a}b", "x"]),
            ("a, b: dep\n", &["a,", "b"]),
            ("a\"b: dep\n", &["a\"b"]),
        ];
        for (input, expected) in cases {
            let mut parsed = vec![Makefile::parse(input)];
            for variant in [
                crate::MakefileVariant::GNUMake,
                crate::MakefileVariant::BSDMake,
                crate::MakefileVariant::POSIXMake,
                crate::MakefileVariant::NMake,
            ] {
                parsed.push(Makefile::parse_with_variant(input, variant));
            }
            for parsed in parsed {
                assert_eq!(parsed.errors(), &[], "{input:?}");
                let makefile = parsed.tree();
                let rule = makefile.rules().next().unwrap();
                assert_eq!(targets(&rule), *expected, "{input:?}");
                assert_eq!(prereqs(&rule), (vec!["dep".to_string()], vec![]));
                assert_eq!(makefile.to_string(), *input);
            }
        }
    }

    #[test]
    fn test_prerequisite_literal_text_around_reference() {
        let input = "all: a${X}b ${X}} | ${Y})c\n";
        let rule: Rule = input.parse().unwrap();
        assert_eq!(
            prereqs(&rule),
            (
                vec!["a${X}b".to_string(), "${X}}".to_string()],
                vec!["${Y})c".to_string()]
            )
        );
        assert_eq!(rule.to_string(), input);
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

    #[test]
    fn test_recipe_prefix() {
        let text = ".RECIPEPREFIX = >\nall:\n> echo one\n>echo two\n\tx = 1\n.RECIPEPREFIX :=\nb:\n\techo b\n";
        let parsed = Makefile::parse_with_variant(text, crate::MakefileVariant::GNUMake);
        assert!(parsed.ok(), "{:?}", parsed.errors());
        let makefile = parsed.tree();
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 2);
        assert_eq!(
            rules[0].recipes().collect::<Vec<_>>(),
            vec![" echo one", "echo two"]
        );
        assert_eq!(rules[1].recipes().collect::<Vec<_>>(), vec!["echo b"]);
        let names: Vec<_> = makefile
            .variable_definitions()
            .filter_map(|v| v.name())
            .collect();
        assert_eq!(names, vec![".RECIPEPREFIX", "x", ".RECIPEPREFIX"]);
        assert_eq!(makefile.to_string(), text);

        // Only GNU make has `.RECIPEPREFIX`.
        for variant in [
            crate::MakefileVariant::BSDMake,
            crate::MakefileVariant::POSIXMake,
            crate::MakefileVariant::NMake,
        ] {
            let parsed = Makefile::parse_with_variant(text, variant);
            assert!(!parsed.ok(), "{variant:?}");
        }
    }

    /// Parse `text` as `variant`, check it round trips without errors and
    /// return the targets and prerequisites of its single rule.
    fn parse_rule_names(text: &str, variant: crate::MakefileVariant) -> (Vec<String>, Vec<String>) {
        let parsed = Makefile::parse_with_variant(text, variant);
        assert!(parsed.ok(), "{text:?}: {:?}", parsed.errors());
        let makefile = parsed.tree();
        assert_eq!(makefile.to_string(), text);
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 1, "{text:?}");
        (targets(&rules[0]), rules[0].prerequisites().collect())
    }

    #[test]
    fn test_target_backslash() {
        for variant in [
            crate::MakefileVariant::GNUMake,
            crate::MakefileVariant::POSIXMake,
            crate::MakefileVariant::BSDMake,
        ] {
            for (text, expected) in [
                ("a\\b: x\n", vec!["a\\b"]),
                ("\\foo: x\n", vec!["\\foo"]),
                ("a\\\\b: x\n", vec!["a\\\\b"]),
                ("a\\b c\\d: x\n", vec!["a\\b", "c\\d"]),
                ("a\\ b: x\n", vec!["a\\ b"]),
                ("a\\  b: x\n", vec!["a\\ ", "b"]),
                ("a\\:b: x\n", vec!["a\\:b"]),
                ("a\\\\ b: x\n", vec!["a\\\\", "b"]),
                ("a\\\\\\:: x\n", vec!["a\\\\\\:"]),
                ("a\\\\: x\n", vec!["a\\\\"]),
                ("a\\b \\\n c: x\n", vec!["a\\b", "c"]),
                ("a\\\\\\\n c: x\n", vec!["a\\\\", "c"]),
            ] {
                assert_eq!(
                    parse_rule_names(text, variant),
                    (
                        expected.into_iter().map(String::from).collect(),
                        vec!["x".to_string()]
                    ),
                    "{variant:?} {text:?}"
                );
            }
        }
    }

    #[test]
    fn test_prerequisite_escaped_space() {
        // GNU make takes `\ ` as part of the name, BSD make splits source
        // names at any whitespace.
        let text = "all: a\\b c\\ d e\\:f\n";
        for variant in [
            crate::MakefileVariant::GNUMake,
            crate::MakefileVariant::POSIXMake,
        ] {
            assert_eq!(
                parse_rule_names(text, variant).1,
                vec!["a\\b", "c\\ d", "e\\:f"],
                "{variant:?}"
            );
        }
        assert_eq!(
            parse_rule_names(text, crate::MakefileVariant::BSDMake).1,
            vec!["a\\b", "c\\", "d", "e\\:f"]
        );
    }

    #[test]
    fn test_rule_accessors_for_variant() {
        let text = "$(subst a \\\n  b,c,a  b) all: $(X:a \\\n  b=c): \\\n  \
                    x$(subst a \\\n  b,c,a  b) | $(subst a \\\n  b,c,a  b)\n";
        let makefile: Makefile = text.parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            rule.targets().collect::<Vec<_>>(),
            vec!["$(subst a b,c,a  b)", "all"]
        );
        assert_eq!(
            rule.targets_for(MakefileVariant::GNUMake)
                .collect::<Vec<_>>(),
            vec!["$(subst a b,c,a  b)", "all"]
        );
        assert_eq!(
            rule.targets_for(MakefileVariant::POSIXMake)
                .collect::<Vec<_>>(),
            vec!["$(subst a  b,c,a  b)", "all"]
        );
        assert_eq!(rule.static_pattern(), Some("$(X:a b=c)".to_string()));
        assert_eq!(
            rule.static_pattern_for(MakefileVariant::POSIXMake),
            Some("$(X:a  b=c)".to_string())
        );
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["x$(subst a b,c,a  b)"]
        );
        assert_eq!(
            rule.prerequisites_for(MakefileVariant::POSIXMake)
                .collect::<Vec<_>>(),
            vec!["x$(subst a  b,c,a  b)"]
        );
        assert_eq!(
            rule.order_only_prerequisites().collect::<Vec<_>>(),
            vec!["$(subst a b,c,a  b)"]
        );
        assert_eq!(
            rule.order_only_prerequisites_for(MakefileVariant::POSIXMake)
                .collect::<Vec<_>>(),
            vec!["$(subst a  b,c,a  b)"]
        );
    }

    #[test]
    fn test_rule_accessors_for_bsd() {
        let text = "${A:S/a/b/ \\\n\t:S/c/d/}: ${B:S/a/b/ \\\n\t:S/c/d/}\n";
        let parsed = Makefile::parse_with_variant(text, MakefileVariant::BSDMake);
        assert!(parsed.ok(), "{:?}", parsed.errors());
        let rule = parsed.tree().rules().next().unwrap();
        assert_eq!(
            rule.targets_for(MakefileVariant::BSDMake)
                .collect::<Vec<_>>(),
            vec!["${A:S/a/b/  :S/c/d/}"]
        );
        assert_eq!(
            rule.prerequisites_for(MakefileVariant::BSDMake)
                .collect::<Vec<_>>(),
            vec!["${B:S/a/b/  :S/c/d/}"]
        );
    }

    #[test]
    fn test_rule_names_unescape_hash() {
        let text = "a\\#b c\\\\\\#d: e\\#f g\\\\\\#h $(subst \\#,x,y) | o\\#p\n";
        let gnu = [
            vec!["a#b", "c\\#d"],
            vec!["e#f", "g\\#h", "$(subst \\#,x,y)"],
            vec!["o#p"],
        ];
        let bsd = [
            vec!["a#b", "c\\\\#d"],
            vec!["e#f", "g\\\\#h", "$(subst #,x,y)"],
            vec!["o#p"],
        ];
        let as_written = [
            vec!["a\\#b", "c\\\\\\#d"],
            vec!["e\\#f", "g\\\\\\#h", "$(subst \\#,x,y)"],
            vec!["o\\#p"],
        ];
        for parsed in [
            Makefile::parse(text),
            Makefile::parse_with_variant(text, MakefileVariant::GNUMake),
        ] {
            assert!(parsed.ok(), "{:?}", parsed.errors());
            let makefile = parsed.tree();
            assert_eq!(makefile.to_string(), text);
            let rule = makefile.rules().next().unwrap();
            let names = |variant: Option<MakefileVariant>| match variant {
                Some(v) => [
                    rule.targets_for(v).collect::<Vec<_>>(),
                    rule.prerequisites_for(v).collect(),
                    rule.order_only_prerequisites_for(v).collect(),
                ],
                None => [
                    rule.targets().collect(),
                    rule.prerequisites().collect(),
                    rule.order_only_prerequisites().collect(),
                ],
            };
            assert_eq!(names(None), gnu);
            assert_eq!(names(Some(MakefileVariant::GNUMake)), gnu);
            assert_eq!(names(Some(MakefileVariant::POSIXMake)), gnu);
            assert_eq!(names(Some(MakefileVariant::BSDMake)), bsd);
            assert_eq!(names(Some(MakefileVariant::NMake)), as_written);
        }

        let text = "a\\#b c\\\\\\#d: e\\#f g\\\\\\#h\n";
        for (variant, expected) in [
            (
                MakefileVariant::POSIXMake,
                [vec!["a#b", "c\\#d"], vec!["e#f", "g\\#h"]],
            ),
            (
                MakefileVariant::BSDMake,
                [vec!["a#b", "c\\\\#d"], vec!["e#f", "g\\\\#h"]],
            ),
        ] {
            let parsed = Makefile::parse_with_variant(text, variant);
            assert!(parsed.ok(), "{variant:?}: {:?}", parsed.errors());
            let makefile = parsed.tree();
            assert_eq!(makefile.to_string(), text);
            let rule = makefile.rules().next().unwrap();
            assert_eq!(
                [
                    rule.targets_for(variant).collect::<Vec<_>>(),
                    rule.prerequisites_for(variant).collect()
                ],
                expected,
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_static_pattern_unescape_hash() {
        let makefile: Makefile = "x\\#1: %\\#1: %\\#2\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(targets(&rule), vec!["x#1"]);
        assert_eq!(rule.static_pattern(), Some("%#1".to_string()));
        assert_eq!(
            rule.static_pattern_for(MakefileVariant::BSDMake),
            Some("%#1".to_string())
        );
        assert_eq!(
            rule.static_pattern_for(MakefileVariant::NMake),
            Some("%\\#1".to_string())
        );
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["%#2"]);
    }

    #[test]
    fn test_prerequisite_backslashes_before_comment() {
        // GNU make halves the backslashes before a comment, BSD make keeps
        // them.
        let makefile: Makefile = "a: b\\\\# c\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["b\\"]);
        assert_eq!(
            rule.prerequisites_for(MakefileVariant::BSDMake)
                .collect::<Vec<_>>(),
            vec!["b\\\\"]
        );
    }

    #[test]
    fn test_set_rule_names_escapes_hash() {
        let makefile: Makefile = "a: b\n".parse().unwrap();
        let mut rule = makefile.rules().next().unwrap();
        rule.set_targets(vec!["x#y", "p\\#q"]).unwrap();
        assert_eq!(makefile.to_string(), "x\\#y p\\\\\\#q: b\n");
        assert_eq!(targets(&rule), vec!["x#y", "p\\#q"]);
        rule.set_prerequisites(vec!["$(subst #,x,y)", "e#f"])
            .unwrap();
        assert_eq!(
            makefile.to_string(),
            "x\\#y p\\\\\\#q: $(subst #,x,y) e\\#f\n"
        );
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["$(subst #,x,y)", "e#f"]
        );
        rule.add_prerequisite("g#h").unwrap();
        assert_eq!(
            makefile.to_string(),
            "x\\#y p\\\\\\#q: $(subst #,x,y) e\\#f g\\#h\n"
        );
        assert!(rule.remove_prerequisite("e#f").unwrap());
        assert_eq!(
            makefile.to_string(),
            "x\\#y p\\\\\\#q: $(subst #,x,y) g\\#h\n"
        );
        assert!(rule.rename_target("x#y", "n#m").unwrap());
        assert_eq!(
            makefile.to_string(),
            "n\\#m p\\\\\\#q: $(subst #,x,y) g\\#h\n"
        );
        rule.add_target("z").unwrap();
        assert_eq!(
            makefile.to_string(),
            "n\\#m p\\\\\\#q z: $(subst #,x,y) g\\#h\n"
        );
        assert!(rule.remove_target("n#m").unwrap());
        assert_eq!(makefile.to_string(), "p\\\\\\#q z: $(subst #,x,y) g\\#h\n");
    }

    #[test]
    fn test_set_prerequisites_before_comment() {
        let makefile: Makefile = "a: b# c\n".parse().unwrap();
        let mut rule = makefile.rules().next().unwrap();
        rule.set_prerequisites(vec!["x\\"]).unwrap();
        assert_eq!(makefile.to_string(), "a: x\\\\# c\n");
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["x\\"]);
    }

    #[test]
    fn test_new_rule_escapes_hash() {
        let rule = Rule::new(&["a#b"], &["c#d", "e"], &["echo #"]);
        assert_eq!(rule.to_string(), "a\\#b: c\\#d e\n\techo #\n");
        assert_eq!(targets(&rule), vec!["a#b"]);
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["c#d", "e"]);

        let mut makefile = Makefile::new();
        let rule = makefile.add_rule("x#y");
        assert_eq!(makefile.to_string(), "x\\#y:\n");
        assert_eq!(targets(&rule), vec!["x#y"]);
    }

    #[test]
    fn test_set_rule_names_unrepresentable() {
        let makefile: Makefile = "a: b\n".parse().unwrap();
        let mut rule = makefile.rules().next().unwrap();
        assert!(rule.set_targets(vec!["x y"]).is_err());
        assert!(rule.set_targets(vec!["x:"]).is_err());
        assert!(rule.set_prerequisites(vec!["c | d"]).is_err());
        assert!(rule.set_prerequisites(vec!["c;d"]).is_err());
        assert_eq!(makefile.to_string(), "a: b\n");
    }

    #[test]
    fn test_recipe_continuation_lines_without_indent() {
        // As in intel-ipsec-mb's LibTestApp/Makefile. Both makes run
        // `echo a b,c,# d` (GNU make) as one command.
        let text = "style:\n\techo a \\\nb,\\\nc,\\\n# d\nall:\n";
        for variant in [
            crate::MakefileVariant::GNUMake,
            crate::MakefileVariant::BSDMake,
        ] {
            let parsed = Makefile::parse_with_variant(text, variant);
            assert_eq!(parsed.errors(), &[], "{variant:?}");
            let makefile = parsed.tree();
            let rules: Vec<_> = makefile.rules().collect();
            assert_eq!(rules.len(), 2, "{variant:?}");
            assert_eq!(
                rules[0].recipes().collect::<Vec<_>>(),
                vec!["echo a \\\nb,\\\nc,\\\n# d"],
                "{variant:?}"
            );
            assert_eq!(makefile.to_string(), text);
        }
    }

    #[test]
    fn test_recipe_line_ending_in_escaped_backslash() {
        // As in NetBSD make's escape.mk: both makes run two commands.
        let text = "x:\n\techo two\\\\\n\techo three\\\\\n";
        let makefile: Makefile = text.parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            rule.recipes().collect::<Vec<_>>(),
            vec!["echo two\\\\", "echo three\\\\"]
        );

        // A backslash followed by a space doesn't continue the line either.
        let makefile: Makefile = "x:\n\techo a \\ \n\techo b\n".parse().unwrap();
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            rule.recipes().collect::<Vec<_>>(),
            vec!["echo a \\ ", "echo b"]
        );
    }
}
