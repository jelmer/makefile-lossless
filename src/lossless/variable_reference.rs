use super::*;
use crate::ConditionalBranch;

/// A reference to a variable in the makefile, e.g. `$(FOO)` or `${BAR}`.
///
/// This wraps an EXPR syntax node whose first token is `$` followed by `(` or `{`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct VariableReference(SyntaxNode);

impl VariableReference {
    /// Try to cast a syntax node into a VariableReference.
    ///
    /// Returns `Some` if the node is an EXPR whose first token is `$` followed by
    /// `(`, `{`, or an identifier (for single-character variables like `$X`).
    /// An escaped dollar sign (`$$`) is not a reference, and neither is the
    /// EXPR holding the body of a `define` block, which may start with a
    /// `$`.
    pub fn cast(syntax: SyntaxNode) -> Option<Self> {
        if syntax.kind() != EXPR {
            return None;
        }
        if syntax
            .parent()
            .and_then(VariableDefinition::cast)
            .is_some_and(|v| v.is_define() && v.value_expr().as_ref() == Some(&syntax))
        {
            return None;
        }
        let mut tokens = syntax
            .children_with_tokens()
            .filter_map(|it| it.into_token());
        let first = tokens.next()?;
        if first.kind() != DOLLAR {
            return None;
        }
        // Accept $(...), ${...}, or $X (single-char)
        if tokens.next()?.kind() == DOLLAR {
            return None;
        }
        Some(Self(syntax))
    }

    /// Get the syntax node backing this variable reference.
    pub fn syntax(&self) -> &SyntaxNode {
        &self.0
    }

    /// Get the name of the referenced variable.
    ///
    /// For simple references like `$(FOO)`, returns `"FOO"`.
    /// For function calls like `$(wildcard *.c)`, returns `"wildcard"`.
    /// Modifiers are not part of the name, so `${SRCS:M*.c}` returns
    /// `"SRCS"`, while nested references are, as in `${VAR.${M}}`. For
    /// single-character references such as `$@`, returns that character,
    /// and for nmake's `$**`, `"**"`.
    ///
    /// Returns `None` for expressions without a variable name, such as BSD
    /// make's `${:Uvalue}`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "CFLAGS = $(BASE_FLAGS) -Wall\n".parse().unwrap();
    /// let refs: Vec<_> = makefile.variable_references().collect();
    /// assert_eq!(refs[0].name(), Some("BASE_FLAGS".to_string()));
    /// ```
    pub fn name(&self) -> Option<String> {
        let elements = self.name_elements();
        if !self.is_delimited() {
            // A single-character reference such as `$@` or `$X`, or nmake's
            // `$**`
            return Some(elements.first()?.as_token()?.text().to_string());
        }
        let name: String = elements.iter().map(|it| it.to_string()).collect();
        if name.is_empty() {
            None
        } else {
            Some(name)
        }
    }

    /// Internal: whether this is delimited by parentheses or braces, rather
    /// than a single-character reference.
    fn is_delimited(&self) -> bool {
        self.0
            .children_with_tokens()
            .nth(1)
            .is_some_and(|it| matches!(it.kind(), LPAREN | LBRACE))
    }

    /// Internal: the elements making up the name, which ends at the closing
    /// delimiter, whitespace, a comma or an operator such as the `:` before
    /// modifiers. For a single-character reference this is the token after
    /// the `$`.
    fn name_elements(&self) -> Vec<SyntaxElement> {
        let mut children = self.0.children_with_tokens().skip(1);
        if !self.is_delimited() {
            return children.next().into_iter().collect();
        }
        children
            .skip(1)
            .take_while(|child| {
                !matches!(
                    child.kind(),
                    RPAREN | RBRACE | WHITESPACE | COMMA | OPERATOR | NEWLINE
                )
            })
            .collect()
    }

    /// The source range of the name, covering the same text as
    /// [`Self::name`].
    ///
    /// For a function call this is the function name, and for a
    /// single-character reference such as `$@` the text after the `$`.
    /// Returns `None` if [`Self::name`] does.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "X = ${SRCS:.c=.o} $(FOO.$(BAR)) $@\n".parse().unwrap();
    /// let ranges: Vec<_> = makefile
    ///     .variable_references()
    ///     .map(|r| r.name_range())
    ///     .collect();
    /// assert_eq!(
    ///     ranges,
    ///     vec![
    ///         Some(TextRange::new(6.into(), 10.into())),
    ///         Some(TextRange::new(20.into(), 30.into())),
    ///         Some(TextRange::new(26.into(), 29.into())),
    ///         Some(TextRange::new(33.into(), 34.into())),
    ///     ]
    /// );
    /// ```
    pub fn name_range(&self) -> Option<rowan::TextRange> {
        let elements = self.name_elements();
        if !self.is_delimited() {
            return Some(elements.first()?.as_token()?.text_range());
        }
        let first = elements.first()?.text_range();
        let last = elements.last()?.text_range();
        Some(first.cover(last))
    }

    /// The innermost reference this one is nested in, as the function call
    /// `$(dir $(FILE))` is for `$(FILE)` or `$(FOO.$(BAR))` for `$(BAR)`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "X = $(dir $(FILE)) $(Y)\n".parse().unwrap();
    /// let parents: Vec<_> = makefile
    ///     .variable_references()
    ///     .map(|r| r.parent_reference().map(|p| p.to_string()))
    ///     .collect();
    /// assert_eq!(parents, vec![None, Some("$(dir $(FILE))".to_string()), None]);
    /// ```
    pub fn parent_reference(&self) -> Option<VariableReference> {
        self.0.ancestors().skip(1).find_map(VariableReference::cast)
    }

    /// Where this reference is: in which part of the enclosing reference, if
    /// it is nested in one, or otherwise in which part of which makefile
    /// item.
    ///
    /// For a nested reference, call `location()` on the enclosing reference
    /// in turn to find out where that one is.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, ReferenceLocation};
    /// let makefile: Makefile = "$(OBJS): $(SRCS)\nX := $(dir $(FILE))\n".parse().unwrap();
    /// let locations: Vec<_> = makefile
    ///     .variable_references()
    ///     .map(|r| match r.location() {
    ///         ReferenceLocation::Target(_) => "target",
    ///         ReferenceLocation::Prerequisite(_) => "prerequisite",
    ///         ReferenceLocation::VariableValue(_) => "value",
    ///         ReferenceLocation::FunctionArgument(_) => "argument",
    ///         _ => "other",
    ///     })
    ///     .collect();
    /// assert_eq!(locations, vec!["target", "prerequisite", "value", "argument"]);
    /// ```
    pub fn location(&self) -> ReferenceLocation {
        let mut child = self.0.clone();
        for ancestor in self.0.ancestors().skip(1) {
            if let Some(outer) = VariableReference::cast(ancestor.clone()) {
                return outer.location_of_child(&child);
            }
            let location = match ancestor.kind() {
                EXPR | PREREQUISITE | ARCHIVE_MEMBERS | ARCHIVE_MEMBER => {
                    child = ancestor;
                    continue;
                }
                TARGETS => ancestor
                    .parent()
                    .and_then(Rule::cast)
                    .map(ReferenceLocation::Target),
                TARGET_PATTERN => ancestor
                    .parent()
                    .and_then(Rule::cast)
                    .map(ReferenceLocation::TargetPattern),
                PREREQUISITES => ancestor
                    .parent()
                    .and_then(Rule::cast)
                    .map(ReferenceLocation::Prerequisite),
                VARIABLE => VariableDefinition::cast(ancestor.clone()).map(|var| {
                    if var.value_expr().as_ref() != Some(&child) {
                        ReferenceLocation::VariableName(var)
                    } else if ancestor.parent().is_some_and(|p| p.kind() == RULE) {
                        ReferenceLocation::TargetSpecificValue(var)
                    } else {
                        ReferenceLocation::VariableValue(var)
                    }
                }),
                CONDITIONAL_IF | CONDITIONAL_ELSE => ancestor
                    .parent()
                    .and_then(Conditional::cast)
                    .and_then(|cond| {
                        let index = cond
                            .syntax()
                            .children()
                            .filter(|it| matches!(it.kind(), CONDITIONAL_IF | CONDITIONAL_ELSE))
                            .position(|it| it == ancestor)?;
                        cond.branches().nth(index)
                    })
                    .map(ReferenceLocation::Condition),
                RECIPE => Recipe::cast(ancestor).map(ReferenceLocation::Recipe),
                INCLUDE => Include::cast(ancestor).map(ReferenceLocation::Include),
                VPATH => Vpath::cast(ancestor).map(ReferenceLocation::Vpath),
                LOAD => Load::cast(ancestor).map(ReferenceLocation::Load),
                EXPRESSION_STATEMENT => {
                    ExpressionStatement::cast(ancestor).map(ReferenceLocation::ExpressionStatement)
                }
                FOR_HEADER => ancestor
                    .parent()
                    .and_then(ForLoop::cast)
                    .map(ReferenceLocation::ForLoop),
                DIRECTIVE => Directive::cast(ancestor).map(ReferenceLocation::Directive),
                _ => None,
            };
            return location.unwrap_or(ReferenceLocation::Other);
        }
        ReferenceLocation::Other
    }

    /// The archive member list this reference is in, as `$(OBJS)` in
    /// `lib.a($(OBJS))` or `$@` in `lib.a($@): x`.
    ///
    /// [`Self::location`] gives the [`ReferenceLocation::Target`] or
    /// [`ReferenceLocation::Prerequisite`] the member list is part of. Like
    /// [`Self::location`], this only looks at the innermost enclosing item:
    /// a reference nested in another one, as `$(X)` in
    /// `lib.a($(addsuffix .o,$(X)))`, returns `None`, and so does a
    /// reference in the archive name, as in `$(LIB)(m.o)`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "$(LIB)($(OBJS)): x\n".parse().unwrap();
    /// let members: Vec<_> = makefile
    ///     .variable_references()
    ///     .map(|r| r.archive_members().map(|m| m.member_names()))
    ///     .collect();
    /// assert_eq!(members, vec![None, Some(vec!["$(OBJS)".to_string()])]);
    /// ```
    pub fn archive_members(&self) -> Option<ArchiveMembers> {
        self.0
            .ancestors()
            .skip(1)
            .take_while(|it| {
                VariableReference::cast(it.clone()).is_none()
                    && matches!(
                        it.kind(),
                        EXPR | PREREQUISITE | ARCHIVE_MEMBERS | ARCHIVE_MEMBER
                    )
            })
            .find_map(ArchiveMembers::cast)
    }

    /// Internal: the location of `child`, a child node of this reference
    /// containing a nested reference.
    fn location_of_child(&self, child: &SyntaxNode) -> ReferenceLocation {
        let in_name = self
            .name_elements()
            .iter()
            .any(|it| it.as_node() == Some(child));
        if in_name {
            ReferenceLocation::ReferenceName(self.clone())
        } else if self.is_function_call() {
            ReferenceLocation::FunctionArgument(self.clone())
        } else {
            ReferenceLocation::Modifier(self.clone())
        }
    }

    /// Check if this is a function call rather than a simple variable reference.
    ///
    /// Returns `true` if the content after the function name contains whitespace
    /// or commas, indicating arguments (e.g. `$(subst a,b,text)` vs `$(CC)`).
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "FILES = $(wildcard *.c)\n".parse().unwrap();
    /// let refs: Vec<_> = makefile.variable_references().collect();
    /// assert!(refs[0].is_function_call());
    /// ```
    pub fn is_function_call(&self) -> bool {
        let mut tokens = self
            .0
            .children_with_tokens()
            .filter_map(|it| it.into_token());

        // Skip $ and opening paren/brace
        let Some(dollar) = tokens.next() else {
            return false;
        };
        if dollar.kind() != DOLLAR {
            return false;
        }
        let Some(open) = tokens.next() else {
            return false;
        };
        if open.kind() != LPAREN && open.kind() != LBRACE {
            return false;
        }

        // Skip the function name (first IDENTIFIER)
        let Some(ident) = tokens.next() else {
            return false;
        };
        if ident.kind() != IDENTIFIER {
            return false;
        }

        // If the next token is whitespace or comma, it's a function call
        match tokens.next() {
            Some(t) => t.kind() == WHITESPACE || t.kind() == COMMA,
            None => false,
        }
    }

    /// Count the number of comma-separated arguments in a function call.
    ///
    /// Returns 0 for simple variable references. For function calls, counts
    /// the commas at depth 0 (not inside nested parentheses) plus 1.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "X = $(subst a,b,text)\n".parse().unwrap();
    /// let refs: Vec<_> = makefile.variable_references().collect();
    /// assert_eq!(refs[0].argument_count(), 3);
    /// ```
    pub fn argument_count(&self) -> usize {
        if !self.is_function_call() {
            return 0;
        }

        let mut commas = 0;
        let mut depth = 0;
        let mut past_name = false;

        for element in self.0.children_with_tokens() {
            let Some(token) = element.as_token() else {
                // Child nodes (nested EXPR) don't contain top-level commas
                continue;
            };
            match token.kind() {
                IDENTIFIER if !past_name => {
                    past_name = true;
                }
                DOLLAR | LPAREN | LBRACE if !past_name => {}
                LPAREN => depth += 1,
                RPAREN if depth > 0 => depth -= 1,
                COMMA if depth == 0 && past_name => commas += 1,
                _ => {}
            }
        }

        if past_name {
            commas + 1
        } else {
            0
        }
    }

    /// Determine which argument (0-based) the given byte offset falls into.
    ///
    /// Returns `None` if the offset is not inside this reference or if this
    /// is not a function call.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "X = $(subst a,b,text)\n".parse().unwrap();
    /// let refs: Vec<_> = makefile.variable_references().collect();
    /// // offset 12 is 'a' (first arg), offset 14 is 'b' (second arg), offset 16 is 't' (third arg)
    /// assert_eq!(refs[0].argument_index_at_offset(12), Some(0));
    /// assert_eq!(refs[0].argument_index_at_offset(14), Some(1));
    /// assert_eq!(refs[0].argument_index_at_offset(16), Some(2));
    /// ```
    pub fn argument_index_at_offset(&self, offset: usize) -> Option<usize> {
        if !self.is_function_call() {
            return None;
        }

        let ref_start: usize = self.0.text_range().start().into();
        let ref_end: usize = self.0.text_range().end().into();
        if offset < ref_start || offset > ref_end {
            return None;
        }

        let mut arg_index = 0;
        let mut depth = 0;
        let mut past_name = false;

        for element in self.0.children_with_tokens() {
            let Some(token) = element.as_token() else {
                continue;
            };
            let token_end: usize = token.text_range().end().into();

            match token.kind() {
                IDENTIFIER if !past_name => {
                    past_name = true;
                }
                DOLLAR | LPAREN | LBRACE if !past_name => {}
                LPAREN => depth += 1,
                RPAREN if depth > 0 => depth -= 1,
                COMMA if depth == 0 && past_name => {
                    if offset < token_end {
                        return Some(arg_index);
                    }
                    arg_index += 1;
                }
                _ => {}
            }
        }

        if past_name {
            Some(arg_index)
        } else {
            None
        }
    }

    /// Parse this reference into the variable name and its modifiers.
    ///
    /// The variant determines which modifiers are recognized; see
    /// [`crate::ParsedReference::parse`]. Error offsets are relative to the
    /// start of the reference.
    ///
    /// For [`crate::MakefileVariant::BSDMake`], the reference is parsed in
    /// the context of the rest of its logical line, as the makefile parser
    /// does: make only treats a modifier as a SysV substitution if a closing
    /// brace follows, and looks for it past the end of the reference, so
    /// `${S:a=b{}}` is the reference `${S:a=b{}` followed by `}`. Parse the
    /// makefile with [`crate::MakefileVariant::BSDMake`] as well: otherwise
    /// the reference may end at the wrong place, as described for
    /// [`Makefile::parse`], and this returns an error.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant, Modifier, ModifierArg};
    /// let makefile = Makefile::parse_with_variant(
    ///     "OBJS = ${SRCS:M*.c:.c=.o}\n",
    ///     MakefileVariant::BSDMake,
    /// )
    /// .tree();
    /// let refs: Vec<_> = makefile.variable_references().collect();
    /// let parsed = refs[0].parse(MakefileVariant::BSDMake).unwrap();
    /// assert_eq!(parsed.name, "SRCS");
    /// assert_eq!(
    ///     parsed.modifiers,
    ///     vec![
    ///         Modifier::Match(ModifierArg::literal("*.c")),
    ///         Modifier::SysVSubstitute {
    ///             from: ModifierArg::literal(".c"),
    ///             to: ModifierArg::literal(".o"),
    ///         },
    ///     ]
    /// );
    /// ```
    pub fn parse(
        &self,
        variant: crate::MakefileVariant,
    ) -> Result<crate::ParsedReference, crate::ReferenceError> {
        if variant != crate::MakefileVariant::BSDMake {
            return crate::ParsedReference::parse(&self.0.text().to_string(), variant);
        }
        let tokens = std::iter::successors(self.0.first_token(), |t| t.next_token())
            .map(|t| (t.kind(), t.text().to_string(), t.text_range()));
        let (line, starts, _) = super::parser::bsd_logical_line(tokens, false);
        let start = self.0.text_range().start();
        let end = self.0.text_range().end();
        let len = starts
            .iter()
            .find(|(pos, _)| *pos == end)
            .map_or(line.len(), |(_, offset)| *offset);
        // The offset relative to the start of the reference in the source
        // corresponding to `offset` in `line`.
        let source_offset = |offset: usize| {
            let i = starts
                .partition_point(|(_, o)| *o <= offset)
                .saturating_sub(1);
            starts
                .get(i)
                .map_or(offset, |(pos, o)| usize::from(*pos - start) + (offset - o))
        };
        let (parsed, parsed_len) = crate::ParsedReference::parse_prefix(&line, variant)
            .map_err(|e| e.map_offset(source_offset))?;
        match parsed_len.cmp(&len) {
            std::cmp::Ordering::Equal => Ok(parsed),
            std::cmp::Ordering::Less => Err(crate::reference::syntax_error(
                source_offset(parsed_len),
                crate::ReferenceSyntaxErrorKind::TrailingText,
                "unexpected text after reference",
            )),
            std::cmp::Ordering::Greater => Err(crate::reference::syntax_error(
                usize::from(end - start),
                crate::ReferenceSyntaxErrorKind::UnclosedExpression,
                "reference continues past the end of the syntax node",
            )),
        }
    }

    /// Get the line number (0-indexed) where this reference starts.
    pub fn line(&self) -> usize {
        line_col_at_offset(&self.0, self.0.text_range().start()).0
    }

    /// Get the column number (0-indexed, in bytes) where this reference starts.
    pub fn column(&self) -> usize {
        line_col_at_offset(&self.0, self.0.text_range().start()).1
    }

    /// Get both line and column (0-indexed) where this reference starts.
    pub fn line_col(&self) -> (usize, usize) {
        line_col_at_offset(&self.0, self.0.text_range().start())
    }

    /// Get the text range of this reference in the source.
    pub fn text_range(&self) -> rowan::TextRange {
        self.0.text_range()
    }
}

/// Where a [`VariableReference`] is, as returned by
/// [`VariableReference::location`].
///
/// A reference nested in another one gives the part of that reference it is
/// in. Otherwise it gives the part of the makefile item that contains it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ReferenceLocation {
    /// In an argument of a function call, as `$(SRCS)` in
    /// `$(patsubst %.c,%.o,$(SRCS))`. Like
    /// [`VariableReference::is_function_call`], this goes by the syntax, so
    /// it also covers `$(FOO $(BAR))` if `FOO` is not a function.
    FunctionArgument(VariableReference),
    /// In the name of another reference, which is computed: `$(BAR)` in
    /// `$(FOO.$(BAR))`.
    ReferenceName(VariableReference),
    /// In the modifiers of another reference, as in the substitution
    /// reference `$(SRCS:.c=$(EXT))` or BSD make's `${SRCS:M${PATTERN}}`.
    Modifier(VariableReference),
    /// In the name of a variable assignment, `define`, `undefine` or
    /// `export` directive, including a target-specific one.
    VariableName(VariableDefinition),
    /// In the value of a variable assignment on its own line, including the
    /// body of a `define` block.
    VariableValue(VariableDefinition),
    /// In the value of a target-specific variable assignment on a rule line,
    /// as in `all: CFLAGS = $(OPT)`; see
    /// [`Rule::scoped_assignment`](crate::Rule::scoped_assignment).
    TargetSpecificValue(VariableDefinition),
    /// In the targets of a rule, including an archive member list as in
    /// `lib.a($(OBJS)): x`; see [`VariableReference::archive_members`].
    Target(Rule),
    /// In the target pattern of a static pattern rule, between the two
    /// colons.
    TargetPattern(Rule),
    /// In the prerequisites of a rule, including order-only ones and
    /// archive member lists; see [`VariableReference::archive_members`].
    Prerequisite(Rule),
    /// In a recipe line, including one after the `;` of a rule line and
    /// one outside any rule, as returned by
    /// [`MakefileItem::Recipe`](crate::MakefileItem::Recipe).
    Recipe(Recipe),
    /// In the condition of a conditional branch, such as `ifeq ($(A),b)`,
    /// `else ifdef $(B)`, `.if ${C}` or `!IF "$(D)" == "1"`.
    Condition(ConditionalBranch),
    /// In the file names of an include directive.
    Include(Include),
    /// In the pattern or directories of a `vpath` directive.
    Vpath(Vpath),
    /// In the objects of a `load` directive.
    Load(Load),
    /// In a line consisting of references only, such as `$(eval $(RULES))`.
    ExpressionStatement(ExpressionStatement),
    /// In the header of a BSD make `.for` loop.
    ForLoop(ForLoop),
    /// In the argument of a BSD make directive such as `.error` or `.undef`.
    Directive(Directive),
    /// Anywhere else, such as text the parser could not make sense of.
    Other,
}

impl core::fmt::Display for VariableReference {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{}", self.0.text())
    }
}

impl core::fmt::Debug for VariableReference {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        crate::lossless::debug_node(f, "VariableReference", &self.0)
    }
}
