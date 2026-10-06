use super::*;

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
    /// body of a `define` block, which is kept as raw text; see
    /// [`VariableDefinition::define_variable_references`].
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
    /// single-character references such as `$@`, returns that character.
    ///
    /// Returns `None` for expressions without a variable name, such as BSD
    /// make's `${:Uvalue}`.
    ///
    /// Note: Variable references inside recipes and `define` bodies are not
    /// parsed into the syntax tree (they are stored as raw text). This only
    /// finds references in variable values, prerequisites, and targets.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "CFLAGS = $(BASE_FLAGS) -Wall\n".parse().unwrap();
    /// let refs: Vec<_> = makefile.variable_references().collect();
    /// assert_eq!(refs[0].name(), Some("BASE_FLAGS".to_string()));
    /// ```
    pub fn name(&self) -> Option<String> {
        let mut children = self.0.children_with_tokens().skip(1);
        let open = children.next()?;
        if !matches!(open.kind(), LPAREN | LBRACE) {
            // A single-character reference such as `$@` or `$X`
            return open.into_token()?.text().chars().next().map(String::from);
        }
        let mut name = String::new();
        for child in children {
            match child.kind() {
                RPAREN | RBRACE | WHITESPACE | COMMA | OPERATOR | NEWLINE => break,
                _ => name.push_str(&child.to_string()),
            }
        }
        if name.is_empty() {
            None
        } else {
            Some(name)
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
    /// [`crate::ParsedReference::parse`]. For BSD make, parse the makefile
    /// with [`crate::MakefileVariant::BSDMake`] as well: otherwise the
    /// reference may end at the wrong place, as described for
    /// [`Makefile::parse`].
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
    ///         Modifier::Match("*.c".to_string()),
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
        crate::ParsedReference::parse(&self.0.text().to_string(), variant)
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

impl core::fmt::Display for VariableReference {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{}", self.0.text())
    }
}
