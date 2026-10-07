use super::bsd::{directive_keyword, keyword_range, keyword_token};
use super::makefile::MakefileItem;
use super::{collapse_continuations, escape_hashes, is_continuation, logical_text, LineSyntax};
use crate::lex::NMAKE_ESCAPABLE;
use crate::lossless::{
    parse, remove_with_preceding_comments, Error, ErrorInfo, Include, Lang, ParseError,
};
use crate::MakefileVariant;
use crate::SyntaxKind::{
    BACKSLASH, COMMENT, EXPR, IDENTIFIER, INCLUDE, NEWLINE, OPERATOR, WHITESPACE,
};
use rowan::ast::AstNode;
use rowan::{GreenNodeBuilder, SyntaxNode, SyntaxToken};

/// Strip the `<...>` or `"..."` delimiters from a BSD make or nmake include
/// path.
///
/// Like BSD make, this ignores anything after the closing delimiter.
fn strip_delimiters(path: &str) -> Option<&str> {
    let (close, rest) = match path.chars().next()? {
        '<' => ('>', &path[1..]),
        '"' => ('"', &path[1..]),
        _ => return None,
    };
    rest.find(close).map(|end| &rest[..end])
}

/// Escape `path` for an nmake `!INCLUDE`: each `#` becomes `^#`, so that
/// it does not start a comment, a caret that would escape the next
/// character becomes `^^`, and a trailing backslash becomes `^\` so that
/// it does not continue the line.
fn escape_nmake(path: &str) -> String {
    let mut escaped = String::new();
    let mut chars = path.chars().peekable();
    while let Some(c) = chars.next() {
        let escape = match c {
            '#' => true,
            '^' => chars.peek().is_some_and(|n| NMAKE_ESCAPABLE.contains(n)),
            '\\' => chars.peek().is_none(),
            _ => false,
        };
        if escape {
            escaped.push('^');
        }
        escaped.push(c);
    }
    escaped
}

impl Include {
    /// Internal: a detached `include` directive for `path`, ending in `eol`.
    pub(crate) fn new(path: &str, eol: &str) -> Result<Include, Error> {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(INCLUDE.into());
        builder.token(IDENTIFIER.into(), "include");
        builder.token(WHITESPACE.into(), " ");
        builder.start_node(EXPR.into());
        builder.finish_node();
        builder.token(NEWLINE.into(), eol);
        builder.finish_node();
        let mut include = Include::cast(SyntaxNode::new_root_mut(builder.finish())).unwrap();
        include.set_path(path)?;
        Ok(include)
    }

    /// Internal: the token holding the include keyword and the keyword
    /// name without any dot, such as `-include`.
    fn keyword_name(&self) -> Option<(SyntaxToken<Lang>, String)> {
        let (token, keyword) = keyword_token(self.syntax())?;
        let name = keyword.trim_start_matches('.').to_string();
        Some((token, name))
    }

    /// The character before the name of a BSD make `.include` (`.`) or
    /// nmake `!INCLUDE` (`!`) directive, or `None` for GNU make.
    fn prefix(&self) -> Option<char> {
        directive_keyword(self.syntax())?
            .chars()
            .next()
            .filter(|c| matches!(c, '.' | '!'))
    }

    /// Whether this is a BSD make `.include` directive.
    fn is_bsd(&self) -> bool {
        self.prefix() == Some('.')
    }

    /// Whether this is a BSD make `.include` or nmake `!INCLUDE` directive,
    /// whose path may be delimited by `<...>` or `"..."`.
    fn has_delimited_path(&self) -> bool {
        self.prefix().is_some()
    }

    /// The EXPR node holding the path.
    fn path_expr(&self) -> Option<SyntaxNode<Lang>> {
        self.syntax().children().find(|it| it.kind() == EXPR)
    }

    /// Get the path of the include directive as make reads it, before
    /// expansion.
    ///
    /// Line continuations are collapsed and `\#` is unescaped the way
    /// BSD make does for `.include` and GNU make otherwise, while for an
    /// nmake `!INCLUDE` escapes such as `^#` are unescaped; see
    /// [`crate::VariableDefinition::value`] and [`Self::path_for`] for
    /// other variants. Variable references and backslashes before
    /// whitespace are kept, since make only handles them after expanding
    /// the path. For BSD make and nmake, the `<...>` or `"..."` delimiters
    /// around the path are removed. An `include` without any file names,
    /// which GNU make accepts, has an empty path.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = ".include <bsd.prog.mk>\ninclude a\\#b.mk\n".parse().unwrap();
    /// let paths: Vec<_> = makefile.includes().map(|i| i.path().unwrap()).collect();
    /// assert_eq!(paths, vec!["bsd.prog.mk", "a#b.mk"]);
    ///
    /// let makefile =
    ///     Makefile::parse_with_variant("!INCLUDE <win32.mak>\n", MakefileVariant::NMake).tree();
    /// let inc = makefile.includes().next().unwrap();
    /// assert_eq!(inc.path(), Some("win32.mak".to_string()));
    /// ```
    pub fn path(&self) -> Option<String> {
        let syntax = match self.prefix() {
            Some('.') => LineSyntax::Bsd,
            Some('!') => LineSyntax::NMake,
            _ => LineSyntax::Gnu,
        };
        self.path_with(syntax)
    }

    /// Get the path of the include directive as `variant` reads it, before
    /// expansion; see [`Self::path`].
    ///
    /// GNU make drops the whitespace before a line continuation, while
    /// POSIX make (and GNU make after `.POSIX:`) and BSD make keep it. This
    /// matters inside variable references, such as in function arguments
    /// or BSD make modifiers.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = "include $(subst a \\\n  b,c,a  b)\n".parse().unwrap();
    /// let inc = makefile.includes().next().unwrap();
    /// assert_eq!(
    ///     inc.path_for(MakefileVariant::GNUMake),
    ///     Some("$(subst a b,c,a  b)".to_string())
    /// );
    /// assert_eq!(
    ///     inc.path_for(MakefileVariant::POSIXMake),
    ///     Some("$(subst a  b,c,a  b)".to_string())
    /// );
    /// ```
    pub fn path_for(&self, variant: MakefileVariant) -> Option<String> {
        self.path_with(variant.into())
    }

    fn path_with(&self, syntax: LineSyntax) -> Option<String> {
        let expr = self.path_expr()?;
        let tokens = expr
            .descendants_with_tokens()
            .filter_map(|it| it.into_token());
        let text = logical_text(&expr, tokens, syntax, true);
        let path = text.trim();
        if self.has_delimited_path() {
            if let Some(inner) = strip_delimiters(path) {
                return Some(inner.to_string());
            }
        }
        Some(path.to_string())
    }

    /// The file names of this directive with their source ranges.
    fn path_words(&self) -> Vec<(rowan::TextRange, String)> {
        let Some(expr) = self.path_expr() else {
            return vec![];
        };
        if self.has_delimited_path() {
            let Some(path) = self.path().filter(|p| !p.is_empty()) else {
                return vec![];
            };
            let range = expr.text_range();
            let raw = expr.text().to_string();
            let range = match strip_delimiters(&raw) {
                Some(inner) => {
                    let start = range.start() + rowan::TextSize::from(1);
                    rowan::TextRange::at(start, rowan::TextSize::of(inner))
                }
                None => range,
            };
            return vec![(range, path)];
        }
        let mut words = vec![];
        let mut current: Vec<SyntaxToken<Lang>> = vec![];
        let mut backslashes = 0;
        for element in expr.children_with_tokens() {
            let escaped = backslashes % 2 == 1;
            backslashes = if element.kind() == BACKSLASH {
                backslashes + 1
            } else {
                0
            };
            if (element.kind() == WHITESPACE && !escaped) || is_continuation(&element) {
                if !current.is_empty() {
                    words.push(std::mem::take(&mut current));
                }
                continue;
            }
            match element {
                rowan::NodeOrToken::Token(token) => current.push(token),
                rowan::NodeOrToken::Node(n) => {
                    current.extend(n.descendants_with_tokens().filter_map(|it| it.into_token()))
                }
            }
        }
        if !current.is_empty() {
            words.push(current);
        }
        words
            .into_iter()
            .map(|tokens| {
                let range = tokens[0]
                    .text_range()
                    .cover(tokens[tokens.len() - 1].text_range());
                (range, logical_text(&expr, tokens, LineSyntax::Gnu, true))
            })
            .collect()
    }

    /// Get the file names of the include directive as make reads them,
    /// before expansion, one per file.
    ///
    /// Unlike [`Self::path`], which returns the whole list, this splits the
    /// path at whitespace outside variable references, as GNU make does
    /// after expanding it. Each name is read as for [`Self::path`]: `\#` is
    /// unescaped and a backslash-escaped space is kept as written, without
    /// splitting the name. A BSD make `.include` or nmake `!INCLUDE` names a
    /// single file, so it gives at most one name.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include a.mk $(DIR)/b\\#.mk \\\n  c.mk\n".parse().unwrap();
    /// let inc = makefile.includes().next().unwrap();
    /// assert_eq!(inc.path(), Some("a.mk $(DIR)/b#.mk c.mk".to_string()));
    /// assert_eq!(inc.paths().collect::<Vec<_>>(), vec!["a.mk", "$(DIR)/b#.mk", "c.mk"]);
    /// ```
    pub fn paths(&self) -> impl Iterator<Item = String> + '_ {
        self.path_words().into_iter().map(|(_, path)| path)
    }

    /// The source ranges of the file names of the include directive, in the
    /// same order as [`Self::paths`].
    ///
    /// Each range covers the name as written, including any escapes and
    /// variable references. For a BSD make or nmake path delimited by
    /// `<...>` or `"..."`, the range excludes the delimiters.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant, TextRange};
    /// let makefile: Makefile = "include a.mk  $(B)\n".parse().unwrap();
    /// let inc = makefile.includes().next().unwrap();
    /// assert_eq!(
    ///     inc.path_ranges().collect::<Vec<_>>(),
    ///     vec![
    ///         TextRange::new(8.into(), 12.into()),
    ///         TextRange::new(14.into(), 18.into()),
    ///     ]
    /// );
    ///
    /// let makefile =
    ///     Makefile::parse_with_variant(".include <a b.mk>\n", MakefileVariant::BSDMake).tree();
    /// let inc = makefile.includes().next().unwrap();
    /// assert_eq!(inc.paths().collect::<Vec<_>>(), vec!["a b.mk"]);
    /// assert_eq!(
    ///     inc.path_ranges().collect::<Vec<_>>(),
    ///     vec![TextRange::new(10.into(), 16.into())]
    /// );
    /// ```
    pub fn path_ranges(&self) -> impl Iterator<Item = rowan::TextRange> + '_ {
        self.path_words().into_iter().map(|(range, _)| range)
    }

    /// The path as written, including any delimiters, with line
    /// continuations collapsed.
    fn raw_path(&self) -> Option<String> {
        self.path_expr().map(|it| {
            collapse_continuations(&it, LineSyntax::Gnu)
                .trim()
                .to_string()
        })
    }

    /// Get the text range of the path portion of the include directive.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include config.mk\n".parse().unwrap();
    /// let inc = makefile.includes().next().unwrap();
    /// let range = inc.path_range().unwrap();
    /// assert_eq!(&makefile.to_string()[std::ops::Range::from(range)], "config.mk");
    /// ```
    pub fn path_range(&self) -> Option<rowan::TextRange> {
        self.path_expr().map(|it| it.text_range())
    }

    /// The include keyword, such as `include`, `-include` or `sinclude`.
    ///
    /// As for [`Directive::keyword`](crate::Directive::keyword), a BSD make
    /// keyword is normalized to a leading dot followed by the name, as in
    /// `.include` or `.-include`, and an nmake one to `!INCLUDE`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "-include a.mk\n. include \"b.mk\"\n".parse().unwrap();
    /// let keywords: Vec<_> = makefile.includes().map(|i| i.keyword()).collect();
    /// assert_eq!(keywords, vec![Some("-include".to_string()), Some(".include".to_string())]);
    /// ```
    pub fn keyword(&self) -> Option<String> {
        directive_keyword(self.syntax())
    }

    /// The source range of the include keyword, including a leading dot or
    /// `!` and any whitespace after it.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, TextRange};
    /// let makefile: Makefile = "sinclude a.mk\n".parse().unwrap();
    /// let include = makefile.includes().next().unwrap();
    /// assert_eq!(include.keyword_range(), Some(TextRange::new(0.into(), 8.into())));
    /// ```
    pub fn keyword_range(&self) -> Option<rowan::TextRange> {
        keyword_range(self.syntax())
    }

    /// Check if this is an optional include (-include or sinclude)
    ///
    /// For BSD make, `.-include`, `.sinclude` and `.dinclude` are optional.
    pub fn is_optional(&self) -> bool {
        self.keyword_name()
            .is_some_and(|(_, name)| matches!(name.as_str(), "-include" | "sinclude" | "dinclude"))
    }

    /// Get the parent item of this include directive, if any
    ///
    /// Returns `Some(MakefileItem)` if this include has a parent that is a MakefileItem
    /// (e.g., a Conditional), or `None` if the parent is the root Makefile node.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    ///
    /// let makefile: Makefile = r#"ifdef DEBUG
    /// include debug.mk
    /// endif
    /// "#.parse().unwrap();
    /// let cond = makefile.conditionals().next().unwrap();
    /// let inc = cond.if_items().next().unwrap();
    /// // Include's parent is the conditional
    /// assert!(matches!(inc, makefile_lossless::MakefileItem::Include(_)));
    /// ```
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }

    /// Remove this include directive from the makefile
    ///
    /// This also removes the comment lines directly above it, with no blank line in between, as
    /// they document it. If that leaves a blank line above where it was
    /// followed by another blank line or the end of the file, the blank line
    /// above is removed too.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "include config.mk\nVAR = value\n".parse().unwrap();
    /// let mut inc = makefile.includes().next().unwrap();
    /// inc.remove().unwrap();
    /// assert_eq!(makefile.includes().count(), 0);
    /// ```
    pub fn remove(&mut self) -> Result<(), Error> {
        let Some(parent) = self.syntax().parent() else {
            return Err(Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: "Cannot remove include: no parent node".to_string(),
                    line: 1,
                    context: "include_remove".to_string(),
                }],
            }));
        };

        remove_with_preceding_comments(self.syntax(), &parent);
        Ok(())
    }

    /// Set the path of this include directive
    ///
    /// `#` is escaped as needed, so that [`Self::path`] returns `new_path`.
    /// Returns an error if the directive has no path, `new_path` is empty or
    /// `new_path` can not be written in it, such as a path containing a
    /// newline.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "include old.mk\n".parse().unwrap();
    /// let mut inc = makefile.includes().next().unwrap();
    /// inc.set_path("new#1.mk").unwrap();
    /// assert_eq!(inc.path(), Some("new#1.mk".to_string()));
    /// assert_eq!(makefile.to_string(), "include new\\#1.mk\n");
    /// ```
    pub fn set_path(&mut self, new_path: &str) -> Result<(), Error> {
        let error = |message: String| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message,
                    line: 1,
                    context: "include_set_path".to_string(),
                }],
            })
        };
        // GNU make accepts an include without file names, but that is not
        // a path.
        if new_path.is_empty() {
            return Err(error("Cannot set an empty include path".to_string()));
        }
        let expr = self
            .path_expr()
            .ok_or_else(|| error("Cannot set path: include has no path".to_string()))?;
        let before_comment = expr
            .next_sibling_or_token()
            .is_some_and(|it| it.kind() == COMMENT);
        let nmake = self.prefix() == Some('!');
        // Keep the delimiters of a BSD make or nmake include.
        let open = self
            .raw_path()
            .filter(|raw| self.has_delimited_path() && strip_delimiters(raw).is_some())
            .and_then(|raw| raw.chars().next());
        let mut text = match (nmake, open) {
            // Carets in an nmake quoted string are literal, so there is no
            // way to escape a `#`.
            (true, Some('"')) if new_path.contains('#') => {
                return Err(error(format!(
                    "Cannot set a quoted nmake include path containing '#': {new_path}"
                )));
            }
            (true, Some('"')) => new_path.to_string(),
            (true, _) => escape_nmake(new_path),
            (false, _) => escape_hashes(new_path, self.is_bsd(), before_comment),
        };
        if let Some(open) = open {
            let close = if open == '<' { '>' } else { '"' };
            text = format!("{open}{text}{close}");
        }

        // Parse the directive with the new path, from its keyword (or the
        // `!` of an nmake directive) on, to check that make reads it back as
        // `new_path`.
        let start = if nmake { OPERATOR } else { IDENTIFIER };
        let directive: String = self
            .syntax()
            .children_with_tokens()
            .skip_while(|it| it.kind() != start)
            .map(|it| match it.as_node() {
                Some(node) if node == &expr => text.clone(),
                _ => it.to_string(),
            })
            .collect();
        let parsed = parse(&directive, nmake.then_some(MakefileVariant::NMake));
        let mut items = parsed.root().syntax().children();
        let new_expr = items
            .next()
            .and_then(Include::cast)
            .filter(|include| {
                parsed.errors.is_empty()
                    && items.next().is_none()
                    && include.path().as_deref() == Some(new_path)
            })
            .and_then(|include| include.path_expr())
            .ok_or_else(|| error(format!("Cannot write {:?} as an include path", new_path)))?;
        super::replace_children(
            &expr,
            new_expr.green().children().map(|c| c.to_owned()).collect(),
        );
        Ok(())
    }

    /// Make this include optional (change "include" to "-include")
    ///
    /// If the include is already optional, this has no effect. For BSD make
    /// this switches between `.include` and `.-include`.
    ///
    /// Returns an error when making an nmake `!INCLUDE` optional, as nmake
    /// has no optional include directive, and when making a BSD make
    /// `.dinclude` non-optional, as there is no such form of it.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "include config.mk\n".parse().unwrap();
    /// let mut inc = makefile.includes().next().unwrap();
    /// inc.set_optional(true).unwrap();
    /// assert!(inc.is_optional());
    /// assert_eq!(makefile.to_string(), "-include config.mk\n");
    /// ```
    pub fn set_optional(&mut self, optional: bool) -> Result<(), Error> {
        let error = |message: &str| {
            Error::Parse(ParseError {
                errors: vec![ErrorInfo {
                    kind: crate::ParseErrorKind::Other,
                    message: message.to_string(),
                    line: 1,
                    context: "include_set_optional".to_string(),
                }],
            })
        };
        let (token, name) = self
            .keyword_name()
            .ok_or_else(|| error("Include has no keyword"))?;
        if optional == self.is_optional() {
            return Ok(());
        }
        if optional && name.starts_with('!') {
            return Err(error("nmake has no optional include directive"));
        }
        // In the `.include` form the dot is part of the keyword token.
        let dot = if token.text().starts_with('.') {
            "."
        } else {
            ""
        };
        let new_name = match (optional, name.as_str()) {
            (true, "include") => "-include",
            (false, "-include" | "sinclude") => "include",
            (false, "dinclude") => return Err(error(".dinclude has no non-optional form")),
            _ => return Err(error(&format!("Unknown include directive {name:?}"))),
        };

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(INCLUDE.into());
        builder.token(IDENTIFIER.into(), &format!("{}{}", dot, new_name));
        builder.finish_node();
        let new_token = SyntaxNode::new_root_mut(builder.finish())
            .first_token()
            .unwrap();
        let index = token.index();
        self.syntax()
            .splice_children(index..index + 1, vec![new_token.into()]);
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lossless::Makefile;

    #[test]
    fn test_include_parent() {
        let makefile: Makefile = "include common.mk\n".parse().unwrap();

        let inc = makefile.includes().next().unwrap();
        let parent = inc.parent();
        // Parent is ROOT node which doesn't cast to MakefileItem
        assert!(parent.is_none());
    }

    #[test]
    fn test_add_include() {
        let mut makefile = Makefile::new();
        makefile.add_include("config.mk").unwrap();

        let includes: Vec<_> = makefile.includes().collect();
        assert_eq!(includes.len(), 1);
        assert_eq!(includes[0].path(), Some("config.mk".to_string()));

        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["config.mk"]);

        // Check the generated text
        assert_eq!(makefile.to_string(), "include config.mk\n");
    }

    #[test]
    fn test_add_include_to_existing() {
        let mut makefile: Makefile = "VAR = value\nrule:\n\tcommand\n".parse().unwrap();
        makefile.add_include("config.mk").unwrap();

        // Include should be added at the beginning
        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["config.mk"]);

        // Check that the include comes first
        let text = makefile.to_string();
        assert!(text.starts_with("include config.mk\n"));
        assert!(text.contains("VAR = value"));
    }

    #[test]
    fn test_insert_include() {
        let mut makefile: Makefile = "VAR = value\nrule:\n\tcommand\n".parse().unwrap();
        makefile.insert_include(1, "config.mk").unwrap();

        let items: Vec<_> = makefile.items().collect();
        assert_eq!(items.len(), 3);

        // Check the middle item is the include
        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["config.mk"]);
    }

    #[test]
    fn test_insert_include_at_beginning() {
        let mut makefile: Makefile = "VAR = value\n".parse().unwrap();
        makefile.insert_include(0, "config.mk").unwrap();

        let text = makefile.to_string();
        assert!(text.starts_with("include config.mk\n"));
    }

    #[test]
    fn test_insert_include_at_end() {
        let mut makefile: Makefile = "VAR = value\n".parse().unwrap();
        let item_count = makefile.items().count();
        makefile.insert_include(item_count, "config.mk").unwrap();

        let text = makefile.to_string();
        assert!(text.ends_with("include config.mk\n"));
    }

    #[test]
    fn test_insert_include_out_of_bounds() {
        let mut makefile: Makefile = "VAR = value\n".parse().unwrap();
        let result = makefile.insert_include(100, "config.mk");
        assert!(result.is_err());
    }

    #[test]
    fn test_insert_include_after() {
        let mut makefile: Makefile = "VAR1 = value1\nVAR2 = value2\n".parse().unwrap();
        let first_var = makefile.items().next().unwrap();
        makefile
            .insert_include_after(&first_var, "config.mk")
            .unwrap();

        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["config.mk"]);

        // Check that the include is after VAR1
        let text = makefile.to_string();
        let var1_pos = text.find("VAR1").unwrap();
        let include_pos = text.find("include config.mk").unwrap();
        assert!(include_pos > var1_pos);
    }

    #[test]
    fn test_insert_include_after_with_rule() {
        let mut makefile: Makefile = "rule1:\n\tcommand1\nrule2:\n\tcommand2\n".parse().unwrap();
        let first_rule_item = makefile.items().next().unwrap();
        makefile
            .insert_include_after(&first_rule_item, "config.mk")
            .unwrap();

        let text = makefile.to_string();
        let rule1_pos = text.find("rule1:").unwrap();
        let include_pos = text.find("include config.mk").unwrap();
        let rule2_pos = text.find("rule2:").unwrap();

        // Include should be between rule1 and rule2
        assert!(include_pos > rule1_pos);
        assert!(include_pos < rule2_pos);
    }

    #[test]
    fn test_include_remove() {
        let makefile: Makefile = "include config.mk\nVAR = value\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.remove().unwrap();

        assert_eq!(makefile.includes().count(), 0);
        assert_eq!(makefile.to_string(), "VAR = value\n");
    }

    #[test]
    fn test_include_remove_multiple() {
        let makefile: Makefile = "include first.mk\ninclude second.mk\nVAR = value\n"
            .parse()
            .unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.remove().unwrap();

        assert_eq!(makefile.includes().count(), 1);
        let remaining = makefile.includes().next().unwrap();
        assert_eq!(remaining.path(), Some("second.mk".to_string()));
    }

    #[test]
    fn test_include_set_path() {
        let makefile: Makefile = "include old.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_path("new.mk").unwrap();

        assert_eq!(inc.path(), Some("new.mk".to_string()));
        assert_eq!(makefile.to_string(), "include new.mk\n");
    }

    #[test]
    fn test_include_set_path_preserves_optional() {
        let makefile: Makefile = "-include old.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_path("new.mk").unwrap();

        assert_eq!(inc.path(), Some("new.mk".to_string()));
        assert!(inc.is_optional());
        assert_eq!(makefile.to_string(), "-include new.mk\n");
    }

    #[test]
    fn test_include_set_optional_true() {
        let makefile: Makefile = "include config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(true).unwrap();

        assert!(inc.is_optional());
        assert_eq!(makefile.to_string(), "-include config.mk\n");
    }

    #[test]
    fn test_include_set_optional_false() {
        let makefile: Makefile = "-include config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(false).unwrap();

        assert!(!inc.is_optional());
        assert_eq!(makefile.to_string(), "include config.mk\n");
    }

    #[test]
    fn test_include_set_optional_from_sinclude() {
        let makefile: Makefile = "sinclude config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(false).unwrap();

        assert!(!inc.is_optional());
        assert_eq!(makefile.to_string(), "include config.mk\n");
    }

    #[test]
    fn test_include_set_optional_already_optional() {
        let makefile: Makefile = "-include config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(true).unwrap();

        // Should remain unchanged
        assert!(inc.is_optional());
        assert_eq!(makefile.to_string(), "-include config.mk\n");
    }

    #[test]
    fn test_include_set_optional_already_non_optional() {
        let makefile: Makefile = "include config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(false).unwrap();

        // Should remain unchanged
        assert!(!inc.is_optional());
        assert_eq!(makefile.to_string(), "include config.mk\n");
    }

    #[test]
    fn test_include_combined_operations() {
        let makefile: Makefile = "include old.mk\nVAR = value\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();

        // Change path and make optional
        inc.set_path("new.mk").unwrap();
        inc.set_optional(true).unwrap();

        assert_eq!(inc.path(), Some("new.mk".to_string()));
        assert!(inc.is_optional());
        assert_eq!(makefile.to_string(), "-include new.mk\nVAR = value\n");
    }

    #[test]
    fn test_include_path_range() {
        let makefile: Makefile = "include config.mk\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        let range = inc.path_range().unwrap();
        assert_eq!(
            &makefile.to_string()[std::ops::Range::from(range)],
            "config.mk"
        );
    }

    #[test]
    fn test_include_path_range_optional() {
        let makefile: Makefile = "-include optional.mk\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        let range = inc.path_range().unwrap();
        assert_eq!(
            &makefile.to_string()[std::ops::Range::from(range)],
            "optional.mk"
        );
    }

    #[test]
    fn test_include_path_range_sinclude() {
        let makefile: Makefile = "sinclude silent.mk\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        let range = inc.path_range().unwrap();
        assert_eq!(
            &makefile.to_string()[std::ops::Range::from(range)],
            "silent.mk"
        );
    }

    /// The paths of each include in `text`, paired with the text of their
    /// ranges.
    fn include_paths(text: &str, variant: MakefileVariant) -> Vec<Vec<(String, &str)>> {
        let makefile = Makefile::parse_with_variant(text, variant).tree();
        makefile
            .includes()
            .map(|inc| {
                let paths: Vec<_> = inc.paths().collect();
                let ranges: Vec<_> = inc.path_ranges().map(|r| &text[r]).collect();
                assert_eq!(paths.len(), ranges.len());
                paths.into_iter().zip(ranges).collect()
            })
            .collect()
    }

    fn pairs<'a>(items: &[(&str, &'a str)]) -> Vec<(String, &'a str)> {
        items.iter().map(|(p, r)| (p.to_string(), *r)).collect()
    }

    #[test]
    fn test_include_paths() {
        assert_eq!(
            include_paths(
                "include a.mk  $(subst a b,c,d) ${X}/y.mk # comment\n",
                MakefileVariant::GNUMake
            ),
            vec![pairs(&[
                ("a.mk", "a.mk"),
                ("$(subst a b,c,d)", "$(subst a b,c,d)"),
                ("${X}/y.mk", "${X}/y.mk"),
            ])]
        );
    }

    #[test]
    fn test_include_paths_optional() {
        assert_eq!(
            include_paths(
                "-include a.mk b.mk\nsinclude c.mk\n",
                MakefileVariant::GNUMake
            ),
            vec![
                pairs(&[("a.mk", "a.mk"), ("b.mk", "b.mk")]),
                pairs(&[("c.mk", "c.mk")]),
            ]
        );
    }

    #[test]
    fn test_include_paths_continuation() {
        assert_eq!(
            include_paths(
                "include a.mk \\\n  b.mk\\\n\tc.mk\n",
                MakefileVariant::GNUMake
            ),
            vec![pairs(&[
                ("a.mk", "a.mk"),
                ("b.mk", "b.mk"),
                ("c.mk", "c.mk")
            ])]
        );
        assert_eq!(
            include_paths(
                "include $(subst a \\\n  b,c,x) d.mk\n",
                MakefileVariant::GNUMake
            ),
            vec![pairs(&[
                ("$(subst a b,c,x)", "$(subst a \\\n  b,c,x)"),
                ("d.mk", "d.mk"),
            ])]
        );
    }

    #[test]
    fn test_include_paths_crlf() {
        assert_eq!(
            include_paths("include a.mk \\\r\n  b.mk\r\n", MakefileVariant::GNUMake),
            vec![pairs(&[("a.mk", "a.mk"), ("b.mk", "b.mk")])]
        );
    }

    #[test]
    fn test_include_paths_escapes() {
        assert_eq!(
            include_paths(
                "include a\\#b.mk c\\ d.mk e\\\\ f.mk\n",
                MakefileVariant::GNUMake
            ),
            vec![pairs(&[
                ("a#b.mk", "a\\#b.mk"),
                ("c\\ d.mk", "c\\ d.mk"),
                ("e\\\\", "e\\\\"),
                ("f.mk", "f.mk"),
            ])]
        );
    }

    #[test]
    fn test_include_paths_empty() {
        assert_eq!(
            include_paths("include\ninclude  # c\n", MakefileVariant::GNUMake),
            vec![vec![], vec![]]
        );
    }

    #[test]
    fn test_include_paths_conditional() {
        assert_eq!(
            include_paths(
                "ifdef X\ninclude a.mk b.mk\nendif\n",
                MakefileVariant::GNUMake
            ),
            vec![pairs(&[("a.mk", "a.mk"), ("b.mk", "b.mk")])]
        );
    }

    #[test]
    fn test_include_paths_bsd() {
        assert_eq!(
            include_paths(
                ".include <a b.mk> # c\n.include \"${X}/c.mk\"\n.-include \"d.mk\"\n",
                MakefileVariant::BSDMake
            ),
            vec![
                pairs(&[("a b.mk", "a b.mk")]),
                pairs(&[("${X}/c.mk", "${X}/c.mk")]),
                pairs(&[("d.mk", "d.mk")]),
            ]
        );
    }

    #[test]
    fn test_include_paths_nmake() {
        assert_eq!(
            include_paths(
                "!INCLUDE <win32.mak>\n!INCLUDE a.mak\n",
                MakefileVariant::NMake
            ),
            vec![
                pairs(&[("win32.mak", "win32.mak")]),
                pairs(&[("a.mak", "a.mak")]),
            ]
        );
    }

    #[test]
    fn test_include_with_comment() {
        let makefile: Makefile = "# Comment\ninclude config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.remove().unwrap();

        // Comment should also be removed
        assert_eq!(makefile.includes().count(), 0);
        assert!(!makefile.to_string().contains("# Comment"));
    }

    #[test]
    fn test_set_optional_keeps_variable_references() {
        let makefile: Makefile = "include $(TOP)/config.mk\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_optional(true).unwrap();
        assert_eq!(makefile.to_string(), "-include $(TOP)/config.mk\n");
        inc.set_optional(false).unwrap();
        assert_eq!(makefile.to_string(), "include $(TOP)/config.mk\n");
    }

    #[test]
    fn test_bsd_set_optional() {
        let makefile: Makefile = ".include <bsd.prog.mk>\n.  include \"x.mk\"\n"
            .parse()
            .unwrap();
        for mut inc in makefile.includes() {
            inc.set_optional(true).unwrap();
            assert!(inc.is_optional());
        }
        assert_eq!(
            makefile.to_string(),
            ".-include <bsd.prog.mk>\n.  -include \"x.mk\"\n"
        );
        for mut inc in makefile.includes() {
            inc.set_optional(false).unwrap();
            assert!(!inc.is_optional());
        }
        assert_eq!(
            makefile.to_string(),
            ".include <bsd.prog.mk>\n.  include \"x.mk\"\n"
        );
    }

    #[test]
    fn test_bsd_set_optional_dinclude() {
        let makefile: Makefile = ".dinclude <b.mk>\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        assert!(inc.set_optional(false).is_err());
        assert!(inc.is_optional());
        inc.set_optional(true).unwrap();
        assert_eq!(makefile.to_string(), ".dinclude <b.mk>\n");
    }

    #[test]
    fn test_set_optional_without_keyword() {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(INCLUDE.into());
        builder.finish_node();
        let mut inc = Include::cast(SyntaxNode::new_root_mut(builder.finish())).unwrap();
        assert!(inc.set_optional(true).is_err());
        assert!(inc.set_optional(false).is_err());
    }

    #[test]
    fn test_bsd_optional_variants() {
        let makefile: Makefile = ".sinclude <a.mk>\n.dinclude <b.mk>\n.include <c.mk>\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile
                .includes()
                .map(|i| (i.path().unwrap(), i.is_optional()))
                .collect::<Vec<_>>(),
            vec![
                ("a.mk".to_string(), true),
                ("b.mk".to_string(), true),
                ("c.mk".to_string(), false),
            ]
        );
    }

    #[test]
    fn test_bsd_set_path_keeps_delimiters() {
        let makefile: Makefile = ".include <bsd.prog.mk>\n. include \"old.mk\"\n"
            .parse()
            .unwrap();
        for mut inc in makefile.includes() {
            inc.set_path("new.mk").unwrap();
            assert_eq!(inc.path(), Some("new.mk".to_string()));
        }
        assert_eq!(
            makefile.to_string(),
            ".include <new.mk>\n. include \"new.mk\"\n"
        );
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["new.mk", "new.mk"]
        );
    }

    #[test]
    fn test_include_line_continuation() {
        for (code, keyword_optional) in [
            ("include a.mk \\\n  b.mk\n", false),
            ("-include a.mk \\\n  b.mk\n", true),
            ("sinclude a.mk\\\n\tb.mk\n", true),
        ] {
            let makefile: Makefile = code.parse().unwrap();
            assert_eq!(makefile.to_string(), code);
            let includes: Vec<_> = makefile.includes().collect();
            assert_eq!(includes.len(), 1);
            assert_eq!(includes[0].path(), Some("a.mk b.mk".to_string()));
            assert_eq!(includes[0].is_optional(), keyword_optional);
            assert_eq!(makefile.rules().count(), 0);
        }
    }

    #[test]
    fn test_include_line_continuation_before_path() {
        let code = "include \\\n  a.mk \\\n \\\n  b.mk\nc.mk: d\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["a.mk b.mk"]
        );
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_include_escaped_backslash_not_continuation() {
        let code = "include a.mk\\\\\nb.mk: c\n";
        let makefile: Makefile = code.parse().unwrap();
        assert_eq!(makefile.to_string(), code);
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["a.mk\\\\"]
        );
        let rules: Vec<_> = makefile.rules().collect();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["b.mk"]);
    }

    #[test]
    fn test_path_unescapes_hash() {
        let code = concat!(
            "include a\\#b\n",
            "include a\\\\\\#b # c\n",
            "include a\\\\#b\n",
            "include $(subst \\#,x,a) # c\n",
        );
        let parsed = Makefile::parse_with_variant(code, MakefileVariant::GNUMake);
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        assert_eq!(
            makefile.included_files().collect::<Vec<_>>(),
            vec!["a#b", "a\\#b", "a\\", "$(subst \\#,x,a)"]
        );
        assert_eq!(
            makefile
                .includes()
                .map(|i| &code[std::ops::Range::from(i.path_range().unwrap())])
                .collect::<Vec<_>>(),
            vec!["a\\#b", "a\\\\\\#b", "a\\\\", "$(subst \\#,x,a)"]
        );

        let makefile: Makefile = ".include <a\\#b> # c\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        assert_eq!(inc.path(), Some("a#b".to_string()));
        assert_eq!(
            &makefile.to_string()[std::ops::Range::from(inc.path_range().unwrap())],
            "<a\\#b>"
        );
    }

    #[test]
    fn test_set_path_escapes_hash() {
        for (code, path, expected) in [
            ("include old.mk\n", "a#b", "include a\\#b\n"),
            ("include old.mk\n", "a\\#b", "include a\\\\\\#b\n"),
            ("include old.mk\n", "a\\\\", "include a\\\\\n"),
            ("include old.mk# c\n", "a\\", "include a\\\\# c\n"),
            (
                "include old.mk\n",
                "$(subst \\#,x,a)",
                "include $(subst \\#,x,a)\n",
            ),
            ("-include old.mk\n", "a b#c", "-include a b\\#c\n"),
            (".include <old.mk>\n", "a#b", ".include <a\\#b>\n"),
            (
                ".include <old.mk> # c\n",
                "a\\\\#b",
                ".include <a\\\\\\#b> # c\n",
            ),
        ] {
            let makefile: Makefile = code.parse().unwrap();
            let mut inc = makefile.includes().next().unwrap();
            inc.set_path(path).unwrap();
            assert_eq!(makefile.to_string(), expected);
            assert_eq!(inc.path().as_deref(), Some(path));
            let reparsed: Makefile = expected.parse().unwrap();
            assert_eq!(
                reparsed.included_files().collect::<Vec<_>>(),
                vec![path.to_string()]
            );
        }
    }

    #[test]
    fn test_set_path_unrepresentable() {
        for (code, path) in [
            ("include old.mk\n", "a\nb"),
            ("include old.mk\n", "a\\"),
            ("include old.mk\n", ""),
            (".include <old.mk>\n", "a>b"),
            (".include <old.mk>\n", "a\\#b"),
        ] {
            let makefile: Makefile = code.parse().unwrap();
            let mut inc = makefile.includes().next().unwrap();
            assert!(inc.set_path(path).is_err(), "{path:?}");
            assert_eq!(makefile.to_string(), code);
        }
    }

    #[test]
    fn test_add_include_escapes_hash() {
        for eol in ["\n", "\r\n"] {
            for (path, written) in [
                ("a#b", "a\\#b"),
                ("a\\#b", "a\\\\\\#b"),
                ("$(subst \\#,x,a)", "$(subst \\#,x,a)"),
            ] {
                let mut makefile: Makefile = format!("X = 1{eol}").parse().unwrap();
                let first = makefile.items().next().unwrap();
                let added = makefile.add_include(path).unwrap();
                let inserted = makefile.insert_include(2, path).unwrap();
                let after = makefile.insert_include_after(&first, path).unwrap();
                assert_eq!(
                    makefile.to_string(),
                    format!("include {written}{eol}X = 1{eol}include {written}{eol}include {written}{eol}")
                );
                for inc in [added, inserted, after] {
                    assert_eq!(inc.path().as_deref(), Some(path));
                }
                let reparsed: Makefile = makefile.to_string().parse().unwrap();
                assert_eq!(reparsed.included_files().collect::<Vec<_>>(), vec![path; 3]);
            }
        }
    }

    #[test]
    fn test_add_include_unrepresentable() {
        for eol in ["\n", "\r\n"] {
            for path in ["a\nb", "a\\", " a", ""] {
                let code = format!("X = 1{eol}");
                let mut makefile: Makefile = code.parse().unwrap();
                let first = makefile.items().next().unwrap();
                assert!(makefile.add_include(path).is_err(), "{path:?}");
                assert!(makefile.insert_include(1, path).is_err(), "{path:?}");
                assert!(
                    makefile.insert_include_after(&first, path).is_err(),
                    "{path:?}"
                );
                assert_eq!(makefile.to_string(), code);
            }
        }
    }

    #[test]
    fn test_path_excludes_comment() {
        let makefile: Makefile = "include foo.mk # comment\n.include <bsd.own.mk> # c\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile.includes().map(|i| i.path()).collect::<Vec<_>>(),
            vec![Some("foo.mk".to_string()), Some("bsd.own.mk".to_string())]
        );
        let mut inc = makefile.includes().next().unwrap();
        inc.set_path("bar.mk").unwrap();
        assert_eq!(
            makefile.to_string(),
            "include bar.mk # comment\n.include <bsd.own.mk> # c\n"
        );
    }

    #[test]
    fn test_bsd_quoted_path() {
        for variant in [None, Some(MakefileVariant::BSDMake)] {
            for (code, path, names) in [
                (
                    ".include \"${.CURDIR}/a\\#b.mk\" # c\n",
                    "${.CURDIR}/a#b.mk",
                    vec![".CURDIR"],
                ),
                (
                    ".include \"${X:S/a/b/ \\\n  :S/c/d/}.mk\"\n",
                    "${X:S/a/b/  :S/c/d/}.mk",
                    vec!["X"],
                ),
                (". -include \"$(A)'$(B)'\"\n", "$(A)'$(B)'", vec!["A", "B"]),
            ] {
                let parsed = match variant {
                    Some(variant) => Makefile::parse_with_variant(code, variant),
                    None => Makefile::parse(code),
                };
                assert_eq!(parsed.errors(), &[]);
                let makefile = parsed.tree();
                assert_eq!(makefile.to_string(), code);
                let inc = makefile.includes().next().unwrap();
                assert_eq!(inc.path().as_deref(), Some(path));
                assert_eq!(
                    makefile
                        .variable_references()
                        .filter_map(|r| r.name())
                        .collect::<Vec<_>>(),
                    names
                );
            }
        }
    }

    #[test]
    fn test_gnu_quoted_path() {
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::POSIXMake),
        ] {
            let code = "-include \"$(X) b\\#c\" \"d\\\n   e\"\n";
            let parsed = match variant {
                Some(variant) => Makefile::parse_with_variant(code, variant),
                None => Makefile::parse(code),
            };
            assert_eq!(parsed.errors(), &[]);
            let makefile = parsed.tree();
            assert_eq!(makefile.to_string(), code);
            assert_eq!(
                makefile.included_files().collect::<Vec<_>>(),
                vec!["\"$(X) b#c\" \"d e\""]
            );
            assert_eq!(
                makefile
                    .variable_references()
                    .filter_map(|r| r.name())
                    .collect::<Vec<_>>(),
                vec!["X"]
            );
        }
    }

    #[test]
    fn test_bsd_quoted_set_path_escapes_hash() {
        let makefile: Makefile = ". include \"old.mk\" # c\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        inc.set_path("${.CURDIR}/a#b").unwrap();
        assert_eq!(makefile.to_string(), ". include \"${.CURDIR}/a\\#b\" # c\n");
        assert_eq!(inc.path().as_deref(), Some("${.CURDIR}/a#b"));
    }

    #[test]
    fn test_path_for_variant() {
        let makefile: Makefile = "include $(subst a \\\n  b,c,a  b)\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        assert_eq!(inc.path(), Some("$(subst a b,c,a  b)".to_string()));
        assert_eq!(
            inc.path_for(MakefileVariant::GNUMake),
            Some("$(subst a b,c,a  b)".to_string())
        );
        assert_eq!(
            inc.path_for(MakefileVariant::POSIXMake),
            Some("$(subst a  b,c,a  b)".to_string())
        );
    }

    #[test]
    fn test_path_for_bsd() {
        let parsed = Makefile::parse_with_variant(
            ".include <${DIR:S/a/b/ \\\n\t:S/c/d/}/x.mk>\n",
            MakefileVariant::BSDMake,
        );
        assert!(parsed.is_ok(), "{:?}", parsed.errors());
        let inc = parsed.tree().includes().next().unwrap();
        assert_eq!(inc.path(), Some("${DIR:S/a/b/  :S/c/d/}/x.mk".to_string()));
        assert_eq!(
            inc.path_for(MakefileVariant::BSDMake),
            Some("${DIR:S/a/b/  :S/c/d/}/x.mk".to_string())
        );
        assert_eq!(
            inc.path_for(MakefileVariant::GNUMake),
            Some("${DIR:S/a/b/ :S/c/d/}/x.mk".to_string())
        );
    }

    #[test]
    fn test_path_for_unescapes_hash() {
        let makefile: Makefile = "include a\\#b \\\n  c.mk\n".parse().unwrap();
        let inc = makefile.includes().next().unwrap();
        assert_eq!(inc.path(), Some("a#b c.mk".to_string()));
        assert_eq!(
            inc.path_for(MakefileVariant::POSIXMake),
            Some("a#b  c.mk".to_string())
        );
    }

    #[test]
    fn test_include_api() {
        // Test the API for working with include directives
        let makefile_str = "include simple.mk\n-include optional.mk\nsinclude synonym.mk\n";
        let makefile: Makefile = makefile_str.parse().unwrap();

        // Test the includes method
        let includes: Vec<_> = makefile.includes().collect();
        assert_eq!(includes.len(), 3);

        // Test the is_optional method
        assert!(!includes[0].is_optional()); // include
        assert!(includes[1].is_optional()); // -include
        assert!(includes[2].is_optional()); // sinclude

        // Test the included_files method
        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["simple.mk", "optional.mk", "synonym.mk"]);

        // Test the path method on Include
        assert_eq!(includes[0].path(), Some("simple.mk".to_string()));
        assert_eq!(includes[1].path(), Some("optional.mk".to_string()));
        assert_eq!(includes[2].path(), Some("synonym.mk".to_string()));
    }

    #[test]
    fn test_keyword_and_range() {
        let text =
            "include a.mk\n-include b.mk\nsinclude c.mk\n.  include \"d.mk\"\n.-include <e.mk>\n";
        let makefile: Makefile = text.parse().unwrap();
        let keywords: Vec<_> = makefile
            .includes()
            .map(|i| (i.keyword().unwrap(), &text[i.keyword_range().unwrap()]))
            .collect();
        assert_eq!(
            keywords,
            vec![
                ("include".to_string(), "include"),
                ("-include".to_string(), "-include"),
                ("sinclude".to_string(), "sinclude"),
                (".include".to_string(), ".  include"),
                (".-include".to_string(), ".-include"),
            ]
        );
    }

    #[test]
    fn test_keyword_range_nmake() {
        let text = "!  include a.mak\r\n!INCLUDE <b.mak>\r\n";
        let makefile = crate::Makefile::parse_with_variant(text, MakefileVariant::NMake).tree();
        let keywords: Vec<_> = makefile
            .includes()
            .map(|i| (i.keyword(), i.keyword_range()))
            .collect();
        assert_eq!(
            keywords,
            vec![
                (
                    Some("!INCLUDE".to_string()),
                    Some(rowan::TextRange::new(0.into(), 10.into()))
                ),
                (
                    Some("!INCLUDE".to_string()),
                    Some(rowan::TextRange::new(18.into(), 26.into()))
                ),
            ]
        );
    }

    #[test]
    fn test_keyword_range_in_conditional() {
        let text = "ifdef X\n  include a.mk\nendif\n";
        let makefile: Makefile = text.parse().unwrap();
        let include = makefile.includes().next().unwrap();
        assert_eq!(
            include.keyword_range(),
            Some(rowan::TextRange::new(10.into(), 17.into()))
        );
    }

    #[test]
    fn test_set_path_keeps_unchanged_parts() {
        let makefile: Makefile = "include  a.mk  $(B)  # x\n".parse().unwrap();
        let mut inc = makefile.includes().next().unwrap();
        let expr = inc.path_expr().unwrap();
        let reference = expr.children().next().unwrap();
        inc.set_path("z.mk  $(B)").unwrap();
        assert_eq!(makefile.code(), "include  z.mk  $(B)  # x\n");
        assert_eq!(inc.path_expr(), Some(expr.clone()));
        assert_eq!(reference.parent(), Some(expr));
        crate::test_util::assert_matches_reparse(&makefile);
    }
}
