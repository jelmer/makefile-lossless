//! Accessors for BSD make constructs: `.for` loops and single-line
//! directives such as `.undef` or `.error`.

use super::conditional::ConditionalItem;
use super::makefile::MakefileItem;
use crate::lossless::{node_text, Directive, ForLoop, SyntaxNode, SyntaxToken};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;

/// Return the token holding the directive name at the start of `node`,
/// together with the keyword normalized to a leading dot followed by the
/// name, e.g. `.if` for both `.if` and `.  if`. In the latter form the
/// returned token is `if`, without the dot.
///
/// For non-BSD constructs such as GNU `ifdef` the keyword is the first
/// identifier as-is.
pub(crate) fn keyword_token(node: &SyntaxNode) -> Option<(SyntaxToken, String)> {
    let mut identifiers = node
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .filter(|t| t.kind() == IDENTIFIER);
    let first = identifiers.next()?;
    if first.text() == "." {
        let name = identifiers.next()?;
        let keyword = format!(".{}", name.text());
        Some((name, keyword))
    } else {
        let keyword = first.text().to_string();
        Some((first, keyword))
    }
}

/// The normalized directive keyword at the start of `node`; see
/// [`keyword_token`].
pub(crate) fn directive_keyword(node: &SyntaxNode) -> Option<String> {
    keyword_token(node).map(|(_, keyword)| keyword)
}

/// Return the trimmed text of the first EXPR child of `node`.
fn expr_text(node: &SyntaxNode) -> Option<String> {
    node.children()
        .find(|it| it.kind() == EXPR)
        .map(|it| node_text(&it).trim().to_string())
}

impl ForLoop {
    fn header(&self) -> Option<SyntaxNode> {
        self.syntax().children().find(|it| it.kind() == FOR_HEADER)
    }

    /// The names of the loop variables.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let makefile: Makefile = ".for src dst in a b\nX+= ${src}\n.endfor\n".parse().unwrap();
    /// let MakefileItem::ForLoop(f) = makefile.items().next().unwrap() else { panic!() };
    /// assert_eq!(f.variables(), vec!["src", "dst"]);
    /// assert_eq!(f.list(), Some("a b".to_string()));
    /// ```
    pub fn variables(&self) -> Vec<String> {
        let Some(header) = self.header() else {
            return vec![];
        };
        let mut identifiers = header
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == IDENTIFIER);
        // Skip the keyword, which is either `.for` or `.` followed by `for`.
        if identifiers.next().is_some_and(|t| t.text() == ".") {
            identifiers.next();
        }
        identifiers
            .take_while(|t| t.text() != "in")
            .map(|t| t.text().to_string())
            .collect()
    }

    /// The unexpanded list of values the loop iterates over.
    pub fn list(&self) -> Option<String> {
        expr_text(&self.header()?)
    }

    /// The items (rules, variables, nested loops, ...) in the loop body.
    pub fn items(&self) -> impl Iterator<Item = MakefileItem> + '_ {
        self.syntax().children().filter_map(MakefileItem::cast)
    }

    /// The items in the loop body in source order, including recipe lines,
    /// which [`ForLoop::items`] skips. A loop inside a rule's body can
    /// contain recipe lines.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{ConditionalItem, Makefile, MakefileItem, MakefileVariant};
    /// let makefile = Makefile::parse_with_variant(
    ///     "all:\n.for f in a b\n\techo ${f}\n.endfor\n",
    ///     MakefileVariant::BSDMake,
    /// )
    /// .tree();
    /// let rule = makefile.rules().next().unwrap();
    /// let Some(ConditionalItem::Item(MakefileItem::ForLoop(f))) = rule.body_items().next() else {
    ///     panic!()
    /// };
    /// let recipes: Vec<String> = f
    ///     .body_items()
    ///     .map(|item| match item {
    ///         ConditionalItem::Recipe(r) => r.text(),
    ///         ConditionalItem::Item(_) => panic!("expected recipe"),
    ///     })
    ///     .collect();
    /// assert_eq!(recipes, vec!["echo ${f}"]);
    /// ```
    pub fn body_items(&self) -> impl Iterator<Item = ConditionalItem> {
        self.syntax().children().filter_map(ConditionalItem::cast)
    }

    /// Get the parent item of this loop, if any.
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }
}

impl Directive {
    /// The directive keyword including the leading dot, e.g. `.undef`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let makefile: Makefile = ".  error unsupported platform\n".parse().unwrap();
    /// let MakefileItem::Directive(d) = makefile.items().next().unwrap() else { panic!() };
    /// assert_eq!(d.keyword(), Some(".error".to_string()));
    /// assert_eq!(d.argument(), Some("unsupported platform".to_string()));
    /// ```
    pub fn keyword(&self) -> Option<String> {
        directive_keyword(self.syntax())
    }

    /// The unexpanded argument of the directive, if any.
    pub fn argument(&self) -> Option<String> {
        expr_text(self.syntax()).filter(|s| !s.is_empty())
    }

    /// Get the parent item of this directive, if any.
    pub fn parent(&self) -> Option<MakefileItem> {
        self.syntax().parent().and_then(MakefileItem::cast)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Makefile, MakefileItem, MakefileVariant};

    fn parse_ok(text: &str) -> Makefile {
        let parsed = Makefile::parse(text);
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        assert_eq!(makefile.to_string(), text);
        makefile
    }

    #[test]
    fn test_include() {
        let makefile =
            parse_ok(".include <bsd.prog.mk>\n.-include \"${.CURDIR}/../Makefile.inc\"\n");
        let includes: Vec<_> = makefile.includes().collect();
        assert_eq!(includes.len(), 2);
        assert_eq!(includes[0].path(), Some("bsd.prog.mk".to_string()));
        assert!(!includes[0].is_optional());
        assert_eq!(
            includes[1].path(),
            Some("${.CURDIR}/../Makefile.inc".to_string())
        );
        assert!(includes[1].is_optional());
    }

    #[test]
    fn test_conditional() {
        let makefile = parse_ok(
            ".if ${MKPIC} != \"no\" # comment\nA=1\n.elif defined(X)\nA=2\n.else\nA=3\n.endif\n",
        );
        let cond = makefile.conditionals().next().unwrap();
        assert_eq!(cond.conditional_type(), Some(".if".to_string()));
        assert_eq!(cond.condition(), Some("${MKPIC} != \"no\"".to_string()));
        assert!(cond.has_else());
        assert_eq!(cond.if_items().count(), 1);
        assert_eq!(cond.else_items().count(), 2);
        let names: Vec<_> = makefile
            .variable_definitions()
            .map(|v| v.raw_value().unwrap())
            .collect();
        assert_eq!(names, vec!["1", "2", "3"]);
    }

    #[test]
    fn test_indented_directives() {
        let makefile = parse_ok(".if defined(A)\n.  ifndef B\nX=1\n.  endif\n.endif\n");
        let outer = makefile.conditionals().next().unwrap();
        let Some(MakefileItem::Conditional(inner)) = outer.if_items().next() else {
            panic!("expected nested conditional");
        };
        assert_eq!(inner.conditional_type(), Some(".ifndef".to_string()));
        assert_eq!(inner.condition(), Some("B".to_string()));
    }

    #[test]
    fn test_add_endif() {
        let parsed = Makefile::parse(".ifdef DEBUG\nVAR = 1\n");
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["unterminated .if (missing .endif)"]
        );
        let makefile = parsed.tree();
        let mut cond = makefile.conditionals().next().unwrap();
        assert!(cond.add_endif().unwrap());
        assert_eq!(makefile.code(), ".ifdef DEBUG\nVAR = 1\n.endif\n");
    }

    #[test]
    fn test_add_else() {
        let makefile = parse_ok(".if 1\nA=1\n.endif\n");
        let mut cond = makefile.conditionals().next().unwrap();
        let temp = parse_ok("A=2\n");
        let var = temp.variable_definitions().next().unwrap();
        cond.add_else_item(MakefileItem::Variable(var));
        assert_eq!(makefile.code(), ".if 1\nA=1\n.else\nA=2\n.endif\n");
    }

    #[test]
    fn test_for_loop() {
        let makefile = parse_ok(
            ".for _src _dst in ${LINKS}\nX+= ${_src}\n.  if 1\nY+= ${_dst}\n.  endif\n.endfor\n",
        );
        let Some(MakefileItem::ForLoop(f)) = makefile.items().next() else {
            panic!("expected for loop");
        };
        assert_eq!(f.variables(), vec!["_src", "_dst"]);
        assert_eq!(f.list(), Some("${LINKS}".to_string()));
        assert_eq!(f.items().count(), 2);
        let names: Vec<_> = makefile
            .variable_definitions()
            .map(|v| v.name().unwrap())
            .collect();
        assert_eq!(names, vec!["X", "Y"]);
    }

    #[test]
    fn test_for_loop_continued_header() {
        let makefile = parse_ok(".for \\\n    var \\\n    in \\\n    a b\n.endfor\n");
        let Some(MakefileItem::ForLoop(f)) = makefile.items().next() else {
            panic!("expected for loop");
        };
        assert_eq!(f.variables(), vec!["var"]);
        assert_eq!(f.list(), Some("a b".to_string()));
    }

    #[test]
    fn test_continuation_after_dot() {
        let makefile =
            parse_ok(".for outer in o\n.\\\n   for inner in i\n.\\\n   endfor\n.endfor\n");
        let Some(MakefileItem::ForLoop(outer)) = makefile.items().next() else {
            panic!("expected for loop");
        };
        let Some(MakefileItem::ForLoop(inner)) = outer.items().next() else {
            panic!("expected nested for loop");
        };
        assert_eq!(inner.variables(), vec!["inner"]);
        assert_eq!(inner.list(), Some("i".to_string()));
    }

    #[test]
    fn test_for_loop_indented_keyword() {
        let makefile = parse_ok(".  for f in a b\n.  endfor\n");
        let Some(MakefileItem::ForLoop(f)) = makefile.items().next() else {
            panic!("expected for loop");
        };
        assert_eq!(f.variables(), vec!["f"]);
        assert_eq!(f.list(), Some("a b".to_string()));
    }

    #[test]
    fn test_directives() {
        let makefile = parse_ok(".undef FOO\n.export-env BAR\n.error ${PROG} is not supported\n");
        let directives: Vec<_> = makefile
            .items()
            .map(|item| match item {
                MakefileItem::Directive(d) => (d.keyword().unwrap(), d.argument()),
                _ => panic!("expected directive"),
            })
            .collect();
        assert_eq!(
            directives,
            vec![
                (".undef".to_string(), Some("FOO".to_string())),
                (".export-env".to_string(), Some("BAR".to_string())),
                (
                    ".error".to_string(),
                    Some("${PROG} is not supported".to_string())
                ),
            ]
        );
    }

    #[test]
    fn test_dependency_operator_force() {
        let makefile = parse_ok("${_F}!\t\t${F} __fileinstall\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["${_F}"]);
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["${F}", "__fileinstall"]
        );
    }

    #[test]
    fn test_empty_target_list() {
        let makefile = parse_ok(": empty-source\n\t: command\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().count(), 0);
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["empty-source"]
        );
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec![": command"]);

        // GNU make accepts this too.
        let parsed = Makefile::parse_with_variant(": empty-source\n", MakefileVariant::GNUMake);
        assert!(parsed.ok());
    }

    #[test]
    fn test_conditional_in_recipe() {
        let makefile = parse_ok("all:\n.if defined(X)\n\techo x\n.endif\n\techo y\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo y"]);
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_conditional_after_rule_without_recipe() {
        // The conditional does not continue the recipe, so it is not part
        // of the rule.
        let makefile = parse_ok("all: foo\n.if defined(X)\nCFLAGS+= -g\n.endif\n");
        assert_eq!(makefile.items().count(), 2);
        assert_eq!(makefile.conditionals().count(), 1);
    }

    #[test]
    fn test_for_loop_in_recipe() {
        let makefile = parse_ok("all:\n.  for d in a b\n\techo ${d}\n.  endfor\n");
        assert_eq!(makefile.items().count(), 1);
    }

    #[test]
    fn test_directive_ends_rule() {
        let makefile = parse_ok("all:\n\techo x\n.include <bsd.prog.mk>\n");
        assert_eq!(makefile.includes().count(), 1);
    }

    #[test]
    fn test_shell_assignment() {
        let makefile = parse_ok("SRCS!=\techo *.c\n");
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("SRCS".to_string()));
        assert_eq!(var.assignment_operator(), Some("!=".to_string()));
        assert_eq!(var.raw_value(), Some("echo *.c".to_string()));
    }

    #[test]
    fn test_empty_variable_name() {
        let makefile = parse_ok("!=\techo 'command during parsing' 1>&2; echo\n");
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.name(), None);
        assert_eq!(var.assignment_operator(), Some("!=".to_string()));
        assert_eq!(
            var.raw_value(),
            Some("echo 'command during parsing' 1>&2; echo".to_string())
        );

        let parsed = Makefile::parse_with_variant("!= echo\n", MakefileVariant::GNUMake);
        assert!(!parsed.ok());
    }

    #[test]
    fn test_unusual_variable_names() {
        let text = "EXP.[A-]=\tA B ]\nC++=\tvalue\nVAR(spaces in parens)=\t()\n@D=\tx\n*=\tasterisk\n%=\tpercent\n";
        let makefile = parse_ok(text);
        assert_eq!(
            makefile
                .variable_definitions()
                .map(|v| (
                    v.name().unwrap(),
                    v.assignment_operator().unwrap(),
                    v.raw_value().unwrap()
                ))
                .collect::<Vec<_>>(),
            vec![
                ("EXP.[A-]".to_string(), "=".to_string(), "A B ]".to_string()),
                ("C+".to_string(), "+=".to_string(), "value".to_string()),
                (
                    "VAR(spaces in parens)".to_string(),
                    "=".to_string(),
                    "()".to_string()
                ),
                ("@D".to_string(), "=".to_string(), "x".to_string()),
                ("*".to_string(), "=".to_string(), "asterisk".to_string()),
                ("%".to_string(), "=".to_string(), "percent".to_string()),
            ]
        );
    }

    #[test]
    fn test_colon_in_variable_name() {
        // BSD make treats this as an assignment to `a:b`; GNU make, and the
        // default mode, as a target-specific variable.
        let parsed = Makefile::parse_with_variant("a:b=c\n", MakefileVariant::BSDMake);
        assert!(parsed.ok());
        let var = parsed.tree().variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("a:b".to_string()));
        assert_eq!(var.raw_value(), Some("c".to_string()));

        let makefile = parse_ok("a:b=c\n");
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_name_with_space_is_not_assignment() {
        let parsed = Makefile::parse("VARIABLE NAME=\tvalue\n");
        assert!(!parsed.ok());
        assert_eq!(parsed.tree().variable_definitions().count(), 0);
    }

    #[test]
    fn test_select_words_modifier_is_not_comment() {
        let makefile = parse_ok("N:=\t${LIST:[#]}\n");
        let var = makefile.variable_definitions().next().unwrap();
        assert_eq!(var.raw_value(), Some("${LIST:[#]}".to_string()));
    }

    #[test]
    fn test_stray_directives() {
        let parsed = Makefile::parse(".endif\n.else\n.endfor\n");
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| (e.line, e.message.as_str()))
                .collect::<Vec<_>>(),
            vec![
                (1, ".endif without matching .if"),
                (2, ".else without matching .if"),
                (3, ".endfor without matching .for"),
            ]
        );
        assert_eq!(parsed.tree().to_string(), ".endif\n.else\n.endfor\n");
    }

    #[test]
    fn test_unterminated_for() {
        let parsed = Makefile::parse(".for x in a\nA=1\n");
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["unterminated .for (missing .endfor)"]
        );
    }

    #[test]
    fn test_unclosed_if_in_for() {
        let parsed = Makefile::parse(".for var in value\n.  if 0\n.endfor\nA=1\n");
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| (e.line, e.message.as_str()))
                .collect::<Vec<_>>(),
            vec![(3, "unterminated .if (missing .endif)")]
        );
        let makefile = parsed.tree();
        assert!(matches!(
            makefile.items().next(),
            Some(MakefileItem::ForLoop(_))
        ));
        assert_eq!(makefile.items().count(), 2);
    }

    #[test]
    fn test_for_without_in() {
        let parsed = Makefile::parse(".for x\n.endfor\n");
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["expected 'in' in .for"]
        );
    }

    #[test]
    fn test_directive_like_rule() {
        // A colon after the keyword makes this a rule, not a directive.
        let makefile = parse_ok(".info: message\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec![".info"]);
    }

    #[test]
    fn test_directive_followed_by_operator() {
        // With whitespace after the name, this is still a directive.
        let makefile = parse_ok(".info = x\n.if == \"\"\n.endif\n");
        let Some(MakefileItem::Directive(d)) = makefile.items().next() else {
            panic!("expected directive");
        };
        assert_eq!(d.argument(), Some("= x".to_string()));
        assert_eq!(makefile.conditionals().count(), 1);
    }

    #[test]
    fn test_gnu_variant_ignores_bsd_directives() {
        let parsed =
            Makefile::parse_with_variant(".include <bsd.prog.mk>\n", MakefileVariant::GNUMake);
        assert!(!parsed.ok());
        assert_eq!(parsed.tree().includes().count(), 0);
    }

    #[test]
    fn test_bsd_variant_ignores_gnu_conditionals() {
        let parsed = Makefile::parse_with_variant("ifdef X\nendif\n", MakefileVariant::BSDMake);
        assert!(!parsed.ok());
        assert_eq!(parsed.tree().conditionals().count(), 0);

        let parsed = Makefile::parse_with_variant(".ifdef X\n.endif\n", MakefileVariant::BSDMake);
        assert!(parsed.ok());
        assert_eq!(parsed.tree().conditionals().count(), 1);
    }

    #[test]
    fn test_missing_condition() {
        let parsed = Makefile::parse(".ifdef\n.endif\n");
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| (e.line, e.message.as_str()))
                .collect::<Vec<_>>(),
            vec![(1, "expected condition after .ifdef")]
        );
    }

    fn parse_bsd(text: &str) -> Makefile {
        let parsed = Makefile::parse_with_variant(text, MakefileVariant::BSDMake);
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        assert_eq!(makefile.to_string(), text);
        makefile
    }

    #[test]
    fn test_sunsh_assignment() {
        let makefile = parse_bsd(concat!(
            "VAR:sh=\techo colon-sh\n",
            "VAR :sh =\techo spaced\n",
            "VAR :sh :sh=\techo multiple\n",
            "VAR:sh =\techo space-before-op\n",
        ));
        assert_eq!(
            makefile
                .variable_definitions()
                .map(|v| (
                    v.name().unwrap(),
                    v.assignment_operator().unwrap(),
                    v.raw_value().unwrap()
                ))
                .collect::<Vec<_>>(),
            vec![
                (
                    "VAR".to_string(),
                    ":sh=".to_string(),
                    "echo colon-sh".to_string()
                ),
                (
                    "VAR".to_string(),
                    ":sh=".to_string(),
                    "echo spaced".to_string()
                ),
                (
                    "VAR".to_string(),
                    ":sh=".to_string(),
                    "echo multiple".to_string()
                ),
                (
                    "VAR".to_string(),
                    ":sh=".to_string(),
                    "echo space-before-op".to_string()
                ),
            ]
        );
    }

    #[test]
    fn test_sunsh_not_an_operator() {
        // As in BSD make: `:shell` is part of the name, `:sh` before another
        // operator is ignored if separated from the name, and part of the
        // name otherwise. A group of parentheses after `:sh` is ignored too.
        let makefile = parse_bsd(concat!(
            "VAR:shell=\techo colon-shell\n",
            "VAR :sh +=\techo two\n",
            "VAR:sh !=\techo space-after\n",
            "VAR :sh(a comment)=\tvalue\n",
        ));
        assert_eq!(
            makefile
                .variable_definitions()
                .map(|v| (v.name().unwrap(), v.assignment_operator().unwrap()))
                .collect::<Vec<_>>(),
            vec![
                ("VAR:shell".to_string(), "=".to_string()),
                ("VAR".to_string(), "+=".to_string()),
                ("VAR:sh".to_string(), "!=".to_string()),
                ("VAR".to_string(), "=".to_string()),
            ]
        );
    }

    #[test]
    fn test_sunsh_in_default_mode_is_rule() {
        // GNU make reads this as a rule with a target-specific variable.
        let makefile = parse_ok("VAR:sh= echo\n");
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_set_assignment_operator_on_sunsh() {
        let makefile = parse_bsd("VAR :sh =\techo\n");
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_assignment_operator("!=");
        assert_eq!(makefile.code(), "VAR !=\techo\n");
        assert_eq!(var.assignment_operator(), Some("!=".to_string()));
    }

    #[test]
    fn test_include_without_space() {
        let makefile = parse_ok(".include<bsd.own.mk>\n.-include\"x.mk\"\n");
        assert_eq!(
            makefile
                .includes()
                .map(|i| (i.path().unwrap(), i.is_optional()))
                .collect::<Vec<_>>(),
            vec![
                ("bsd.own.mk".to_string(), false),
                ("x.mk".to_string(), true)
            ]
        );
    }

    #[test]
    fn test_include_keyword_as_target() {
        // Like make, `include` needs whitespace after it to be a directive.
        let makefile = parse_ok("include: foo\n\techo\n");
        assert_eq!(makefile.includes().count(), 0);
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["include"]);
    }

    #[test]
    fn test_sysv_include_dependency_line() {
        // BSD make reads a line with a dependency operator followed by
        // whitespace as a dependency line, even if it starts with `include`.
        let makefile = parse_bsd("include foo: bar\ninclude a:b\n");
        assert_eq!(makefile.rules().count(), 1);
        assert_eq!(makefile.included_files().collect::<Vec<_>>(), vec!["a:b"]);
    }

    #[test]
    fn test_add_bsd_conditional() {
        let mut makefile = Makefile::new();
        let cond = makefile
            .add_conditional(
                ".if",
                "defined(DEBUG)",
                "CFLAGS+= -g\n",
                Some("CFLAGS+= -O2\n"),
            )
            .unwrap();
        assert_eq!(cond.conditional_type(), Some(".if".to_string()));
        let text = makefile.to_string();
        assert_eq!(
            text,
            ".if defined(DEBUG)\nCFLAGS+= -g\n.else\nCFLAGS+= -O2\n.endif\n"
        );
        let reparsed = parse_bsd(&text);
        let cond = reparsed.conditionals().next().unwrap();
        assert_eq!(cond.condition(), Some("defined(DEBUG)".to_string()));
        assert!(cond.has_else());
    }

    fn errors_with(variant: MakefileVariant, text: &str) -> usize {
        Makefile::parse_with_variant(text, variant).errors().len()
    }

    #[test]
    fn test_gnu_only_syntax_is_error_in_bsd_make() {
        // BSD make reports these as "Invalid line" or, for `export`,
        // "Variable/Value missing from export".
        for text in [
            "define X\nfoo\nendef\n",
            "vpath %.c src\n",
            "override X = 1\n",
            "private X = 1\n",
            "unexport X\n",
            "undefine X\n",
            "export X\n",
            "export\n",
            "ifdef X\nendif\n",
        ] {
            assert_ne!(errors_with(MakefileVariant::BSDMake, text), 0, "{text:?}");
            assert_eq!(errors_with(MakefileVariant::GNUMake, text), 0, "{text:?}");
        }
    }

    #[test]
    fn test_gmake_export_in_bsd_make() {
        let parsed = Makefile::parse_with_variant("export X = 1\n", MakefileVariant::BSDMake);
        assert!(parsed.ok());
        let var = parsed.tree().variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("X".to_string()));
        assert!(var.is_export());
    }

    #[test]
    fn test_bsd_only_syntax_is_error_in_gnu_make() {
        for text in [
            ".if 1\n.endif\n",
            ".include <bsd.prog.mk>\n",
            ".for f in a\n.endfor\n",
            ".undef X\n",
            "a! b\n",
            "!= echo\n",
        ] {
            assert_ne!(errors_with(MakefileVariant::GNUMake, text), 0, "{text:?}");
            assert_eq!(errors_with(MakefileVariant::BSDMake, text), 0, "{text:?}");
        }
    }

    #[test]
    fn test_gnu_variable_names() {
        // GNU make allows any characters but whitespace, `:`, `#` and `=`.
        let parsed = Makefile::parse_with_variant(
            "EXP.[A-]= x\n*= y\na(b)= z\nx,y = w\n",
            MakefileVariant::GNUMake,
        );
        assert!(parsed.ok());
        assert_eq!(
            parsed
                .tree()
                .variable_definitions()
                .map(|v| v.name().unwrap())
                .collect::<Vec<_>>(),
            vec!["EXP.[A-]", "*", "a(b)", "x,y"]
        );
        assert_ne!(errors_with(MakefileVariant::GNUMake, "a b = c\n"), 0);
    }

    #[test]
    fn test_indented_line_outside_rule_in_bsd_make() {
        // BSD make reads a tab-indented line as a shell command, which is an
        // error outside of a rule, unless it only has a comment.
        let parsed = Makefile::parse_with_variant("X=1\n\tA = 1\n", MakefileVariant::BSDMake);
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| (e.line, e.message.as_str()))
                .collect::<Vec<_>>(),
            vec![(2, "indented line not part of a rule")]
        );
        assert_eq!(parsed.tree().variable_definitions().count(), 1);
        assert_eq!(
            errors_with(MakefileVariant::BSDMake, "X=1\n\t\t# comment\n"),
            0
        );
        // GNU make parses it as a normal line.
        let parsed = Makefile::parse_with_variant("X=1\n\tA = 1\n", MakefileVariant::GNUMake);
        assert!(parsed.ok());
        assert_eq!(parsed.tree().variable_definitions().count(), 2);
    }

    #[test]
    fn test_no_order_only_prerequisites_in_bsd_make() {
        // BSD make takes `|` as a file name: "don't know how to make |".
        let makefile = parse_bsd("foo: bar | baz\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["bar", "|", "baz"]
        );
        assert_eq!(rule.order_only_prerequisites().count(), 0);
    }

    #[test]
    fn test_no_gnu_rule_syntax_in_bsd_make() {
        // BSD make takes `%.o:` as a source and `&` as a target.
        let makefile = parse_bsd("a.o: %.o: %.c\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.static_pattern(), None);
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["%.o:", "%.c"]
        );

        let makefile = parse_bsd("a b &: c\n");
        let rule = makefile.rules().next().unwrap();
        assert!(!rule.is_grouped());
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a", "b", "&"]);
    }

    #[test]
    fn test_target_local_assignment_with_empty_name() {
        // BSD make: "one: ignoring ' = three' as the variable name '' expands
        // to empty". GNU make reports "empty variable name".
        let makefile = parse_bsd("one two:=three\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["one", "two"]);
        let var = rule.scoped_assignment().unwrap();
        assert_eq!(var.name(), None);
        assert_eq!(var.assignment_operator(), Some("=".to_string()));
        assert_eq!(var.raw_value(), Some("three".to_string()));
        assert_ne!(errors_with(MakefileVariant::GNUMake, "one two:=three\n"), 0);
    }
}
