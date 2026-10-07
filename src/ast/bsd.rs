//! Accessors for BSD make constructs: `.for` loops and single-line
//! directives such as `.undef` or `.error`.

use super::conditional::ConditionalItem;
use super::makefile::MakefileItem;
use super::{logical_text, LineSyntax};
use crate::lossless::{Directive, ForLoop, SyntaxNode, SyntaxToken};
use crate::SyntaxKind::*;
use rowan::ast::AstNode;

/// Return the token holding the directive name at the start of `node`,
/// together with the keyword normalized to a leading dot followed by the
/// name, e.g. `.if` for both `.if` and `.  if`. In the latter form the
/// returned token is `if`, without the dot.
///
/// For nmake directives such as `!  if` the keyword is `!` followed by the
/// name in upper case, e.g. `!IF`, and the returned token is the name.
///
/// For non-BSD constructs such as GNU `ifdef` the keyword is the first
/// identifier as-is.
pub(crate) fn keyword_token(node: &SyntaxNode) -> Option<(SyntaxToken, String)> {
    let mut tokens = node.children_with_tokens().filter_map(|it| it.into_token());
    let nmake = tokens
        .clone()
        .next()
        .is_some_and(|t| t.kind() == OPERATOR && t.text() == "!");
    let mut identifiers = tokens.by_ref().filter(|t| t.kind() == IDENTIFIER);
    let first = identifiers.next()?;
    if nmake {
        let keyword = format!("!{}", first.text().to_ascii_uppercase());
        Some((first, keyword))
    } else if first.text() == "." {
        let name = identifiers.next()?;
        let keyword = format!(".{}", name.text());
        Some((name, keyword))
    } else {
        let keyword = first.text().to_string();
        Some((first, keyword))
    }
}

/// The source range of the directive keyword at the start of `node`, from
/// any `.` or `!` before the name up to the end of the name token returned
/// by [`keyword_token`], so `.  if` is covered entirely.
pub(crate) fn keyword_range(node: &SyntaxNode) -> Option<rowan::TextRange> {
    let (token, _) = keyword_token(node)?;
    let first = node.children_with_tokens().find_map(|it| it.into_token())?;
    Some(first.text_range().cover(token.text_range()))
}

/// The normalized directive keyword at the start of `node`; see
/// [`keyword_token`].
pub(crate) fn directive_keyword(node: &SyntaxNode) -> Option<String> {
    keyword_token(node).map(|(_, keyword)| keyword)
}

/// How the make implementation that reads the directive at the start of
/// `node` forms its logical line: nmake for `!` directives and BSD make
/// otherwise.
fn directive_line_syntax(node: &SyntaxNode) -> LineSyntax {
    match node.first_token() {
        Some(t) if t.kind() == OPERATOR && t.text() == "!" => LineSyntax::NMake,
        _ => LineSyntax::Bsd,
    }
}

/// Return the trimmed logical text of the first EXPR child of `node`, as
/// read by the make implementation of the directive.
fn expr_text(node: &SyntaxNode) -> Option<String> {
    let expr = node.children().find(|it| it.kind() == EXPR)?;
    let tokens = expr
        .descendants_with_tokens()
        .filter_map(|it| it.into_token());
    let text = logical_text(&expr, tokens, directive_line_syntax(node), true);
    Some(text.trim().to_string())
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
    ///
    /// This is the text as BSD make reads it: line continuations are
    /// collapsed, keeping the whitespace before them, `\#` is unescaped
    /// and trailing whitespace is removed.
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
    ///         _ => panic!("expected recipe"),
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
    /// For nmake, the keyword is the `!` followed by the directive name in
    /// upper case, e.g. `!UNDEF` for `! undef`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem, MakefileVariant};
    /// let makefile: Makefile = ".  error unsupported platform\n".parse().unwrap();
    /// let MakefileItem::Directive(d) = makefile.items().next().unwrap() else { panic!() };
    /// assert_eq!(d.keyword(), Some(".error".to_string()));
    /// assert_eq!(d.argument(), Some("unsupported platform".to_string()));
    ///
    /// let makefile =
    ///     Makefile::parse_with_variant("!message Building\n", MakefileVariant::NMake).tree();
    /// let MakefileItem::Directive(d) = makefile.items().next().unwrap() else { panic!() };
    /// assert_eq!(d.keyword(), Some("!MESSAGE".to_string()));
    /// assert_eq!(d.argument(), Some("Building".to_string()));
    /// ```
    pub fn keyword(&self) -> Option<String> {
        directive_keyword(self.syntax())
    }

    /// The source range of the directive keyword, including the leading dot
    /// or `!` and any whitespace after it, as in `.  error`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem, MakefileVariant, TextRange};
    /// let makefile =
    ///     Makefile::parse_with_variant(".  undef X\n", MakefileVariant::BSDMake).tree();
    /// let Some(MakefileItem::Directive(d)) = makefile.items().next() else { panic!() };
    /// assert_eq!(d.keyword_range(), Some(TextRange::new(0.into(), 8.into())));
    /// ```
    pub fn keyword_range(&self) -> Option<rowan::TextRange> {
        keyword_range(self.syntax())
    }

    /// The unexpanded argument of the directive, if any.
    ///
    /// Line continuations are collapsed and `\#` is unescaped the way BSD
    /// make does, or nmake for `!` directives such as `!MESSAGE`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileItem};
    /// let makefile: Makefile = ".info a \\\n\tb\\#c # comment\n".parse().unwrap();
    /// let MakefileItem::Directive(d) = makefile.items().next().unwrap() else { panic!() };
    /// assert_eq!(d.argument(), Some("a  b#c".to_string()));
    /// ```
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
    use crate::{Makefile, MakefileItem, MakefileVariant, ParseErrorKind, Rule, TextRange};
    use rowan::ast::AstNode;

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
        assert_eq!(makefile.to_string(), ".ifdef DEBUG\nVAR = 1\n.endif\n");
    }

    #[test]
    fn test_add_else() {
        let makefile = parse_ok(".if 1\nA=1\n.endif\n");
        let mut cond = makefile.conditionals().next().unwrap();
        let temp = parse_ok("A=2\n");
        let var = temp.variable_definitions().next().unwrap();
        cond.add_else_item(MakefileItem::Variable(var));
        assert_eq!(makefile.to_string(), ".if 1\nA=1\n.else\nA=2\n.endif\n");
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
    fn test_directive_argument_logical_line() {
        // As in bmake, whitespace before a continuation is kept, `\#` is
        // unescaped and trailing whitespace is removed.
        let text = ".info a \\\n\t\tb\\#c # comment\n.error \\\n  x  \\\n\n";
        for variant in [None, Some(MakefileVariant::BSDMake)] {
            let parsed = match variant {
                Some(v) => Makefile::parse_with_variant(text, v),
                None => Makefile::parse(text),
            };
            assert_eq!(parsed.errors(), &[]);
            let makefile = parsed.tree();
            assert_eq!(makefile.to_string(), text);
            let arguments: Vec<_> = makefile
                .items()
                .map(|item| match item {
                    MakefileItem::Directive(d) => d.argument(),
                    _ => panic!("expected directive"),
                })
                .collect();
            assert_eq!(
                arguments,
                vec![Some("a  b#c".to_string()), Some("x".to_string())],
                "{variant:?}"
            );
        }
    }

    #[test]
    fn test_nmake_directive_argument_logical_line() {
        let text = "!MESSAGE a \\\n  b\n";
        let parsed = Makefile::parse_with_variant(text, MakefileVariant::NMake);
        assert_eq!(parsed.errors(), &[]);
        let makefile = parsed.tree();
        assert_eq!(makefile.to_string(), text);
        let Some(MakefileItem::Directive(d)) = makefile.items().next() else {
            panic!("expected directive");
        };
        assert_eq!(d.argument(), Some("a  b".to_string()));
    }

    #[test]
    fn test_for_loop_list_logical_line() {
        let text = ".for x in a \\\n\t\tb\\#c # comment\n.endfor\n";
        for variant in [None, Some(MakefileVariant::BSDMake)] {
            let parsed = match variant {
                Some(v) => Makefile::parse_with_variant(text, v),
                None => Makefile::parse(text),
            };
            assert_eq!(parsed.errors(), &[]);
            let makefile = parsed.tree();
            assert_eq!(makefile.to_string(), text);
            let Some(MakefileItem::ForLoop(f)) = makefile.items().next() else {
                panic!("expected for loop");
            };
            assert_eq!(f.variables(), vec!["x"], "{variant:?}");
            assert_eq!(f.list(), Some("a  b#c".to_string()), "{variant:?}");
        }
    }

    #[test]
    fn test_for_loop_list_continued_modifier() {
        // From NetBSD's share/mk/bsd.clean.mk.
        let makefile = parse_ok(concat!(
            ".for _d in ${\"${.OBJDIR}\" == \"${.CURDIR}\" || \"${MKCLEANSRC}\" == \"no\" \\\n",
            "\t\t:? ${.OBJDIR} \\\n",
            "\t\t:  ${.OBJDIR} ${.CURDIR} }\n",
            ".endfor\n"
        ));
        let Some(MakefileItem::ForLoop(f)) = makefile.items().next() else {
            panic!("expected for loop");
        };
        assert_eq!(f.variables(), vec!["_d"]);
        assert_eq!(
            f.list(),
            Some(
                "${\"${.OBJDIR}\" == \"${.CURDIR}\" || \"${MKCLEANSRC}\" == \"no\"  \
                 :? ${.OBJDIR}  :  ${.OBJDIR} ${.CURDIR} }"
                    .to_string()
            )
        );
    }

    #[test]
    fn test_condition_logical_line() {
        let makefile = parse_ok(".if ${X:Ua\\#b} == x \\\n\t|| ${Y}\n.endif\n");
        let branch = makefile
            .conditionals()
            .next()
            .unwrap()
            .branches()
            .next()
            .unwrap();
        assert_eq!(
            branch.condition(),
            Some("${X:Ua#b} == x  || ${Y}".to_string())
        );
        assert_eq!(
            branch.condition_for(MakefileVariant::BSDMake),
            Some("${X:Ua#b} == x  || ${Y}".to_string())
        );
        assert_eq!(
            branch.bsd_condition(),
            Some(Ok("${X:Ua#b} == x || ${Y}".parse().unwrap()))
        );

        // GNU make does not unescape `\#` in conditionals.
        let makefile = parse_ok("ifeq (a\\#b,c)\nendif\n");
        let branch = makefile
            .conditionals()
            .next()
            .unwrap()
            .branches()
            .next()
            .unwrap();
        assert_eq!(branch.condition(), Some("(a\\#b,c)".to_string()));
        assert_eq!(
            branch.ifeq_args(),
            Some(("a\\#b".to_string(), "c".to_string()))
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
        assert!(parsed.is_ok());
    }

    #[test]
    fn test_conditional_in_recipe() {
        let makefile = parse_ok("all:\n.if defined(X)\n\techo x\n.endif\n\techo y\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo x", "echo y"]);
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
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo ${d}"]);
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
        assert!(!parsed.is_ok());
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
        assert!(parsed.is_ok());
        let var = parsed.tree().variable_definitions().next().unwrap();
        assert_eq!(var.name(), Some("a:b".to_string()));
        assert_eq!(var.raw_value(), Some("c".to_string()));

        let makefile = parse_ok("a:b=c\n");
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_name_with_space_is_not_assignment() {
        let parsed = Makefile::parse("VARIABLE NAME=\tvalue\n");
        assert!(!parsed.is_ok());
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
        // With whitespace after the name, this is still a directive,
        // although make rejects the condition.
        let parsed = Makefile::parse(".info = x\n.if == \"\"\n.endif\n");
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["Malformed conditional (== \"\")"]
        );
        let makefile = parsed.tree();
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
        assert!(!parsed.is_ok());
        assert_eq!(parsed.tree().includes().count(), 0);
    }

    #[test]
    fn test_bsd_variant_ignores_gnu_conditionals() {
        let parsed = Makefile::parse_with_variant("ifdef X\nendif\n", MakefileVariant::BSDMake);
        assert!(!parsed.is_ok());
        assert_eq!(parsed.tree().conditionals().count(), 0);

        let parsed = Makefile::parse_with_variant(".ifdef X\n.endif\n", MakefileVariant::BSDMake);
        assert!(parsed.is_ok());
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

    #[test]
    fn test_missing_condition_bsd_variant() {
        let parsed = Makefile::parse_with_variant(".ifdef\n.endif\n", MakefileVariant::BSDMake);
        assert_eq!(
            parsed
                .errors()
                .iter()
                .map(|e| (e.line, e.message.as_str()))
                .collect::<Vec<_>>(),
            vec![(1, "expected condition after .ifdef")]
        );
    }

    #[test]
    fn test_malformed_condition() {
        // BSD make rejects text after a complete condition.
        let cases = [
            (".if 1 junk\n.endif\n", "Malformed conditional (1 junk)"),
            (".if (1) junk\n.endif\n", "Malformed conditional ((1) junk)"),
            (
                ".if 1 && 2 junk\n.endif\n",
                "Malformed conditional (1 && 2 junk)",
            ),
            (".if 1)\n.endif\n", "Malformed conditional (1))"),
            (
                ".if ${X} \\\n  junk # c\n.endif\n",
                "Malformed conditional (${X}  junk)",
            ),
            (".ifdef X Y\n.endif\n", "Malformed conditional (X Y)"),
            (".ifndef X Y Z\n.endif\n", "Malformed conditional (X Y Z)"),
            (".ifmake X Y\n.endif\n", "Malformed conditional (X Y)"),
            (".ifnmake X Y\n.endif\n", "Malformed conditional (X Y)"),
            (".ifdef X)\n.endif\n", "Malformed conditional (X))"),
            (
                ".if 0\n.elif 1 junk\n.endif\n",
                "Malformed conditional (1 junk)",
            ),
            (
                ".if 0\n.elifdef X Y\n.endif\n",
                "Malformed conditional (X Y)",
            ),
            (
                ".if 0\n.elifndef X Y\n.endif\n",
                "Malformed conditional (X Y)",
            ),
            (
                ".if 0\n.elifmake X Y\n.endif\n",
                "Malformed conditional (X Y)",
            ),
            (
                ".if 0\n.elifnmake X Y\n.endif\n",
                "Malformed conditional (X Y)",
            ),
        ];
        for (text, message) in cases {
            let line = if text.contains(".elif") || text.contains("\\\n") {
                2
            } else {
                1
            };
            // GNU make rejects these lines too.
            for parsed in [
                Makefile::parse_with_variant(text, MakefileVariant::BSDMake),
                Makefile::parse(text),
            ] {
                assert_eq!(parsed.tree().to_string(), text);
                assert_eq!(
                    parsed
                        .errors()
                        .iter()
                        .map(|e| (e.line, e.kind(), e.message.as_str()))
                        .collect::<Vec<_>>(),
                    vec![(line, ParseErrorKind::InvalidConditional, message)],
                    "{text:?}"
                );
            }
        }
    }

    #[test]
    fn test_malformed_condition_range() {
        let parsed = Makefile::parse_with_variant(
            ".if ${X} \\\n  junk # c\n.endif\n",
            MakefileVariant::BSDMake,
        );
        let ranges: Vec<_> = parsed.positioned_errors().iter().map(|e| e.range).collect();
        assert_eq!(ranges, vec![TextRange::new(13.into(), 17.into())]);
    }

    #[test]
    fn test_well_formed_conditions() {
        for text in [
            ".if 1 # comment\n.endif\n",
            ".ifdef X || Y\n.endif\n",
            ".ifdef X&&Y\n.endif\n",
            ".ifdef !X\n.endif\n",
            ".ifdef (X)\n.endif\n",
            ".if 1 \\\n  && 2\n.endif\n",
            ".if ${X:U1} == 1\n.endif\n",
        ] {
            parse_bsd(text);
        }
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
        assert_eq!(makefile.to_string(), "VAR !=\techo\n");
        assert_eq!(var.assignment_operator(), Some("!=".to_string()));
    }

    #[test]
    fn test_try_set_assignment_operator_colons_after_name() {
        // BSD make reads the first colon of `::=` as part of the name.
        let makefile = parse_bsd("a:b=c\n");
        let mut var = makefile.variable_definitions().next().unwrap();
        assert!(var.try_set_assignment_operator("::=").is_err());
        assert_eq!(makefile.to_string(), "a:b=c\n");
        var.try_set_assignment_operator(":sh=").unwrap();
        assert_eq!(makefile.to_string(), "a:b:sh=c\n");
        assert_eq!(var.assignment_operator(), Some(":sh=".to_string()));
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
        assert!(parsed.is_ok());
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
        assert!(parsed.is_ok());
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
        assert!(parsed.is_ok());
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

    fn local_assignment(rule: &Rule) -> (Option<String>, String, String) {
        let var = rule.scoped_assignment().unwrap();
        (
            var.name(),
            var.assignment_operator().unwrap(),
            var.raw_value().unwrap(),
        )
    }

    #[test]
    fn test_target_local_assignment() {
        // From NetBSD make's var-scope-local.mk.
        for (text, name, op, value) in [
            ("t.o: VAR= local\n", "VAR", "=", "local"),
            ("t.o: VAR+= local\n", "VAR", "+=", "local"),
            ("t.o: VAR += to ${.TARGET}\n", "VAR", "+=", "to ${.TARGET}"),
            ("t.o: VAR= ${VAR}+local\n", "VAR", "=", "${VAR}+local"),
            ("t.o: VAR ?= first\n", "VAR", "?=", "first"),
            ("t.o: VAR := $${VAR}+local\n", "VAR", ":=", "$${VAR}+local"),
            ("t.o: VAR != echo output\n", "VAR", "!=", "echo output"),
            // Only one assignment per line: the rest of it is the value.
            ("all: X=1 Y=2\n", "X", "=", "1 Y=2"),
            ("all: \\\n  X=1\n", "X", "=", "1"),
            (".PHONY: X=1\n", "X", "=", "1"),
        ] {
            let makefile = parse_bsd(text);
            let rule = makefile.rules().next().unwrap();
            assert_eq!(rule.prerequisites().count(), 0, "{text:?}");
            assert_eq!(
                local_assignment(&rule),
                (Some(name.to_string()), op.to_string(), value.to_string()),
                "{text:?}"
            );
        }
    }

    #[test]
    fn test_target_local_assignment_after_sources() {
        // BSD make tries each source in turn as the start of an assignment.
        let makefile = parse_bsd("a_use: .USE VAR=use\n\t@echo ${VAR}\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec![".USE"]);
        assert_eq!(
            local_assignment(&rule),
            (Some("VAR".to_string()), "=".to_string(), "use".to_string())
        );
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["@echo ${VAR}"]);

        // `a b = c` is not an assignment, but `b = c` is.
        let makefile = parse_bsd("all: a b = c\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["a"]);
        assert_eq!(
            local_assignment(&rule),
            (Some("b".to_string()), "=".to_string(), "c".to_string())
        );

        // GNU make takes these as prerequisites.
        let parsed = Makefile::parse_with_variant("all: a b = c\n", MakefileVariant::GNUMake);
        let rule = parsed.tree().rules().next().unwrap();
        assert!(rule.scoped_assignment().is_none());
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["a", "b", "=", "c"]
        );
    }

    #[test]
    fn test_target_local_assignment_with_inline_command() {
        // BSD make splits off the command at the first `;` before looking
        // for an assignment.
        let makefile = parse_bsd("all: X=1; echo $X\n\techo two\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            local_assignment(&rule),
            (Some("X".to_string()), "=".to_string(), "1".to_string())
        );
        assert_eq!(
            rule.recipes().collect::<Vec<_>>(),
            vec!["echo $X", "echo two"]
        );

        let makefile = parse_bsd("all: X; Y=1\n");
        let rule = makefile.rules().next().unwrap();
        assert!(rule.scoped_assignment().is_none());
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["X"]);
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["Y=1"]);
    }

    #[test]
    fn test_target_local_assignment_followed_by_commands() {
        let makefile = parse_bsd("one two:=three\n\techo $@\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            local_assignment(&rule),
            (None, "=".to_string(), "three".to_string())
        );
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo $@"]);
    }

    /// Check that `makefile` has the same tree as when its text is parsed
    /// again for BSD make.
    fn assert_matches_bsd_reparse(makefile: &Makefile) {
        let reparsed = parse_bsd(&makefile.to_string());
        assert_eq!(
            format!("{:#?}", makefile.syntax()),
            format!("{:#?}", reparsed.syntax())
        );
    }

    #[test]
    fn test_target_local_assignment_blank_lines() {
        // Commands after blank lines belong to the rule, as in other rules.
        let makefile = parse_bsd("a: X=1\n\n\techo $X\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo $X"]);
        assert_eq!(rule.syntax().to_string(), "a: X=1\n\n\techo $X\n");

        // Without commands, the blank lines and comments after it are not
        // part of the rule.
        for (text, rule_text) in [
            ("a: X=1\n\nB=2\n", "a: X=1\n"),
            ("a: X=1\n# c\nB=2\n", "a: X=1\n"),
            ("a b:=1\n\nB=2\n", "a b:=1\n"),
            ("a: X=1; echo\n\nB=2\n", "a: X=1; echo\n\n"),
        ] {
            let makefile = parse_bsd(text);
            let rule = makefile.rules().next().unwrap();
            assert_eq!(rule.syntax().to_string(), rule_text, "{text:?}");
        }
    }

    #[test]
    fn test_remove_command_after_target_local_assignment() {
        for (text, expected) in [
            ("a: X=1\n\n\techo $X\n", "a: X=1\n\n"),
            ("a: X=1\n# c\n\techo $X\nB=2\n", "a: X=1\n# c\nB=2\n"),
            (
                "a: X=1\n\techo $X\n\n# c\n\techo\n",
                "a: X=1\n\techo $X\n\n# c\n",
            ),
            ("a: X=1; echo $X\n\n# c\n", "a: X=1\n\n# c\n"),
        ] {
            let makefile = parse_bsd(text);
            let mut rule = makefile.rules().next().unwrap();
            let count = rule.recipe_count();
            assert!(rule.remove_command(count - 1), "{text:?}");
            assert_eq!(makefile.to_string(), expected, "{text:?}");
            assert_matches_bsd_reparse(&makefile);
        }
    }

    #[test]
    fn test_add_rule_after_target_local_assignment() {
        let mut makefile = parse_bsd("a: X=1\n");
        makefile.add_rule("b");
        assert_eq!(makefile.to_string(), "a: X=1\n\nb:\n");
        assert_matches_bsd_reparse(&makefile);

        let mut makefile = parse_bsd("a: X=1\n\techo $X\n");
        makefile.add_rule("b");
        assert_eq!(makefile.to_string(), "a: X=1\n\techo $X\n\nb:\n");
        assert_matches_bsd_reparse(&makefile);
    }

    #[test]
    fn test_no_target_local_assignment_for_special_sources() {
        // These special targets don't take their sources as assignments.
        for (text, sources) in [
            (
                ".SHELL: name=\"sh\" path=/bin/sh\n",
                vec!["name=\"sh\"", "path=/bin/sh"],
            ),
            (
                ".SHELL: \\\n\tname=\"sh\" \\\n\tpath=/bin/sh\n",
                vec!["name=\"sh\"", "path=/bin/sh"],
            ),
            (".PATH: a=b\n", vec!["a=b"]),
            (".PATH.c: a=b\n", vec!["a=b"]),
            (".SUFFIXES: .a=b\n", vec![".a=b"]),
            (".MAKEFLAGS: X=1\n", vec!["X=1"]),
            (".NOTPARALLEL: X=1\n", vec!["X=1"]),
        ] {
            let makefile = parse_bsd(text);
            let rule = makefile.rules().next().unwrap();
            assert!(rule.scoped_assignment().is_none(), "{text:?}");
            assert_eq!(
                rule.prerequisites().collect::<Vec<_>>(),
                sources,
                "{text:?}"
            );
        }
    }

    #[test]
    fn test_unbalanced_brackets_make_dependency_line() {
        // BSD make's Parse_IsVar counts brackets and rejects these as
        // assignments, so they are dependency lines whose sources form a
        // target-local assignment to an empty variable name.
        for (text, target, double_colon, op, value) in [
            ("a}b := 1\n", "a}b", false, "=", "1"),
            (")x := 1\n", ")x", false, "=", "1"),
            ("a}b ::= 1\n", "a}b", true, "=", "1"),
            ("a}b :::= 1\n", "a}b", true, ":=", "1"),
            ("a}b != 1\n", "a}b", false, "=", "1"),
        ] {
            let makefile = parse_bsd(text);
            assert_eq!(makefile.items().count(), 1, "{text:?}");
            let rule = makefile.rules().next().unwrap();
            assert_eq!(rule.targets().collect::<Vec<_>>(), vec![target], "{text:?}");
            assert_eq!(rule.is_double_colon(), double_colon, "{text:?}");
            assert_eq!(rule.prerequisites().count(), 0, "{text:?}");
            let var = rule.scoped_assignment().unwrap();
            assert_eq!(var.name(), None, "{text:?}");
            assert_eq!(var.assignment_operator(), Some(op.to_string()), "{text:?}");
            assert_eq!(var.raw_value(), Some(value.to_string()), "{text:?}");
        }
        // GNU make assigns to a variable named `a}b`.
        let parsed = Makefile::parse_with_variant("a}b := 1\n", MakefileVariant::GNUMake);
        assert!(parsed.is_ok());
        assert_eq!(
            parsed.tree().variable_definitions().next().unwrap().name(),
            Some("a}b".to_string())
        );
    }

    #[test]
    fn test_multiple_targets_with_shell_assignment_operator() {
        // `a b != c` is not an assignment as its left-hand side is not a
        // single word, so BSD make reads the dependency operator `!`.
        let makefile = parse_bsd("a b != c\n");
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a", "b"]);
        let var = rule.scoped_assignment().unwrap();
        assert_eq!(var.name(), None);
        assert_eq!(var.assignment_operator(), Some("=".to_string()));
        assert_eq!(var.raw_value(), Some("c".to_string()));
        assert_ne!(errors_with(MakefileVariant::GNUMake, "a b != c\n"), 0);
    }

    #[test]
    fn test_variable_name_with_braces_in_expression() {
        // From NetBSD make's cond-func.mk: bmake ends the expression at the
        // first `}`, so the name is `VAR{value` followed by `}`, but like
        // Parse_IsVar the name ends at the `=` as the braces balance.
        for (code, name) in [
            ("${:UVAR{value}}=\tx\n", "${:UVAR{value}}"),
            ("${:UV{a}} = x\n", "${:UV{a}}"),
        ] {
            let makefile = parse_bsd(code);
            let vars: Vec<_> = makefile.variable_definitions().collect();
            assert_eq!(vars.len(), 1, "{code:?}");
            assert_eq!(vars[0].name(), Some(name.to_string()), "{code:?}");
            assert_eq!(vars[0].raw_value(), Some("x".to_string()), "{code:?}");
        }
        // The `(` leaves the level at 1, so this is not an assignment, and
        // bmake reports an archive specification error.
        let parsed = Makefile::parse_with_variant("A${:U(}= x\n", MakefileVariant::BSDMake);
        assert!(!parsed.errors().is_empty());
        assert_eq!(parsed.tree().variable_definitions().count(), 0);
    }

    #[test]
    fn test_conditional_name_ends_at_non_letter() {
        // BSD make reads the name of a conditional directive up to the
        // first character that is not a letter, as in NetBSD make's
        // directive-if.mk.
        for code in [
            ".if0\nA=1\n.endif\n",
            ". if1\nA=1\n.endif\n",
            ".ifdef0\nA=1\n.endif\n",
            ".if 0\n.elif1\nA=1\n.endif\n",
            ".if1x\nA=1\n.endif\n",
        ] {
            let parsed = Makefile::parse_with_variant(code, MakefileVariant::BSDMake);
            assert_eq!(parsed.errors(), &[], "{code:?}");
            let makefile = parsed.tree();
            assert_eq!(makefile.conditionals().count(), 1, "{code:?}");
            assert_eq!(makefile.to_string(), code);
        }
        for (code, message) in [
            (
                ".if 1\nA=1\n.endif0\n",
                "The .endif directive does not take arguments",
            ),
            (
                ".if 1\nA=1\n.else0\n.endif\n",
                "The .else directive does not take arguments",
            ),
        ] {
            let parsed = Makefile::parse_with_variant(code, MakefileVariant::BSDMake);
            let messages: Vec<_> = parsed.errors().iter().map(|e| e.message.as_str()).collect();
            assert_eq!(messages, vec![message], "{code:?}");
            assert_eq!(parsed.tree().to_string(), code);
        }
    }

    #[test]
    fn test_for_variable_names() {
        // BSD make takes any word without `$ : \\ ( ) { }` as a loop
        // variable, as in NetBSD make's directive-for-escape.mk.
        for (code, variables) in [
            (".for , in 1\nX+=$,\n.endfor\n", vec![","]),
            (".for a=b c.d in 1 2\n.endfor\n", vec!["a=b", "c.d"]),
            (".for a\\\n  b in 1 2\n.endfor\n", vec!["a", "b"]),
        ] {
            let parsed = Makefile::parse_with_variant(code, MakefileVariant::BSDMake);
            assert_eq!(parsed.errors(), &[], "{code:?}");
            let makefile = parsed.tree();
            let Some(MakefileItem::ForLoop(for_loop)) = makefile.items().next() else {
                panic!("{code:?}");
            };
            assert_eq!(for_loop.variables(), variables, "{code:?}");
            assert_eq!(makefile.to_string(), code);
        }
        for (code, message) in [
            (
                ".for a:b in 1\n.endfor\n",
                "Invalid character \":\" in .for loop variable name",
            ),
            (
                ".for $$ in 1\n.endfor\n",
                "Invalid character \"$\" in .for loop variable name",
            ),
        ] {
            let parsed = Makefile::parse_with_variant(code, MakefileVariant::BSDMake);
            let messages: Vec<_> = parsed.errors().iter().map(|e| e.message.as_str()).collect();
            assert_eq!(messages, vec![message], "{code:?}");
            assert_eq!(parsed.tree().to_string(), code);
        }
    }

    #[test]
    fn test_directive_keyword_range() {
        let text = ".undef X\n.  error a \\\n b\n";
        let makefile = Makefile::parse_with_variant(text, MakefileVariant::BSDMake).tree();
        let ranges: Vec<_> = makefile
            .items()
            .map(|item| {
                let MakefileItem::Directive(d) = item else {
                    panic!("expected a directive");
                };
                &text[d.keyword_range().unwrap()]
            })
            .collect();
        assert_eq!(ranges, vec![".undef", ".  error"]);
    }

    #[test]
    fn test_directive_keyword_range_nmake() {
        let text = "! message hi\n";
        let makefile = Makefile::parse_with_variant(text, MakefileVariant::NMake).tree();
        let Some(MakefileItem::Directive(d)) = makefile.items().next() else {
            panic!("expected a directive");
        };
        assert_eq!(
            d.keyword_range(),
            Some(rowan::TextRange::new(0.into(), 9.into()))
        );
    }
}
