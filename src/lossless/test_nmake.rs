use super::*;
use crate::MakefileItem;
use crate::MakefileVariant;

fn parse_nmake(text: &str) -> Makefile {
    let parsed = Makefile::parse_with_variant(text, MakefileVariant::NMake);
    assert_eq!(parsed.errors(), &[]);
    let makefile = parsed.tree();
    assert_eq!(makefile.to_string(), text);
    makefile
}

fn branches(cond: &Conditional) -> Vec<(Option<String>, Option<String>)> {
    cond.branches()
        .map(|b| (b.conditional_type(), b.condition()))
        .collect()
}

#[test]
fn test_conditional() {
    let makefile = parse_nmake(
            "!IF \"$(CFG)\" == \"Debug\" # comment\nX=1\n!ELSEIF $(A) > 2\nX=2\n!ELSE IF 3\nX=3\n!else\nX=4\n!endif\n",
        );
    let items: Vec<_> = makefile.items().collect();
    assert_eq!(items.len(), 1);
    let cond = makefile.conditionals().next().unwrap();
    assert_eq!(cond.conditional_type(), Some("!IF".to_string()));
    assert_eq!(
        cond.condition(),
        Some("\"$(CFG)\" == \"Debug\"".to_string())
    );
    assert_eq!(
        branches(&cond),
        vec![
            (
                Some("!IF".to_string()),
                Some("\"$(CFG)\" == \"Debug\"".to_string())
            ),
            (Some("!IF".to_string()), Some("$(A) > 2".to_string())),
            (Some("!IF".to_string()), Some("3".to_string())),
            (None, None),
        ]
    );
    assert_eq!(
        makefile
            .variable_definitions()
            .map(|v| v.raw_value().unwrap())
            .collect::<Vec<_>>(),
        vec!["1", "2", "3", "4"]
    );
}

#[test]
fn test_ifdef() {
    let makefile = parse_nmake(
        "!  IFDEF DEBUG\nX=1\n!ELSEIFNDEF NODEBUG\nX=2\n! else ifdef OTHER\nX=3\n!ENDIF\n",
    );
    let cond = makefile.conditionals().next().unwrap();
    assert_eq!(
        branches(&cond),
        vec![
            (Some("!IFDEF".to_string()), Some("DEBUG".to_string())),
            (Some("!IFNDEF".to_string()), Some("NODEBUG".to_string())),
            (Some("!IFDEF".to_string()), Some("OTHER".to_string())),
        ]
    );
}

#[test]
fn test_nested() {
    let makefile = parse_nmake("!IFDEF A\n!IFNDEF B\nX=1\n!ENDIF\n!ENDIF\n");
    let outer = makefile.conditionals().next().unwrap();
    let Some(MakefileItem::Conditional(inner)) = outer.if_items().next() else {
        panic!("expected nested conditional");
    };
    assert_eq!(inner.conditional_type(), Some("!IFNDEF".to_string()));
    assert_eq!(inner.condition(), Some("B".to_string()));
}

#[test]
fn test_conditional_in_rule() {
    let text = "all:\n!IF 1\n\techo one\n!ELSE\n\techo two\n!ENDIF\n\techo done\n";
    let makefile = parse_nmake(text);
    assert_eq!(
            node_kinds(makefile.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    RECIPE\n    CONDITIONAL_ELSE\n    RECIPE\n    CONDITIONAL_ENDIF\n  RECIPE\n"
        );
}

#[test]
fn test_conditional_after_rule() {
    // A conditional without recipe lines ends the rule, also when it
    // is indented after the `!`.
    let makefile = parse_nmake("all:\n\techo a\n\n!  IFDEF X\nY=1\n!  ENDIF\n");
    assert_eq!(
            node_kinds(makefile.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\n"
        );
    let makefile = parse_nmake("all:\n\techo a\n\n!  IFDEF X\n\techo b\n!  ENDIF\n");
    assert_eq!(
            node_kinds(makefile.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    RECIPE\n    CONDITIONAL_ENDIF\n"
        );
}

#[test]
fn test_include() {
    let makefile = parse_nmake("!INCLUDE <win32.mak>\n!include config.mak\n");
    let includes: Vec<_> = makefile.includes().collect();
    assert_eq!(
        includes.iter().map(|i| i.path()).collect::<Vec<_>>(),
        vec![
            Some("win32.mak".to_string()),
            Some("config.mak".to_string())
        ]
    );
    assert!(!includes[0].is_optional());
    includes[0].clone().set_path("other.mak").unwrap();
    assert_eq!(includes[0].path(), Some("other.mak".to_string()));
    includes[1].clone().set_path("a#b.mak").unwrap();
    assert_eq!(includes[1].path(), Some("a#b.mak".to_string()));
    assert_eq!(
        makefile.to_string(),
        "!INCLUDE <other.mak>\n!include a^#b.mak\n"
    );
}

#[test]
fn test_include_caret_escapes() {
    let code = "!INCLUDE a^#b.mak # c\n!INCLUDE <a^^^#^\\>\n!INCLUDE a^\\\nX = 1\n";
    let makefile = parse_nmake(code);
    assert_eq!(makefile.to_string(), code);
    assert_eq!(
        makefile.includes().map(|i| i.path()).collect::<Vec<_>>(),
        vec![
            Some("a#b.mak".to_string()),
            Some("a^#\\".to_string()),
            Some("a\\".to_string()),
        ]
    );
    assert_eq!(makefile.variable_definitions().count(), 1);
}

#[test]
fn test_include_set_path_caret_escapes() {
    for (code, path, expected) in [
        ("!INCLUDE old.mak\n", "a#b", "!INCLUDE a^#b\n"),
        ("!INCLUDE <old.mak>\n", "a#b", "!INCLUDE <a^#b>\n"),
        ("!INCLUDE old.mak\n", "a^#b", "!INCLUDE a^^^#b\n"),
        ("!INCLUDE old.mak\n", "a^b", "!INCLUDE a^b\n"),
        ("!INCLUDE old.mak # c\n", "a\\", "!INCLUDE a^\\ # c\n"),
        ("!INCLUDE old.mak\n", "a\\", "!INCLUDE a^\\\n"),
    ] {
        let makefile = parse_nmake(code);
        let mut include = makefile.includes().next().unwrap();
        include.set_path(path).unwrap();
        assert_eq!(makefile.to_string(), expected, "{path:?}");
        assert_eq!(include.path(), Some(path.to_string()), "{path:?}");
    }
}

#[test]
fn test_include_set_quoted_path_carets() {
    // Carets in a quoted string are literal, so the path is not escaped.
    for path in ["a^:b", "a^^b", "a\\"] {
        let makefile = parse_nmake("!INCLUDE \"old.mak\"\n");
        let mut include = makefile.includes().next().unwrap();
        include.set_path(path).unwrap();
        assert_eq!(makefile.to_string(), format!("!INCLUDE \"{path}\"\n"));
        assert_eq!(include.path(), Some(path.to_string()), "{path:?}");
    }
    // There is no documented way to write a `#` in a quoted string.
    let makefile = parse_nmake("!INCLUDE \"old.mak\"\n");
    let mut include = makefile.includes().next().unwrap();
    assert!(include.set_path("a#b").is_err());
    assert_eq!(makefile.to_string(), "!INCLUDE \"old.mak\"\n");
}

#[test]
fn test_include_set_optional() {
    let makefile = parse_nmake("!INCLUDE config.mak\n");
    let mut include = makefile.includes().next().unwrap();
    let Err(Error::Parse(err)) = include.set_optional(true) else {
        panic!("expected an error");
    };
    assert_eq!(
        err.errors[0].message,
        "nmake has no optional include directive"
    );
    include.set_optional(false).unwrap();
    assert_eq!(makefile.to_string(), "!INCLUDE config.mak\n");
}

#[test]
fn test_directives() {
    let makefile = parse_nmake(
        "!UNDEF FOO\n!MESSAGE Building $(PROJ)\n!ERROR unsupported\n!CMDSWITCHES +D -N\n",
    );
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
            ("!UNDEF".to_string(), Some("FOO".to_string())),
            ("!MESSAGE".to_string(), Some("Building $(PROJ)".to_string())),
            ("!ERROR".to_string(), Some("unsupported".to_string())),
            ("!CMDSWITCHES".to_string(), Some("+D -N".to_string())),
        ]
    );
}

#[test]
fn test_add_else_and_endif() {
    let parsed = Makefile::parse_with_variant("!IFDEF A\nX=1\n", MakefileVariant::NMake);
    assert_eq!(
        parsed
            .errors()
            .iter()
            .map(|e| (e.kind(), e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(
            ParseErrorKind::MissingEndif,
            "unterminated !IF (missing !ENDIF)"
        )]
    );
    let makefile = parsed.tree();
    let mut cond = makefile.conditionals().next().unwrap();
    assert!(cond.add_endif().unwrap());
    let temp = parse_nmake("X=2\n");
    let var = temp.variable_definitions().next().unwrap();
    cond.add_else_item(MakefileItem::Variable(var));
    assert_eq!(makefile.code(), "!IFDEF A\nX=1\n!ELSE\nX=2\n!ENDIF\n");
}

#[test]
fn test_errors() {
    let parsed =
        Makefile::parse_with_variant("!ENDIF\n!ELSE\n!IF\n!ENDIF\n", MakefileVariant::NMake);
    assert_eq!(
        parsed
            .errors()
            .iter()
            .map(|e| (e.kind(), e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![
            (
                ParseErrorKind::ExtraneousEndif,
                "!ENDIF without matching !IF"
            ),
            (ParseErrorKind::ElseWithoutIf, "!ELSE without matching !IF"),
            (
                ParseErrorKind::InvalidConditional,
                "expected condition after !IF"
            ),
        ]
    );
    assert_eq!(parsed.tree().to_string(), "!ENDIF\n!ELSE\n!IF\n!ENDIF\n");
}

#[test]
fn test_other_variants_unaffected() {
    // Outside of nmake, `!IF` is not a directive.
    for variant in [MakefileVariant::GNUMake, MakefileVariant::BSDMake] {
        let parsed = Makefile::parse_with_variant("!IF 1\nX=1\n!ENDIF\n", variant);
        assert_eq!(parsed.tree().conditionals().count(), 0);
        assert_eq!(parsed.tree().to_string(), "!IF 1\nX=1\n!ENDIF\n");
    }
}

#[test]
fn test_not_in_first_column() {
    // nmake only recognizes directives starting in the first column.
    let parsed = Makefile::parse_with_variant("all: ; !IF 1\n", MakefileVariant::NMake);
    assert_eq!(parsed.errors(), &[]);
    assert_eq!(parsed.tree().conditionals().count(), 0);
}

fn node_kinds(node: &SyntaxNode) -> String {
    fn walk(node: &SyntaxNode, depth: usize, out: &mut String) {
        for child in node.children() {
            out.push_str(&format!("{}{:?}\n", "  ".repeat(depth), child.kind()));
            walk(&child, depth + 1, out);
        }
    }
    let mut out = String::new();
    walk(node, 0, &mut out);
    out
}

#[test]
fn test_inline_files() {
    // As in libisc.mak: the lines after a command with `<<` up to a
    // line starting with `<<` are the text of an inline file.
    let code = "\
a.dll : a.obj
    link @<<
  /out:a.dll a.obj
<<
    echo done

a.rc : a.manifest
    type <<$@ <<b.txt
#include <winuser.h>
1RT_MANIFEST \"a.manifest\"
<< KEEP
x: y
<<NOKEEP
";
    let makefile = parse_nmake(code);
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 2);
    assert_eq!(
        rules[0].recipes().collect::<Vec<_>>(),
        vec!["link @<<\n  /out:a.dll a.obj\n<<", "echo done"]
    );
    assert_eq!(
            rules[1].recipes().collect::<Vec<_>>(),
            vec!["type <<$@ <<b.txt\n#include <winuser.h>\n1RT_MANIFEST \"a.manifest\"\n<< KEEP\nx: y\n<<NOKEEP"]
        );

    let code = "a:\n    type <<\ntext\n";
    let parsed = Makefile::parse_with_variant(code, MakefileVariant::NMake);
    let messages: Vec<_> = parsed.errors().iter().map(|e| e.message.as_str()).collect();
    assert_eq!(messages, vec!["unterminated inline file (missing <<)"]);
    assert_eq!(parsed.tree().to_string(), code);
}

#[test]
fn test_substitution_strings_are_literal() {
    // nmake's "string1 and string2 can't invoke macros", so a
    // substitution ends at the first `)`, as in c-ares' Makefile.msvc.
    let makefile = parse_nmake("X = $(SRCS: = $(DIR)\\)\nY = $(SRCS:.c=.obj)\n");
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars.len(), 2);
    let references = |v: &VariableDefinition| -> Vec<String> {
        v.syntax()
            .descendants()
            .filter(|n| {
                n.kind() == EXPR
                    && n.parent().is_some_and(|p| p.kind() == EXPR)
                    && n.first_token().is_some_and(|t| t.kind() == DOLLAR)
            })
            .map(|n| n.text().to_string())
            .collect()
    };
    assert_eq!(references(&vars[0]), vec!["$(SRCS: = $(DIR)"]);
    assert_eq!(references(&vars[1]), vec!["$(SRCS:.c=.obj)"]);
    let parsed: Vec<_> = makefile
        .variable_references()
        .map(|r| r.parse(MakefileVariant::NMake))
        .collect();
    let sysv = |name: &str, from: &str, to: &str| {
        Ok(crate::ParsedReference {
            name: name.to_string(),
            modifiers: vec![crate::Modifier::SysVSubstitute {
                from: crate::ModifierArg::literal(from),
                to: crate::ModifierArg::literal(to),
            }],
        })
    };
    assert_eq!(
        parsed,
        vec![sysv("SRCS", " ", " $(DIR"), sysv("SRCS", ".c", ".obj")]
    );

    // Functions may contain references.
    let makefile = parse_nmake("X = $(subst $(A),b,c)\n");
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(references(&var), vec!["$(subst $(A),b,c)", "$(A)"]);
}

#[test]
fn test_all_dependents_reference() {
    // `$**` stands for all dependents, so the reference covers both `*`s.
    let code = "X = $**\na.exe: a.obj b.obj\n    link $** $***x\n    echo $(**F) $(@D) $(*B) $(?R) $(<F) $* $? $<\n";
    let makefile = parse_nmake(code);
    let references: Vec<_> = makefile
        .variable_references()
        .map(|r| (r.to_string(), r.name()))
        .collect();
    let r = |text: &str, name: &str| (text.to_string(), Some(name.to_string()));
    assert_eq!(
        references,
        vec![
            r("$**", "**"),
            r("$**", "**"),
            r("$**", "**"),
            r("$(**F)", "**F"),
            r("$(@D)", "@D"),
            r("$(*B)", "*B"),
            r("$(?R)", "?R"),
            r("$(<F)", "<F"),
            r("$*", "*"),
            r("$?", "?"),
            r("$<", "<"),
        ]
    );
    let ranges: Vec<_> = makefile
        .variable_references()
        .take(3)
        .map(|r| r.name_range().unwrap())
        .collect();
    assert_eq!(
        ranges,
        vec![
            rowan::TextRange::new(5.into(), 7.into()),
            rowan::TextRange::new(37.into(), 39.into()),
            rowan::TextRange::new(41.into(), 43.into()),
        ]
    );
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(
        format!("{:#?}", var.syntax()),
        r#"VARIABLE@0..8
  IDENTIFIER@0..1 "X"
  WHITESPACE@1..2 " "
  OPERATOR@2..3 "="
  WHITESPACE@3..4 " "
  EXPR@4..7
    EXPR@4..7
      DOLLAR@4..5 "$"
      TEXT@5..7 "**"
  NEWLINE@7..8 "\n"
"#
    );

    // Other makes take `$**` as `$*` followed by `*`.
    let makefile: Makefile = "X = $**\n".parse().unwrap();
    let references: Vec<_> = makefile
        .variable_references()
        .map(|r| (r.to_string(), r.name()))
        .collect();
    assert_eq!(references, vec![r("$*", "*")]);
}

#[test]
fn test_target_as_dependent() {
    // On a dependency line, `$$@` is the current target and `$$(@B)` a part
    // of it; the reference is the `$@` or `$(@B)` after the first `$`.
    let code = "a.obj b.obj: $$(@B).c $$@.h $$x\n\tcl $$@\n";
    let makefile = parse_nmake(code);
    let references: Vec<_> = makefile
        .variable_references()
        .map(|r| (r.to_string(), r.name(), r.text_range()))
        .collect();
    assert_eq!(
        references,
        vec![
            (
                "$(@B)".to_string(),
                Some("@B".to_string()),
                rowan::TextRange::new(14.into(), 19.into())
            ),
            (
                "$@".to_string(),
                Some("@".to_string()),
                rowan::TextRange::new(23.into(), 25.into())
            ),
        ]
    );
    let rule = makefile.rules().next().unwrap();
    assert_eq!(
        rule.prerequisites_for(MakefileVariant::NMake)
            .collect::<Vec<_>>(),
        vec!["$$(@B).c", "$$@.h", "$$x"]
    );

    // Other variants read `$$` as an escaped dollar.
    let makefile: Makefile = "a.obj: $$@.h\n".parse().unwrap();
    assert_eq!(makefile.variable_references().count(), 0);
}

#[test]
fn test_backslash_hash_starts_comment() {
    // nmake has no `\#` escape, so the `#` starts a comment, as it does
    // after any other character.
    let code = "a: b\\#c d\nX = e\\#f\n";
    let makefile = parse_nmake(code);
    let rule = makefile.rules().next().unwrap();
    assert_eq!(
        rule.prerequisites_for(MakefileVariant::NMake)
            .collect::<Vec<_>>(),
        vec!["b\\"]
    );
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.raw_value(), Some("e\\".to_string()));
    assert_eq!(var.value(MakefileVariant::NMake), Some("e\\".to_string()));
    let comments: Vec<_> = makefile
        .syntax()
        .descendants_with_tokens()
        .filter(|it| it.kind() == COMMENT)
        .map(|it| it.to_string())
        .collect();
    assert_eq!(comments, vec!["#c d", "#f"]);

    // Nor are the backslashes before a comment escapes.
    let makefile = parse_nmake("X = e\\\\#f\n");
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.value(MakefileVariant::NMake), Some("e\\\\".to_string()));
}
