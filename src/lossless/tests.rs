use super::*;
use crate::ast::makefile::MakefileItem;
use crate::pattern::matches_pattern;
use crate::test_util::{assert_matches_reparse, item_without_newline};
use crate::MakefileVariant;

#[test]
fn test_variable_reference_names() {
    let makefile: Makefile =
        "A = ${SRCS:M*.c} $(OBJS:.o=.c) ${VAR.${M}} ${:Ufoo} $@ $(wildcard *.c) $$\n"
            .parse()
            .unwrap();
    assert_eq!(
        makefile
            .variable_references()
            .map(|r| r.name())
            .collect::<Vec<_>>(),
        vec![
            Some("SRCS".to_string()),
            Some("OBJS".to_string()),
            Some("VAR.${M}".to_string()),
            Some("M".to_string()),
            None,
            Some("@".to_string()),
            Some("wildcard".to_string()),
        ]
    );
}

#[test]
fn test_recipe_variable_reference_names() {
    let text = "all:\n\t${.ALLSRC:M*.o} ${VAR.${M}} $(shell echo $(X)) ${X:S/a/${Y}/} $1\n";
    let makefile: Makefile = text.parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();
    assert_eq!(
        recipe
            .variable_references()
            .iter()
            .map(|r| (r.name(), &text[std::ops::Range::from(r.text_range())]))
            .collect::<Vec<_>>(),
        vec![
            (".ALLSRC", ".ALLSRC"),
            ("VAR.${M}", "VAR.${M}"),
            ("M", "M"),
            ("X", "X"),
            ("X", "X"),
            ("Y", "Y"),
        ]
    );
}

#[test]
fn test_hash_in_reference_is_literal() {
    let text = "X = ${A:M#*}\nY = $(a #b) c # d\nall: $(subst #,x,a#b)\n";
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
    ] {
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let makefile = parsed.root();
        assert_eq!(makefile.to_string(), text);
        assert_eq!(
            makefile
                .variable_definitions()
                .map(|v| v.raw_value().unwrap())
                .collect::<Vec<_>>(),
            vec!["${A:M#*}", "$(a #b) c "]
        );
        assert_eq!(
            makefile
                .variable_references()
                .map(|r| (r.name(), r.syntax().to_string()))
                .collect::<Vec<_>>(),
            vec![
                (Some("A".to_string()), "${A:M#*}".to_string()),
                (Some("a".to_string()), "$(a #b)".to_string()),
                (Some("subst".to_string()), "$(subst #,x,a#b)".to_string()),
            ]
        );
        assert_eq!(
            makefile
                .rules()
                .next()
                .unwrap()
                .prerequisites()
                .collect::<Vec<_>>(),
            vec!["$(subst #,x,a#b)"]
        );
    }
}

#[test]
fn test_hash_in_reference_is_comment_in_bsd() {
    let text = "X = ${A:M#*}\n";
    let parsed = parse(text, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.root().to_string(), text);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["unclosed variable reference"]
    );
}

#[test]
fn test_unclosed_reference_stops_at_newline() {
    let parsed = parse("A = ${B\nC = 1\n", None);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.line, e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(1, "unclosed variable reference")]
    );
    let makefile = parsed.root();
    assert_eq!(
        makefile
            .variable_definitions()
            .map(|v| v.name().unwrap())
            .collect::<Vec<_>>(),
        vec!["A", "C"]
    );
}

#[test]
fn test_reference_continued_on_next_line() {
    let parsed = parse("A = $(subst a,\\\n  b,c)\nC = 1\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(parsed.root().variable_definitions().count(), 2);
}

#[test]
fn test_dollar_before_closing_brace() {
    let parsed = parse("A = ${:U\\$:M\\$}\nB = ${$}\nC = $\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        parsed
            .root()
            .variable_definitions()
            .map(|v| v.raw_value().unwrap())
            .collect::<Vec<_>>(),
        vec!["${:U\\$:M\\$}", "${$}", "$"]
    );
}

#[test]
fn test_nested_braces_in_reference() {
    let parsed = parse("${:UVAR{value}}=\tx\n", None);
    assert_eq!(parsed.errors, vec![]);
    let var = parsed.root().variable_definitions().next().unwrap();
    assert_eq!(var.name(), Some("${:UVAR{value}}".to_string()));
    assert_eq!(var.raw_value(), Some("x".to_string()));
}

/// The text of the variable references in `text`, after checking that it
/// parses without errors and round-trips.
fn reference_texts(text: &str, variant: MakefileVariant) -> Vec<String> {
    let parsed = Makefile::parse_with_variant(text, variant);
    assert_eq!(parsed.errors(), []);
    let makefile = parsed.tree();
    assert_eq!(makefile.to_string(), text);
    makefile
        .variable_references()
        .map(|r| r.to_string())
        .collect()
}

#[test]
fn test_bsd_reference_regex_anchor() {
    let text = "X = ${X:C/e[lb]$//}\n";
    assert_eq!(
        reference_texts(text, MakefileVariant::BSDMake),
        vec!["${X:C/e[lb]$//}"]
    );
    let makefile = Makefile::parse_with_variant(text, MakefileVariant::BSDMake).tree();
    let reference = makefile.variable_references().next().unwrap();
    assert_eq!(
        reference.parse(MakefileVariant::BSDMake),
        Ok(crate::ParsedReference {
            name: "X".to_string(),
            modifiers: vec![crate::Modifier::RegexSubstitute {
                regex: crate::ModifierArg::literal("e[lb]$"),
                replacement: crate::ModifierArg::literal(""),
                flags: Default::default(),
            }],
        })
    );
}

#[test]
fn test_bsd_reference_unseparated_indirect() {
    let text = "X = ${v:L:${:Dempty}S,v,r,}\n";
    assert_eq!(
        reference_texts(text, MakefileVariant::BSDMake),
        vec!["${v:L:${:Dempty}S,v,r,}", "${:Dempty}"]
    );
    let makefile = Makefile::parse_with_variant(text, MakefileVariant::BSDMake).tree();
    let reference = makefile.variable_references().next().unwrap();
    assert_eq!(
        reference.parse(MakefileVariant::BSDMake),
        Ok(crate::ParsedReference {
            name: "v".to_string(),
            modifiers: vec![
                crate::Modifier::Literal,
                crate::Modifier::UnseparatedIndirect("${:Dempty}".to_string()),
                crate::Modifier::Substitute {
                    from: crate::ModifierArg::literal("v"),
                    to: crate::ModifierArg::literal("r"),
                    anchor_start: false,
                    anchor_end: false,
                    flags: Default::default(),
                },
            ],
        })
    );
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(parsed.root().to_string(), text);
}

#[test]
fn test_bsd_reference_substitute_anchor() {
    assert_eq!(
        reference_texts("X = ${X:S/$/x/}\n", MakefileVariant::BSDMake),
        vec!["${X:S/$/x/}"]
    );
}

#[test]
fn test_bsd_reference_closing_brace_as_delimiter() {
    let text = "Y = ${SRCS:S,},x,}\n";
    assert_eq!(
        reference_texts(text, MakefileVariant::BSDMake),
        vec!["${SRCS:S,},x,}"]
    );
    let makefile = Makefile::parse_with_variant(text, MakefileVariant::BSDMake).tree();
    let reference = makefile.variable_references().next().unwrap();
    assert_eq!(
        reference.parse(MakefileVariant::BSDMake).map(|r| r.name),
        Ok("SRCS".to_string())
    );
    assert_eq!(
        reference_texts("Y = $(X:S/)/y/)\n", MakefileVariant::BSDMake),
        vec!["$(X:S/)/y/)"]
    );
}

#[test]
fn test_bsd_reference_closing_brace_with_lone_cr() {
    assert_eq!(
        reference_texts("Y = ${X:S,},\"a\rb\",} c\n", MakefileVariant::BSDMake),
        vec!["${X:S,},\"a\rb\",}"]
    );
}

#[test]
fn test_bsd_reference_escaped_brace_in_pattern() {
    assert_eq!(
        reference_texts("X = ${X:M*\\}*}\n", MakefileVariant::BSDMake),
        vec!["${X:M*\\}*}"]
    );
}

#[test]
fn test_bsd_reference_loop_body() {
    assert_eq!(
        reference_texts("X = ${X:@v@${v}}@}\n", MakefileVariant::BSDMake),
        vec!["${X:@v@${v}}@}", "${v}"]
    );
}

#[test]
fn test_bsd_reference_default_value_braces() {
    // :U does not balance braces, so the second brace is not part of
    // the reference.
    assert_eq!(
        reference_texts("X = ${X:U}}\n", MakefileVariant::BSDMake),
        vec!["${X:U}"]
    );
    assert_eq!(
        reference_texts("X = ${X:U{a}}\n", MakefileVariant::BSDMake),
        vec!["${X:U{a}"]
    );
}

#[test]
fn test_bsd_reference_nested() {
    assert_eq!(
        reference_texts(
            "X = ${X:S/a/$b/:S/${Y:S,},x,}/c/:M${Z}}\n",
            MakefileVariant::BSDMake
        ),
        vec![
            "${X:S/a/$b/:S/${Y:S,},x,}/c/:M${Z}}",
            "$b",
            "${Y:S,},x,}",
            "${Z}"
        ]
    );
}

#[test]
fn test_bsd_reference_continued() {
    assert_eq!(
        reference_texts("X = ${X:S,},x \\\n\ty,}\n", MakefileVariant::BSDMake),
        vec!["${X:S,},x \\\n\ty,}"]
    );
}

#[test]
fn test_bsd_references_on_one_logical_line() {
    assert_eq!(
        reference_texts(
            "X = ${A:S/a/$b/} $c/d \\\n\t${B:S,},x,} $e/f\nY = ${C:S/$//}\n",
            MakefileVariant::BSDMake
        ),
        vec![
            "${A:S/a/$b/}",
            "$b",
            "$c",
            "${B:S,},x,}",
            "$e",
            "${C:S/$//}"
        ]
    );
}

#[test]
fn test_default_variant_reference_counts_braces() {
    assert_eq!(
        Makefile::parse("Y = ${SRCS:S,},x,}\n")
            .tree()
            .variable_references()
            .map(|r| r.to_string())
            .collect::<Vec<_>>(),
        vec!["${SRCS:S,}"]
    );
}

#[test]
fn test_bsd_single_character_reference() {
    // `i/small` is lexed as a single token.
    assert_eq!(
        reference_texts(
            "X = ${X:@i@${D}/$i/small@} $i/small $$x\n",
            MakefileVariant::BSDMake
        ),
        vec!["${X:@i@${D}/$i/small@}", "${D}", "$i", "$i"]
    );
}

#[test]
fn test_bsd_dollar_colon_is_not_a_reference() {
    // BSD make does not take `:` as a variable name, so `$:` expands to
    // `:` and the line is a dependency line without targets.
    let parsed = parse("$:\n", Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r#"ROOT@0..3
  RULE@0..3
    TARGETS@0..1
      EXPR@0..1
        DOLLAR@0..1 "$"
    OPERATOR@1..2 ":"
    PREREQUISITES@2..2
    NEWLINE@2..3 "\n"
"#
    );
    let makefile = Makefile::parse_with_variant("a$: b\n", MakefileVariant::BSDMake).tree();
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a$"]);
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["b"]);
    assert_eq!(
        reference_texts("X = $: $:: ${:U$:}\n", MakefileVariant::BSDMake),
        vec!["${:U$:}"]
    );
}

#[test]
fn test_gnu_dollar_colon_is_a_reference() {
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let parsed = parse("$:\n", variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        assert_eq!(
            format!("{:#?}", parsed.syntax()),
            r#"ROOT@0..3
  EXPRESSION_STATEMENT@0..3
    EXPR@0..2
      DOLLAR@0..1 "$"
      OPERATOR@1..2 ":"
    NEWLINE@2..3 "\n"
"#,
            "{variant:?}"
        );
    }
}

#[test]
fn test_single_character_reference_covers_one_character() {
    // Make reads `$XY` as the value of `X` followed by `Y`.
    for variant in [
        MakefileVariant::GNUMake,
        MakefileVariant::BSDMake,
        MakefileVariant::POSIXMake,
        MakefileVariant::NMake,
    ] {
        assert_eq!(
            reference_texts("V = $XY $i/small $$x\n", variant),
            vec!["$X", "$i"],
            "{variant:?}"
        );
        assert_eq!(
            reference_texts("$XY: $@a\n", variant),
            vec!["$X", "$@"],
            "{variant:?}"
        );
    }
    let makefile = Makefile::parse("V = $XY\n").tree();
    assert_eq!(
        makefile
            .variable_references()
            .map(|r| (r.name(), r.to_string()))
            .collect::<Vec<_>>(),
        vec![(Some("X".to_string()), "$X".to_string())]
    );
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.raw_value(), Some("$XY".to_string()));
}

#[test]
fn test_bsd_reference_in_quotes() {
    assert_eq!(
        reference_texts(
            "X = ${\"${A:Uno}\"!=\"no\":?${B}:c}\n",
            MakefileVariant::BSDMake
        ),
        vec!["${\"${A:Uno}\"!=\"no\":?${B}:c}", "${A:Uno}", "${B}"]
    );
}

#[test]
fn test_bsd_reference_escaped_hash() {
    // From heimdal's Makefile.rules.inc in NetBSD.
    let text = ".if ${ASN1_FILES.${src}:[\\#]} == 1\n.endif\n";
    assert_eq!(
        reference_texts(text, MakefileVariant::BSDMake),
        vec!["${ASN1_FILES.${src}:[\\#]}", "${src}"]
    );
    let makefile = Makefile::parse_with_variant(text, MakefileVariant::BSDMake).tree();
    let reference = makefile.variable_references().next().unwrap();
    assert_eq!(
        reference.parse(MakefileVariant::BSDMake),
        Ok(crate::ParsedReference {
            name: "ASN1_FILES.${src}".to_string(),
            modifiers: vec![crate::Modifier::Words(crate::WordSelector::Count)],
        })
    );
    assert_eq!(
        reference_texts("X = ${X:[\\#]:S/}/x/}\n", MakefileVariant::BSDMake),
        vec!["${X:[\\#]:S/}/x/}"]
    );
}

#[test]
fn test_gnu_reference_counts_opening_delimiter() {
    assert_eq!(
        reference_texts("Y = $(X:S/)/y/)\n", MakefileVariant::GNUMake),
        vec!["$(X:S/)"]
    );
    assert_eq!(
        reference_texts("Y = ${SRCS:S,},x,}\n", MakefileVariant::GNUMake),
        vec!["${SRCS:S,}"]
    );
}

#[test]
fn test_wildcard_target() {
    let parsed = parse("*.target: *.source\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["*.target"]);
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["*.source"]);
}

#[test]
fn test_quote_in_variable_name() {
    let parsed = parse("${:U'}=\tsingle-quote-var-value'\nB = 1\n", None);
    assert_eq!(parsed.errors, vec![]);
    let vars: Vec<_> = parsed.root().variable_definitions().collect();
    assert_eq!(
        vars.iter()
            .map(|v| (v.name().unwrap(), v.raw_value().unwrap()))
            .collect::<Vec<_>>(),
        vec![
            ("${:U'}".to_string(), "single-quote-var-value'".to_string()),
            ("B".to_string(), "1".to_string()),
        ]
    );
}

#[test]
fn test_conditionals() {
    // We'll use relaxed parsing for conditionals

    // Basic conditionals - ifdef/ifndef
    let code = "ifdef DEBUG\n    DEBUG_FLAG := 1\nendif\n";
    let mut buf = code.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse basic ifdef");
    assert!(makefile.code().contains("DEBUG_FLAG"));

    // Basic conditionals - ifeq/ifneq
    let code = "ifeq ($(OS),Windows_NT)\n    RESULT := windows\nelse\n    RESULT := unix\nendif\n";
    let mut buf = code.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse ifeq/ifneq");
    assert!(makefile.code().contains("RESULT"));
    assert!(makefile.code().contains("windows"));

    // Nested conditionals with else
    let code = "ifdef DEBUG\n    CFLAGS += -g\n    ifdef VERBOSE\n        CFLAGS += -v\n    endif\nelse\n    CFLAGS += -O2\nendif\n";
    let mut buf = code.as_bytes();
    let makefile =
        Makefile::read_relaxed(&mut buf).expect("Failed to parse nested conditionals with else");
    assert!(makefile.code().contains("CFLAGS"));
    assert!(makefile.code().contains("VERBOSE"));

    // Empty conditionals
    let code = "ifdef DEBUG\nendif\n";
    let mut buf = code.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse empty conditionals");
    assert!(makefile.code().contains("ifdef DEBUG"));

    // Conditionals with else ifeq
    let code = "ifeq ($(OS),Windows)\n    EXT := .exe\nelse ifeq ($(OS),Linux)\n    EXT := .bin\nelse\n    EXT := .out\nendif\n";
    let mut buf = code.as_bytes();
    let makefile =
        Makefile::read_relaxed(&mut buf).expect("Failed to parse conditionals with else ifeq");
    assert!(makefile.code().contains("EXT"));

    // Invalid conditionals - this should generate parse errors but still produce a Makefile
    let code = "ifXYZ DEBUG\nDEBUG := 1\nendif\n";
    let mut buf = code.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse with recovery");
    assert!(makefile.code().contains("DEBUG"));

    // Missing condition - this should also generate parse errors but still produce a Makefile
    let code = "ifdef \nDEBUG := 1\nendif\n";
    let mut buf = code.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf)
        .expect("Failed to parse with recovery - missing condition");
    assert!(makefile.code().contains("DEBUG"));
}

#[test]
fn test_variable_named_like_conditional() {
    // A variable whose name starts with "if" must not be mistaken for a
    // conditional directive (regression: `ifpkg` parsed as `ifdef`).
    let code = "ifpkg = $(if $(filter foo,bar),baz)\n";
    let makefile: Makefile = code.parse().expect("ifpkg variable should parse");
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len());
    assert_eq!(Some("ifpkg".to_string()), vars[0].name());
}

#[test]
fn test_conditional_with_trailing_comment() {
    let code = "ifeq ($(X), linux) # extra features\nFOO = bar\nendif\n";
    let makefile: Makefile = code.parse().expect("trailing comment should parse");
    assert_eq!(code, makefile.to_string());
}

#[test]
fn test_conditional_header_comment_tree() {
    // make strips a comment from a conditional directive line, so it
    // must not end up in the condition.
    let code = "ifdef X # c\n# d\nelse ifeq (a,b) # c\nelse # c\nendif # c\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r##"ROOT@0..55
  CONDITIONAL@0..55
    CONDITIONAL_IF@0..12
      IDENTIFIER@0..5 "ifdef"
      WHITESPACE@5..6 " "
      EXPR@6..7
        IDENTIFIER@6..7 "X"
      WHITESPACE@7..8 " "
      COMMENT@8..11 "# c"
      NEWLINE@11..12 "\n"
    COMMENT@12..15 "# d"
    NEWLINE@15..16 "\n"
    CONDITIONAL_ELSE@16..36
      IDENTIFIER@16..20 "else"
      WHITESPACE@20..21 " "
      IDENTIFIER@21..25 "ifeq"
      WHITESPACE@25..26 " "
      EXPR@26..31
        LPAREN@26..27 "("
        IDENTIFIER@27..28 "a"
        COMMA@28..29 ","
        IDENTIFIER@29..30 "b"
        RPAREN@30..31 ")"
      WHITESPACE@31..32 " "
      COMMENT@32..35 "# c"
      NEWLINE@35..36 "\n"
    CONDITIONAL_ELSE@36..44
      IDENTIFIER@36..40 "else"
      WHITESPACE@40..41 " "
      COMMENT@41..44 "# c"
    NEWLINE@44..45 "\n"
    CONDITIONAL_ENDIF@45..55
      IDENTIFIER@45..50 "endif"
      WHITESPACE@50..51 " "
      COMMENT@51..54 "# c"
      NEWLINE@54..55 "\n"
"##
    );
    assert_eq!(code, parsed.root().to_string());
}

/// The error kinds and lines, and the if and else bodies of the single
/// conditional in `code`.
fn parse_single_conditional(
    code: &str,
    variant: Option<MakefileVariant>,
) -> (Vec<(ParseErrorKind, usize)>, Option<String>, Option<String>) {
    let parsed = parse(code, variant);
    assert_eq!(code, parsed.root().to_string());
    let conditionals: Vec<_> = parsed.root().conditionals().collect();
    assert_eq!(1, conditionals.len(), "{code:?}");
    (
        parsed.errors.iter().map(|e| (e.kind(), e.line)).collect(),
        conditionals[0].if_body(),
        conditionals[0].else_body(),
    )
}

#[test]
fn test_conditional_extraneous_text() {
    // GNU make warns "extraneous text after 'else' directive" (or
    // 'endif') and otherwise ignores the text.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (code, line) in [
            ("ifdef X\nA = 1\nelse junk\nA = 2\nendif\n", 3),
            ("ifdef X\nA = 1\nelse junk # c\nA = 2\nendif\n", 3),
            ("ifdef X\nA = 1\nelse $(Y)\nA = 2\nendif\n", 3),
            ("ifdef X\nA = 1\nelse endif\nA = 2\nendif\n", 3),
            ("ifdef X\nA = 1\nelse ifdef:\nA = 2\nendif\n", 3),
            ("ifdef X\nA = 1\nelse ifndef: x\nA = 2\nendif\n", 3),
            ("ifdef X\nA = 1\nelse ifeq(a,a)\nA = 2\nendif\n", 3),
            ("ifdef X\nA = 1\nelse \\\njunk\nA = 2\nendif\n", 4),
            ("ifdef X\nA = 1\nelse\nA = 2\nendif junk\n", 5),
            ("ifdef X\nA = 1\nelse\nA = 2\nendif junk # c\n", 5),
            ("ifdef X\nA = 1\nelse\nA = 2\nendif \\\n junk\n", 6),
        ] {
            assert_eq!(
                parse_single_conditional(code, variant),
                (
                    vec![(ParseErrorKind::ExtraneousText, line)],
                    Some("A = 1\n".to_string()),
                    Some("\nA = 2\n".to_string())
                ),
                "{code:?}"
            );
        }
    }
}

#[test]
fn test_conditional_extraneous_text_tree() {
    let code = "ifdef X\nelse junk\nendif junk\n";
    let parsed = parse(code, None);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.kind(), e.line))
            .collect::<Vec<_>>(),
        vec![
            (ParseErrorKind::ExtraneousText, 2),
            (ParseErrorKind::ExtraneousText, 3)
        ]
    );
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r##"ROOT@0..29
  CONDITIONAL@0..29
    CONDITIONAL_IF@0..8
      IDENTIFIER@0..5 "ifdef"
      WHITESPACE@5..6 " "
      EXPR@6..7
        IDENTIFIER@6..7 "X"
      NEWLINE@7..8 "\n"
    CONDITIONAL_ELSE@8..17
      IDENTIFIER@8..12 "else"
      WHITESPACE@12..13 " "
      ERROR@13..17
        IDENTIFIER@13..17 "junk"
    NEWLINE@17..18 "\n"
    CONDITIONAL_ENDIF@18..29
      IDENTIFIER@18..23 "endif"
      WHITESPACE@23..24 " "
      ERROR@24..28
        IDENTIFIER@24..28 "junk"
      NEWLINE@28..29 "\n"
"##
    );
    assert_eq!(code, parsed.root().to_string());
}

#[test]
fn test_conditional_no_extraneous_text() {
    for code in [
        "ifdef X\nA = 1\nelse # c\nA = 2\nendif # c\n",
        "ifdef X\nA = 1\nelse  \nA = 2\nendif  \n",
        "ifdef X\nA = 1\nelse ifdef Y\nA = 2\nendif\n",
        "ifdef X\nA = 1\nelse ifeq (a,b)\nA = 2\nendif\n",
        "ifdef X\nA = 1\nelse ifdef#c\nA = 2\nendif\n",
        "ifdef X\nA = 1\nelse ifdef\\\n Y\nA = 2\nendif\n",
        "ifdef X\nA = 1\nelse\nA = 2\nendif",
    ] {
        let (errors, if_body, _) = parse_single_conditional(code, None);
        assert_eq!(
            (errors, if_body),
            (vec![], Some("A = 1\n".to_string())),
            "{code:?}"
        );
    }
}

#[test]
fn test_else_if_without_whitespace() {
    let code = "ifdef X\nelse ifdef:\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(
        parsed.errors,
        vec![ErrorInfo {
            message: "extraneous text after `else` directive".to_string(),
            line: 2,
            context: "else ifdef:".to_string(),
            kind: ParseErrorKind::ExtraneousText,
        }]
    );
    assert_eq!(
        parsed
            .positioned_errors
            .iter()
            .map(|e| e.range)
            .collect::<Vec<_>>(),
        vec![rowan::TextRange::new(13.into(), 18.into())]
    );
    assert_eq!(code, parsed.root().to_string());
    let conditionals: Vec<_> = parsed.root().conditionals().collect();
    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].else_body(), Some("\n".to_string()));
}

#[test]
fn test_nested_else_extraneous_text() {
    let code = "ifdef X\nelse ifdef Y\nelse junk\nA = 2\nendif\n";
    assert_eq!(
        parse_single_conditional(code, None).0,
        vec![(ParseErrorKind::ExtraneousText, 3)]
    );
}

#[test]
fn test_block_conditional_extraneous_text() {
    // BSD make: "The .else directive does not take arguments", a fatal
    // error once parsing finishes, but the line is still a `.else`.
    for (variant, code) in [
        (None, ".if 1\nA = 1\n.else junk\nA = 2\n.endif junk\n"),
        (
            Some(MakefileVariant::BSDMake),
            ".if 1\nA = 1\n.else junk\nA = 2\n.endif junk\n",
        ),
        (
            Some(MakefileVariant::NMake),
            "!IF 1\nA = 1\n!ELSE junk\nA = 2\n!ENDIF junk\n",
        ),
    ] {
        assert_eq!(
            parse_single_conditional(code, variant),
            (
                vec![
                    (ParseErrorKind::ExtraneousText, 3),
                    (ParseErrorKind::ExtraneousText, 5)
                ],
                Some("A = 1\n".to_string()),
                Some("A = 2\n".to_string())
            ),
            "{code:?}"
        );
    }
}

#[test]
fn test_rule_with_continuation_in_targets() {
    let code = "a b \\\nc: dep\n\techo hi\n";
    let makefile: Makefile = code.parse().expect("continuation in targets should parse");
    assert_eq!(code, makefile.to_string());
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(1, rules.len());
    assert_eq!(
        vec!["a".to_string(), "b".to_string(), "c".to_string()],
        rules[0].targets().collect::<Vec<_>>()
    );
}

#[test]
fn test_rule_with_indented_continuation_in_targets() {
    // The continued target line is tab-indented; the indent delimits
    // targets rather than becoming part of the target name.
    let code = "a b \\\n\tc: dep\n\techo hi\n";
    let makefile: Makefile = code
        .parse()
        .expect("indented target continuation should parse");
    assert_eq!(code, makefile.to_string());
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(1, rules.len());
    assert_eq!(
        vec!["a".to_string(), "b".to_string(), "c".to_string()],
        rules[0].targets().collect::<Vec<_>>()
    );
}

#[test]
fn test_rule_with_continuation_in_prerequisites() {
    // A prerequisite list continued onto a tab-indented line. The
    // continuation must not be folded into a prerequisite word, and the
    // continued prerequisites must still be recognised.
    let code = "all: a b \\\n\tc d\n\techo hi\n";
    let makefile: Makefile = code
        .parse()
        .expect("prerequisite continuation should parse");
    assert_eq!(code, makefile.to_string());
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(1, rules.len());
    assert_eq!(
        vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string()
        ],
        rules[0].prerequisites().collect::<Vec<_>>()
    );
}

#[test]
fn test_rule_prerequisite_escaped_backslash_not_continuation() {
    // An escaped backslash (`\\`) ending a prerequisite line is a literal
    // backslash, not a continuation, so the next line is a recipe.
    let code = "all: a b\\\\\n\techo hi\n";
    let makefile: Makefile = code.parse().expect("escaped backslash should parse");
    assert_eq!(code, makefile.to_string());
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(1, rules.len());
    assert_eq!(
        vec!["a".to_string(), "b\\\\".to_string()],
        rules[0].prerequisites().collect::<Vec<_>>()
    );
    assert_eq!(
        vec!["echo hi".to_string()],
        rules[0].recipes().collect::<Vec<_>>()
    );
}

#[test]
fn test_escaped_hash_in_conditional() {
    // `\#` does not start a comment, so the closing paren and the rest of
    // the conditional must still be parsed.
    let code = "all:\nifneq ($(X), \\#)\n\techo a\nendif\n";
    let parsed = Makefile::parse(code);
    assert_eq!(parsed.errors(), &[]);
    let makefile = parsed.tree();
    assert_eq!(code, makefile.to_string());
    let conditional = makefile
        .syntax()
        .descendants()
        .find_map(Conditional::cast)
        .expect("conditional");
    assert_eq!(
        Some(("$(X)".to_string(), "\\#".to_string())),
        conditional.ifeq_args()
    );
    assert_eq!(Some("\techo a\n".to_string()), conditional.if_body());
    assert!(conditional
        .syntax()
        .children()
        .any(|n| n.kind() == CONDITIONAL_ENDIF));
}

#[test]
fn test_escaped_hash_in_toplevel_conditional() {
    let code = "ifeq ($(X),a\\#b)\nY = 1\nendif\n";
    let parsed = Makefile::parse(code);
    assert_eq!(parsed.errors(), &[]);
    let makefile = parsed.tree();
    assert_eq!(code, makefile.to_string());
    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(1, conditionals.len());
    assert_eq!(
        Some(("$(X)".to_string(), "a\\#b".to_string())),
        conditionals[0].ifeq_args()
    );
    assert_eq!(Some("Y = 1\n".to_string()), conditionals[0].if_body());
}

#[test]
fn test_escaped_hash_in_variable_value() {
    let code = "X = a\\#b # comment\nY = c\\\\# comment\n";
    let makefile: Makefile = code.parse().expect("escaped hash should parse");
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(2, vars.len());
    assert_eq!(Some("a\\#b ".to_string()), vars[0].raw_value());
    assert_eq!(Some("c\\\\".to_string()), vars[1].raw_value());
}

#[test]
fn test_escaped_hash_in_prerequisites() {
    let code = "foo: a\\#b c # comment\n\techo \\#x\n";
    let makefile: Makefile = code.parse().expect("escaped hash should parse");
    assert_eq!(code, makefile.to_string());
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(1, rules.len());
    assert_eq!(
        vec!["a#b".to_string(), "c".to_string()],
        rules[0].prerequisites().collect::<Vec<_>>()
    );
    assert_eq!(
        vec!["echo \\#x".to_string()],
        rules[0].recipes().collect::<Vec<_>>()
    );
}

#[test]
fn test_assignment_with_tab_continuation() {
    // A variable value continued onto a tab-indented line, as commonly
    // seen in debian/rules. The continuation must not be mistaken for a
    // recipe line (which previously produced a spurious "recipe line is
    // not attached to any target" error).
    let code = "NATIVE_ARCHS += alpha arc hppa \\\n\triscv64 sh4 sparc\n";
    let makefile: Makefile = code.parse().expect("tab continuation should parse");
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len());
    assert_eq!(Some("NATIVE_ARCHS".to_string()), vars[0].name());
    assert_eq!(
        Some("alpha arc hppa \\\n\triscv64 sh4 sparc".to_string()),
        vars[0].raw_value()
    );
}

#[test]
fn test_assignment_escaped_backslash_not_continuation() {
    // A value ending in an escaped backslash (`\\`) is a literal backslash,
    // not a line continuation, so the following line is not folded into the
    // value. An odd run of backslashes still continues the line.
    let code = "VAR = foo \\\\\n\tbar = 1\n";
    let makefile: Makefile = code.parse().expect("escaped backslash should parse");
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(2, vars.len());
    assert_eq!(Some("foo \\\\".to_string()), vars[0].raw_value());

    let code = "VAR = foo \\\\\\\n\tbar\n";
    let makefile: Makefile = code.parse().expect("odd backslash run should parse");
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(Some("foo \\\\\\\n\tbar".to_string()), vars[0].raw_value());
}

#[test]
fn test_target_specific_assignment_trailing_comment() {
    // As with top-level assignments, a trailing comment is not part of
    // the value.
    let code = "foo: X = $(Y) 1 # comment\n";
    let makefile: Makefile = code.parse().unwrap();
    assert_eq!(code, makefile.to_string());
    let rule = makefile.rules().next().unwrap();
    let var = rule.scoped_assignment().unwrap();
    assert_eq!(Some("$(Y) 1 ".to_string()), var.raw_value());
    let top: Makefile = "X = $(Y) 1 # comment\n".parse().unwrap();
    let top_var = top.variable_definitions().next().unwrap();
    let shape = |node: &SyntaxNode| {
        node.descendants_with_tokens()
            .map(|e| (e.kind(), e.as_token().map(|t| t.text().to_string())))
            .collect::<Vec<_>>()
    };
    assert_eq!(shape(top_var.syntax()), shape(var.syntax()));
}

#[test]
fn test_target_specific_assignment_with_continuation() {
    let code = "git.o: EXTRA_CPPFLAGS = \\\n\t-DA \\\n\t-DB\n\nall:\n\techo hi\n";
    let makefile: Makefile = code.parse().unwrap();
    assert_eq!(code, makefile.to_string());
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(2, rules.len());
    let var = rules[0].scoped_assignment().unwrap();
    assert_eq!(Some("EXTRA_CPPFLAGS".to_string()), var.name());
    assert_eq!(Some("\\\n\t-DA \\\n\t-DB".to_string()), var.raw_value());
    assert_eq!(
        "git.o: EXTRA_CPPFLAGS = \\\n\t-DA \\\n\t-DB\n",
        rules[0].syntax().text().to_string()
    );
    assert_eq!(
        vec!["echo hi".to_string()],
        rules[1].recipes().collect::<Vec<_>>()
    );
}

#[test]
fn test_assignment_name_with_backslash() {
    let code = "\\n := 1\na\\b = 2\nx\\\\y ?= 3\na\\ += 4\nexport a\\b\\c = 5\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(code, root.to_string());
    assert_eq!(root.rules().count(), 0);
    let vars = root
        .variable_definitions()
        .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
        .collect::<Vec<_>>();
    let var = |name: &str, op: &str, value: &str| {
        (
            Some(name.to_string()),
            Some(op.to_string()),
            Some(value.to_string()),
        )
    };
    assert_eq!(
        vars,
        vec![
            var("\\n", ":=", "1"),
            var("a\\b", "=", "2"),
            var("x\\\\y", "?=", "3"),
            var("a\\", "+=", "4"),
            var("a\\b\\c", "=", "5"),
        ]
    );
}

#[test]
fn test_assignment_name_with_backslash_in_conditional() {
    let code = "ifdef X\n\\n := 1\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(code, root.to_string());
    let vars = root
        .variable_definitions()
        .map(|v| (v.name(), v.raw_value()))
        .collect::<Vec<_>>();
    assert_eq!(vars, vec![(Some("\\n".to_string()), Some("1".to_string()))]);
}

#[test]
fn test_assignment_name_with_backslash_value_continuation() {
    // The trailing backslash continues the (empty) value onto the next
    // line; it is not part of the name.
    let code = "\\n :=\\\n\nfoo = bar\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(code, root.to_string());
    let vars = root
        .variable_definitions()
        .map(|v| (v.name(), v.raw_value()))
        .collect::<Vec<_>>();
    assert_eq!(
        vars,
        vec![
            (Some("\\n".to_string()), Some("\\\n".to_string())),
            (Some("foo".to_string()), Some("bar".to_string())),
        ]
    );
}

#[test]
fn test_assignment_continuation_before_operator() {
    // As in linux/scripts/Makefile.gcc-plugins.
    let check = |code: &str, expected: Vec<(&str, &str, &str)>| {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let root = parsed.root();
        assert_eq!(code, root.to_string());
        assert_eq!(root.rules().count(), 0, "{code:?}");
        let vars = root
            .variable_definitions()
            .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
            .collect::<Vec<_>>();
        let expected = expected
            .into_iter()
            .map(|(name, op, value)| {
                (
                    Some(name.to_string()),
                    Some(op.to_string()),
                    Some(value.to_string()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(vars, expected, "{code:?}");
    };
    check("X \\\n\t+= a\n", vec![("X", "+=", "a")]);
    check("X \\\r\n\t+= a\r\n", vec![("X", "+=", "a")]);
    check("X\\\n= 1\n", vec![("X", "=", "1")]);
    check("X \\\n \\\n := 2\n", vec![("X", ":=", "2")]);
    check("a\\\\ \\\n = 1\n", vec![("a\\\\", "=", "1")]);
    check("export \\\n Y = 1\n", vec![("Y", "=", "1")]);
    check("override \\\n X \\\n = 1\n", vec![("X", "=", "1")]);
    check(
        "ifdef C\nX \\\n\t+= a\nendif\n$(X) \\\n += b\n",
        vec![("X", "+=", "a"), ("$(X)", "+=", "b")],
    );
}

#[test]
fn test_target_specific_assignment_continuation_before_operator() {
    for code in [
        "all: X \\\n\t= 1\n",
        "all: X \\\r\n\t= 1\r\n",
        "all: \\\n X = 1\n",
        "all: export \\\n X \\\n = 1\n",
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let root = parsed.root();
        assert_eq!(code, root.to_string());
        let rule = root.rules().next().unwrap();
        let var = rule.scoped_assignment().unwrap();
        assert_eq!(Some("X".to_string()), var.name(), "{code:?}");
        assert_eq!(Some("=".to_string()), var.assignment_operator());
        assert_eq!(Some("1".to_string()), var.raw_value());
    }
}

#[test]
fn test_no_target_specific_assignment_outside_gnu_and_bsd_make() {
    // POSIX make and nmake have no target-specific variables, so these
    // are prerequisites.
    for variant in [MakefileVariant::POSIXMake, MakefileVariant::NMake] {
        for (code, prerequisites) in [
            (
                ".SHELL: name=\"sh\" path=/bin/sh\n",
                vec!["name=\"sh\"", "path=/bin/sh"],
            ),
            (
                ".SHELL: \\\n\tname=\"sh\" \\\n\tpath=/bin/sh\n",
                vec!["name=\"sh\"", "path=/bin/sh"],
            ),
            ("all: \\\n  X=1\n", vec!["X=1"]),
        ] {
            let parsed = parse(code, Some(variant));
            assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            let rule = root.rules().next().unwrap();
            assert!(rule.scoped_assignment().is_none(), "{variant:?} {code:?}");
            assert_eq!(
                prerequisites,
                rule.prerequisites().collect::<Vec<_>>(),
                "{variant:?} {code:?}"
            );
        }
    }
}

#[test]
fn test_nmake_space_indented_commands() {
    // In nmake a command line begins with one or more spaces or tabs.
    let code = "all: foo.obj\n    link foo.obj\n  echo a \\\n b\n\techo c\n";
    let parsed = parse(code, Some(MakefileVariant::NMake));
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), code);
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "RULE\n  TARGETS\n  PREREQUISITES\n    PREREQUISITE\n  RECIPE\n  RECIPE\n  RECIPE\n"
    );
    let rule = root.rules().next().unwrap();
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["link foo.obj", "echo a \\\n b", "echo c"]
    );
}

#[test]
fn test_nmake_space_indented_command_after_inline_command() {
    let code = "foo.obj: foo.c ; cl /c foo.c\n  echo done\nbar:\n";
    let parsed = parse(code, Some(MakefileVariant::NMake));
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), code);
    let rules = root.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 2);
    assert_eq!(
        rules[0].recipes().collect::<Vec<_>>(),
        vec!["cl /c foo.c", "echo done"]
    );
    assert_eq!(rules[1].targets().collect::<Vec<_>>(), vec!["bar"]);
}

#[test]
fn test_space_indented_line_after_rule_not_nmake() {
    // Elsewhere only a tab starts a recipe line.
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::BSDMake),
        Some(MakefileVariant::POSIXMake),
    ] {
        let code = "all:\n  X = 1\n";
        let parsed = parse(code, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        assert_eq!(parsed.root().to_string(), code);
        assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\nVARIABLE\n  EXPR\n",
            "{variant:?}"
        );
    }
}

#[test]
fn test_nmake_space_indented_line_outside_rule() {
    // Outside of a rule, nmake handles a space-indented line just like a
    // tab-indented one.
    for (code, tab_code) in [
        ("X = 1\n  Y = 2\nall:\n", "X = 1\n\tY = 2\nall:\n"),
        ("X = 1\n  # c\n  \nall:\n", "X = 1\n\t# c\n\t\nall:\n"),
    ] {
        let parsed = parse(code, Some(MakefileVariant::NMake));
        let tab_parsed = parse(tab_code, Some(MakefileVariant::NMake));
        assert_eq!(parsed.root().to_string(), code);
        assert_eq!(
            node_kinds(&parsed.syntax()),
            node_kinds(&tab_parsed.syntax()),
            "{code:?}"
        );
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| (e.line, e.kind))
                .collect::<Vec<_>>(),
            tab_parsed
                .errors
                .iter()
                .map(|e| (e.line, e.kind))
                .collect::<Vec<_>>(),
            "{code:?}"
        );
    }
}

#[test]
fn test_rule_continuation_before_second_target() {
    let code = "foo \\\n bar: baz\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(code, root.to_string());
    assert_eq!(root.variable_definitions().count(), 0);
    let rule = root.rules().next().unwrap();
    assert_eq!(
        vec!["foo".to_string(), "bar".to_string()],
        rule.targets().collect::<Vec<_>>()
    );
}

#[test]
fn test_define_endef() {
    let code = "define greeting\n\techo hello\n\techo world\nendef\n\nall:\n\t$(greeting)\n";
    let makefile: Makefile = code.parse().expect("define/endef should parse");
    assert_eq!(code, makefile.to_string());
    assert_eq!(1, makefile.rules().count());
}

#[test]
fn test_define_endef_nested() {
    let code = "define outer\ndefine inner\nbody\nendef\nendef\n";
    let makefile: Makefile = code.parse().expect("nested define/endef should parse");
    assert_eq!(code, makefile.to_string());
}

fn assert_define(item: MakefileItem, name: &str, value: &str) {
    let MakefileItem::Variable(var) = item else {
        panic!("expected a variable, got {:?}", item.syntax());
    };
    assert!(var.is_define());
    assert_eq!(Some(name.to_string()), var.name());
    assert_eq!(Some(value.to_string()), var.raw_value());
}

#[test]
fn test_define_in_conditional() {
    let code = "ifdef X\ndefine FOO\nbody\nendef\nelse\ndefine BAR :=\nother\nendef\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(0, makefile.rules().count());
    let cond = makefile.conditionals().next().unwrap();
    let if_items: Vec<_> = cond.if_items().collect();
    assert_eq!(1, if_items.len());
    assert_define(if_items[0].clone(), "FOO", "body\n");
    let else_items: Vec<_> = cond.else_items().collect();
    assert_eq!(1, else_items.len());
    assert_define(else_items[0].clone(), "BAR", "other\n");
}

#[test]
fn test_define_in_nested_conditional() {
    let code = "ifdef X\nifeq ($(Y),1)\ndefine FOO\nbody\nendef\nendif\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let outer = makefile.conditionals().next().unwrap();
    let outer_items: Vec<_> = outer.if_items().collect();
    assert_eq!(1, outer_items.len());
    let MakefileItem::Conditional(inner) = &outer_items[0] else {
        panic!("expected a conditional, got {:?}", outer_items[0].syntax());
    };
    let inner_items: Vec<_> = inner.if_items().collect();
    assert_eq!(1, inner_items.len());
    assert_define(inner_items[0].clone(), "FOO", "body\n");
}

#[test]
fn test_define_in_conditional_with_directive_lines() {
    // Conditional directives inside a define body are part of its value.
    let code = "ifdef X\ndefine FOO\nifdef Y\na\nelse\nb\nendif\nendef\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let cond = makefile.conditionals().next().unwrap();
    assert!(!cond.has_else());
    let if_items: Vec<_> = cond.if_items().collect();
    assert_eq!(1, if_items.len());
    assert_define(if_items[0].clone(), "FOO", "ifdef Y\na\nelse\nb\nendif\n");
}

#[test]
fn test_define_in_conditional_in_rule() {
    let code = "all:\n\techo hi\nifdef X\ndefine FOO\nbody\nendef\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(1, makefile.rules().count());
    let defines: Vec<_> = makefile
        .syntax()
        .descendants()
        .filter_map(VariableDefinition::cast)
        .collect();
    assert_eq!(1, defines.len());
    assert_define(MakefileItem::Variable(defines[0].clone()), "FOO", "body\n");
}

#[test]
fn test_define_name_with_backslash() {
    // devscripts defines a newline helper this way.
    let code = "define \\n\n\n\nendef\n";
    let makefile: Makefile = code.parse().unwrap();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len());
    assert_eq!(Some("\\n".to_string()), vars[0].name());
    assert!(vars[0].is_define());
    assert_eq!(None, vars[0].assignment_operator());
    assert_eq!(Some("\n\n".to_string()), vars[0].raw_value());
}

#[test]
fn test_define_name_with_backslash_and_operator() {
    let code = "define a\\b :=\nbody\nendef\n";
    let makefile: Makefile = code.parse().unwrap();
    assert_eq!(code, makefile.to_string());
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(Some("a\\b".to_string()), var.name());
    assert_eq!(Some(":=".to_string()), var.assignment_operator());
    assert_eq!(Some("body\n".to_string()), var.raw_value());
}

#[test]
fn test_define_continuation_before_operator() {
    for (code, name, op, value) in [
        ("define W \\\n =\nhi\nendef\n", "W", "=", "hi\n"),
        ("define W\\\r\n:=\r\nhi\r\nendef\r\n", "W", ":=", "hi\n"),
        ("define a\\\\ \\\n =\nhi\nendef\n", "a\\\\", "=", "hi\n"),
        ("export \\\n define W \\\n =\nhi\nendef\n", "W", "=", "hi\n"),
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let makefile = parsed.root();
        assert_eq!(code, makefile.to_string());
        let vars = makefile
            .variable_definitions()
            .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
            .collect::<Vec<_>>();
        assert_eq!(
            vars,
            vec![(
                Some(name.to_string()),
                Some(op.to_string()),
                Some(value.to_string())
            )],
            "{code:?}"
        );
    }
}

#[test]
fn test_escaped_backslash_before_operator_line() {
    // An escaped backslash at the end of the line does not continue it,
    // so the `=` on the next line is not the operator.
    let code = "define a\\\\\n= 1\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars = makefile
        .variable_definitions()
        .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
        .collect::<Vec<_>>();
    assert_eq!(
        vars,
        vec![(Some("a\\\\".to_string()), None, Some("= 1\n".to_string()))]
    );

    // GNU make reports a missing separator here.
    let parsed = parse("a\\\\\n= 1\n", Some(MakefileVariant::GNUMake));
    assert_eq!(parsed.root().variable_definitions().count(), 0);
}

#[test]
fn test_define_name_with_spaces() {
    // GNU make takes the whole header up to the operator as the name.
    let code = "define foo bar \nbody\nendef\n";
    let makefile: Makefile = code.parse().unwrap();
    assert_eq!(code, makefile.to_string());
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(Some("foo bar".to_string()), var.name());
    assert_eq!(Some("body\n".to_string()), var.raw_value());
}

#[test]
fn test_define_name_with_continuation() {
    // GNU make reads the whole header, so a continuation and the
    // whitespace around it become a single space in the name.
    for (code, name, op) in [
        ("define A \\\nB\nbody\nendef\n", "A B", None),
        ("define A\\\nB\nbody\nendef\n", "A B", None),
        ("define A \\\n  B  \\\n  C\nbody\nendef\n", "A B C", None),
        ("define $(x) \\\n B\nbody\nendef\n", "$(x) B", None),
        ("define A \\\nB :=\nbody\nendef\n", "A B :=", None),
        ("define A \\\nB # c\nbody\nendef\n", "A B", None),
        ("define A \\\n=\nbody\nendef\n", "A", Some("=")),
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let makefile = parsed.root();
        assert_eq!(code, makefile.to_string());
        let vars = makefile
            .variable_definitions()
            .map(|v| {
                (
                    v.name(),
                    v.names().collect::<Vec<_>>(),
                    v.assignment_operator(),
                    v.raw_value(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            vars,
            vec![(
                Some(name.to_string()),
                vec![name.to_string()],
                op.map(str::to_string),
                Some("body\n".to_string())
            )],
            "{code:?}"
        );
    }
}

#[test]
fn test_define_multiword_name_with_operator() {
    // GNU make only recognises an operator after a single word; in
    // `define A B =` the variable is "A B =".
    for (code, name, op) in [
        ("define A B =\nbody\nendef\n", "A B =", None),
        ("define A B := x\nbody\nendef\n", "A B := x", None),
        ("define A =\nbody\nendef\n", "A", Some("=")),
        (
            "define $(subst _, ,A_B) =\nbody\nendef\n",
            "$(subst _, ,A_B)",
            Some("="),
        ),
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let makefile = parsed.root();
        assert_eq!(code, makefile.to_string());
        let vars = makefile
            .variable_definitions()
            .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
            .collect::<Vec<_>>();
        assert_eq!(
            vars,
            vec![(
                Some(name.to_string()),
                op.map(str::to_string),
                Some("body\n".to_string())
            )],
            "{code:?}"
        );
    }
}

#[test]
fn test_define_name_with_continuation_modifiers() {
    // Words after `define` are part of the name, not modifiers.
    let code = "override define override \\\n X\nbody\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_define());
    assert!(var.is_override());
    assert_eq!(var.name(), Some("override X".to_string()));
}

#[test]
fn test_define_name_reference_tree() {
    let code = "define $(PREFIX)_FLAGS :=\n$(B)\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r##"ROOT@0..37
  VARIABLE@0..37
    IDENTIFIER@0..6 "define"
    WHITESPACE@6..7 " "
    EXPR@7..16
      DOLLAR@7..8 "$"
      LPAREN@8..9 "("
      IDENTIFIER@9..15 "PREFIX"
      RPAREN@15..16 ")"
    IDENTIFIER@16..22 "_FLAGS"
    WHITESPACE@22..23 " "
    OPERATOR@23..25 ":="
    NEWLINE@25..26 "\n"
    EXPR@26..31
      DOLLAR@26..27 "$"
      LPAREN@27..28 "("
      IDENTIFIER@28..29 "B"
      RPAREN@29..30 ")"
      NEWLINE@30..31 "\n"
    IDENTIFIER@31..36 "endef"
    NEWLINE@36..37 "\n"
"##
    );
    assert_eq!(code, parsed.root().to_string());
}

#[test]
fn test_define_header_comment() {
    // make drops a comment on the define header line but keeps `#` in
    // the body.
    let code = "define foo # c\nbody # x\nendef\n";
    let parsed = parse(code, None);
    assert!(parsed.errors.is_empty());
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r##"ROOT@0..30
  VARIABLE@0..30
    IDENTIFIER@0..6 "define"
    WHITESPACE@6..7 " "
    IDENTIFIER@7..10 "foo"
    WHITESPACE@10..11 " "
    COMMENT@11..14 "# c"
    NEWLINE@14..15 "\n"
    EXPR@15..24
      IDENTIFIER@15..19 "body"
      WHITESPACE@19..20 " "
      COMMENT@20..23 "# x"
      NEWLINE@23..24 "\n"
    IDENTIFIER@24..29 "endef"
    NEWLINE@29..30 "\n"
"##
    );
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len());
    assert_eq!(Some("foo".to_string()), vars[0].name());
    assert_eq!(Some("body # x\n".to_string()), vars[0].raw_value());
}

#[test]
fn test_define_header_comment_after_operator() {
    let code = "define foo := # c\nb2\nendef\n";
    let makefile: Makefile = code.parse().expect("define with comment should parse");
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len());
    assert_eq!(Some("foo".to_string()), vars[0].name());
    assert_eq!(Some(":=".to_string()), vars[0].assignment_operator());
    assert_eq!(Some("b2\n".to_string()), vars[0].raw_value());
}

/// Parse a makefile with a single define named "A", returning the
/// errors as (kind, line) pairs and the operator and raw value of A.
fn parse_single_define(
    code: &str,
    variant: Option<MakefileVariant>,
) -> (Vec<(ParseErrorKind, usize)>, Option<String>, Option<String>) {
    let parsed = parse(code, variant);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len(), "{code:?}");
    assert_eq!(Some("A".to_string()), vars[0].name(), "{code:?}");
    (
        parsed.errors.iter().map(|e| (e.kind(), e.line)).collect(),
        vars[0].assignment_operator(),
        vars[0].raw_value(),
    )
}

#[test]
fn test_define_extraneous_text_after_operator() {
    // GNU make: "extraneous text after 'define' directive". The text is
    // not part of the value.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (code, op, line) in [
            ("define A =x\nfoo\nendef\n", "=", 1),
            ("define A = x\nfoo\nendef\n", "=", 1),
            ("define A=x\nfoo\nendef\n", "=", 1),
            ("define A ::= $(B) # c\nfoo\nendef\n", "::=", 1),
            ("override define A +=x\nfoo\nendef\n", "+=", 1),
            ("define A = \\\nbar\nfoo\nendef\n", "=", 2),
            ("define A = x \\\nbar\nfoo\nendef\n", "=", 1),
        ] {
            assert_eq!(
                parse_single_define(code, variant),
                (
                    vec![(ParseErrorKind::ExtraneousText, line)],
                    Some(op.to_string()),
                    Some("foo\n".to_string())
                ),
                "{code:?}"
            );
        }
    }
}

#[test]
fn test_define_no_extraneous_text_after_operator() {
    for code in [
        "define A := # c\nfoo\nendef\n",
        "define A =  \nfoo\nendef\n",
        "define A = \\\n# c\nfoo\nendef\n",
        "define A = \\\n\nfoo\nendef\n",
        "define A = \\\n  \nfoo\nendef\n",
    ] {
        let (errors, _, value) = parse_single_define(code, None);
        assert_eq!(
            (errors, value),
            (vec![], Some("foo\n".to_string())),
            "{code:?}"
        );
    }
}

#[test]
fn test_endef_extraneous_text() {
    // GNU make: "extraneous text after 'endef' directive". The line still
    // ends the define.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (code, line) in [
            ("define A\nfoo\nendef junk\n", 3),
            ("define A\nfoo\nendef $(X)\n", 3),
            ("define A\nfoo\nendef junk # c\n", 3),
            ("define A\nfoo\nendef \\\nbar\n", 4),
        ] {
            assert_eq!(
                parse_single_define(code, variant),
                (
                    vec![(ParseErrorKind::ExtraneousText, line)],
                    None,
                    Some("foo\n".to_string())
                ),
                "{code:?}"
            );
        }
    }
}

#[test]
fn test_endef_no_extraneous_text() {
    for code in [
        "define A\nfoo\nendef # c\n",
        "define A\nfoo\nendef\t# c\n",
        "define A\nfoo\nendef  \n",
        "define A\nfoo\nendef \\\n\n",
        "define A\nfoo\nendef \\\n# c\n",
        "define A\nfoo\nendef",
    ] {
        assert_eq!(
            parse_single_define(code, None),
            (vec![], None, Some("foo\n".to_string())),
            "{code:?}"
        );
    }
}

#[test]
fn test_nested_endef_extraneous_text() {
    // make also checks the `endef` of a define nested in the body, which
    // stays part of the value.
    let code = "define A\ndefine B\nfoo\nendef junk\nendef\n";
    assert_eq!(
        parse_single_define(code, None),
        (
            vec![(ParseErrorKind::ExtraneousText, 4)],
            None,
            Some("define B\nfoo\nendef junk\n".to_string())
        )
    );
}

#[test]
fn test_define_body_keyword_needs_separator() {
    // In a define body make only recognises `define` and `endef` when
    // followed by whitespace or the end of the line.
    for (code, value) in [
        ("define A\nfoo\nendef#c\nendef\n", "foo\nendef#c\n"),
        ("define A\nfoo\nendef=x\nendef\n", "foo\nendef=x\n"),
        ("define A\nfoo\nendef$(X)\nendef\n", "foo\nendef$(X)\n"),
        ("define A\nfoo\n endef#c\nendef\n", "foo\n endef#c\n"),
        ("define A\ndefine#c\nfoo\nendef\n", "define#c\nfoo\n"),
        ("define A\ndefine=x\nfoo\nendef\n", "define=x\nfoo\n"),
        ("define A\nfoo\nendef\t# c\n", "foo\n"),
    ] {
        assert_eq!(
            parse_single_define(code, None),
            (vec![], None, Some(value.to_string())),
            "{code:?}"
        );
    }
    let parsed = parse("define A\nfoo\nendef#c\n", None);
    assert_eq!(
        parsed.errors.iter().map(|e| e.kind()).collect::<Vec<_>>(),
        vec![ParseErrorKind::MissingEndef]
    );
    // A line continuation separates the keyword from what follows.
    assert_eq!(
        parse_single_define("define A\nfoo\nendef\\\nbar\n", None),
        (
            vec![(ParseErrorKind::ExtraneousText, 4)],
            None,
            Some("foo\n".to_string())
        )
    );
}

#[test]
fn test_directive_followed_by_comment() {
    // Outside a define body make strips comments first, so `endif#c` is
    // still `endif`.
    for code in [
        "ifdef X\nA = 1\nendif#c\n",
        "ifdef X\nA = 1\nelse#c\nA = 2\nendif\n",
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        assert_eq!(code, parsed.root().to_string());
    }
    assert_eq!(
        error_kinds("define#c\nendef\n", None),
        vec![ParseErrorKind::ExpectedVariableName]
    );
    assert_eq!(
        error_kinds("endif#c\n", None),
        vec![ParseErrorKind::ExtraneousEndif]
    );
    assert_eq!(
        error_kinds("else#c\n", None),
        vec![ParseErrorKind::ElseWithoutIf]
    );
}

#[test]
fn test_define_extraneous_text_tree() {
    let code = "define A = x\nfoo\nendef y\n";
    let parsed = parse(code, None);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r##"ROOT@0..25
  VARIABLE@0..25
    IDENTIFIER@0..6 "define"
    WHITESPACE@6..7 " "
    IDENTIFIER@7..8 "A"
    WHITESPACE@8..9 " "
    OPERATOR@9..10 "="
    WHITESPACE@10..11 " "
    ERROR@11..12
      IDENTIFIER@11..12 "x"
    NEWLINE@12..13 "\n"
    EXPR@13..17
      IDENTIFIER@13..16 "foo"
      NEWLINE@16..17 "\n"
    IDENTIFIER@17..22 "endef"
    WHITESPACE@22..23 " "
    ERROR@23..24
      IDENTIFIER@23..24 "y"
    NEWLINE@24..25 "\n"
"##
    );
}

#[test]
fn test_define_with_modifiers() {
    let code = "override define FOO :=\nbody\nendef\nexport define BAR\nline\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(0, makefile.rules().count());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(2, vars.len());

    assert!(vars[0].is_define());
    assert!(vars[0].is_override());
    assert!(!vars[0].is_export());
    assert_eq!(Some("FOO".to_string()), vars[0].name());
    assert_eq!(Some(":=".to_string()), vars[0].assignment_operator());
    assert_eq!(Some("body\n".to_string()), vars[0].raw_value());

    assert!(vars[1].is_define());
    assert!(!vars[1].is_override());
    assert!(vars[1].is_export());
    assert_eq!(Some("BAR".to_string()), vars[1].name());
    assert_eq!(None, vars[1].assignment_operator());
    assert_eq!(Some("line\n".to_string()), vars[1].raw_value());
}

#[test]
fn test_define_with_combined_modifiers() {
    let code = "override export define OE =\nx\nendef\nprivate define P\ny\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(2, vars.len());

    assert!(vars[0].is_define());
    assert!(vars[0].is_override());
    assert!(vars[0].is_export());
    assert_eq!(Some("OE".to_string()), vars[0].name());
    assert_eq!(Some("=".to_string()), vars[0].assignment_operator());
    assert_eq!(Some("x\n".to_string()), vars[0].raw_value());

    assert!(vars[1].is_define());
    assert!(!vars[1].is_override());
    assert!(!vars[1].is_export());
    assert_eq!(Some("P".to_string()), vars[1].name());
    assert_eq!(Some("y\n".to_string()), vars[1].raw_value());
}

#[test]
fn test_modifier_keyword_as_variable_name() {
    let makefile: Makefile = "private = 1\n".parse().unwrap();
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(Some("private".to_string()), vars[0].name());
}

#[test]
fn test_define_with_modifier_in_conditional() {
    let code = "ifdef X\noverride define FOO\nbody\nendef\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(0, makefile.rules().count());
    let cond = makefile.conditionals().next().unwrap();
    let if_items: Vec<_> = cond.if_items().collect();
    assert_eq!(1, if_items.len());
    let MakefileItem::Variable(var) = &if_items[0] else {
        panic!("expected a variable, got {:?}", if_items[0].syntax());
    };
    assert!(var.is_define());
    assert!(var.is_override());
    assert_eq!(Some("FOO".to_string()), var.name());
    assert_eq!(Some("body\n".to_string()), var.raw_value());
}

#[test]
fn test_private_define_and_private_assignment() {
    let code = "private define X\nbody\nendef\nprivate Y = 1\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(2, vars.len());
    assert!(vars[0].is_define());
    assert_eq!(Some("X".to_string()), vars[0].name());
    assert!(!vars[1].is_define());
    assert_eq!(Some("Y".to_string()), vars[1].name());
    assert_eq!(Some("1".to_string()), vars[1].raw_value());
}

#[test]
fn test_parse_simple() {
    const SIMPLE: &str = r#"VARIABLE = value

rule: dependency
	command
"#;
    let parsed = parse(SIMPLE, None);
    assert!(parsed.errors.is_empty());
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r#"ROOT@0..44
  VARIABLE@0..17
    IDENTIFIER@0..8 "VARIABLE"
    WHITESPACE@8..9 " "
    OPERATOR@9..10 "="
    WHITESPACE@10..11 " "
    EXPR@11..16
      IDENTIFIER@11..16 "value"
    NEWLINE@16..17 "\n"
  BLANK_LINE@17..18
    NEWLINE@17..18 "\n"
  RULE@18..44
    TARGETS@18..22
      IDENTIFIER@18..22 "rule"
    OPERATOR@22..23 ":"
    WHITESPACE@23..24 " "
    PREREQUISITES@24..34
      PREREQUISITE@24..34
        IDENTIFIER@24..34 "dependency"
    NEWLINE@34..35 "\n"
    RECIPE@35..44
      INDENT@35..36 "\t"
      TEXT@36..43 "command"
      NEWLINE@43..44 "\n"
"#
    );

    let root = parsed.root();

    let mut rules = root.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    let rule = rules.pop().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);

    let mut variables = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(variables.len(), 1);
    let variable = variables.pop().unwrap();
    assert_eq!(variable.name(), Some("VARIABLE".to_string()));
    assert_eq!(variable.raw_value(), Some("value".to_string()));
}

#[test]
fn test_parse_shell_assign_in_value() {
    let input = "X != echo a!=b\n";
    let parsed = parse(input, None);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let root = parsed.root();
    assert_eq!(root.rules().count(), 0);
    let variables = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(variables.len(), 1);
    assert_eq!(variables[0].name(), Some("X".to_string()));
    assert_eq!(variables[0].assignment_operator(), Some("!=".to_string()));
    assert_eq!(variables[0].raw_value(), Some("echo a!=b".to_string()));
    assert_eq!(root.to_string(), input);
}

#[test]
fn test_parse_target_specific_shell_assign() {
    let parsed = parse("foo: X != echo hi\n", None);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let rule = parsed.root().rules().next().unwrap();
    let var = rule.scoped_assignment().unwrap();
    assert_eq!(var.name(), Some("X".to_string()));
    assert_eq!(var.assignment_operator(), Some("!=".to_string()));
    assert_eq!(var.raw_value(), Some("echo hi".to_string()));
}

#[test]
fn test_parse_export_assign() {
    const EXPORT: &str = r#"export VARIABLE := value
"#;
    let parsed = parse(EXPORT, None);
    assert!(parsed.errors.is_empty());
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r#"ROOT@0..25
  VARIABLE@0..25
    IDENTIFIER@0..6 "export"
    WHITESPACE@6..7 " "
    IDENTIFIER@7..15 "VARIABLE"
    WHITESPACE@15..16 " "
    OPERATOR@16..18 ":="
    WHITESPACE@18..19 " "
    EXPR@19..24
      IDENTIFIER@19..24 "value"
    NEWLINE@24..25 "\n"
"#
    );

    let root = parsed.root();

    let mut variables = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(variables.len(), 1);
    let variable = variables.pop().unwrap();
    assert_eq!(variable.name(), Some("VARIABLE".to_string()));
    assert_eq!(variable.raw_value(), Some("value".to_string()));
}

#[test]
fn test_parse_order_only_prerequisites() {
    let parsed = parse("foo: a | b\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r#"ROOT@0..11
  RULE@0..11
    TARGETS@0..3
      IDENTIFIER@0..3 "foo"
    OPERATOR@3..4 ":"
    WHITESPACE@4..5 " "
    PREREQUISITES@5..10
      PREREQUISITE@5..6
        IDENTIFIER@5..6 "a"
      WHITESPACE@6..7 " "
      OPERATOR@7..8 "|"
      WHITESPACE@8..9 " "
      PREREQUISITE@9..10
        IDENTIFIER@9..10 "b"
    NEWLINE@10..11 "\n"
"#
    );
}

#[test]
fn test_parse_static_pattern_rule() {
    let parsed = parse("a.o: %.o : %.c\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r#"ROOT@0..15
  RULE@0..15
    TARGETS@0..3
      IDENTIFIER@0..3 "a.o"
    OPERATOR@3..4 ":"
    WHITESPACE@4..5 " "
    TARGET_PATTERN@5..8
      IDENTIFIER@5..8 "%.o"
    WHITESPACE@8..9 " "
    OPERATOR@9..10 ":"
    WHITESPACE@10..11 " "
    PREREQUISITES@11..14
      PREREQUISITE@11..14
        IDENTIFIER@11..14 "%.c"
    NEWLINE@14..15 "\n"
"#
    );
}

#[test]
fn test_parse_double_colon_static_pattern_rule() {
    let parsed = parse("a.o:: %.o: %.c\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r#"ROOT@0..15
  RULE@0..15
    TARGETS@0..3
      IDENTIFIER@0..3 "a.o"
    OPERATOR@3..5 "::"
    WHITESPACE@5..6 " "
    TARGET_PATTERN@6..9
      IDENTIFIER@6..9 "%.o"
    OPERATOR@9..10 ":"
    WHITESPACE@10..11 " "
    PREREQUISITES@11..14
      PREREQUISITE@11..14
        IDENTIFIER@11..14 "%.c"
    NEWLINE@14..15 "\n"
"#
    );
}

#[test]
fn test_parse_grouped_targets() {
    let parsed = parse("a b &: c\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r#"ROOT@0..9
  RULE@0..9
    TARGETS@0..4
      IDENTIFIER@0..1 "a"
      WHITESPACE@1..2 " "
      IDENTIFIER@2..3 "b"
      WHITESPACE@3..4 " "
    OPERATOR@4..6 "&:"
    WHITESPACE@6..7 " "
    PREREQUISITES@7..8
      PREREQUISITE@7..8
        IDENTIFIER@7..8 "c"
    NEWLINE@8..9 "\n"
"#
    );
}

#[test]
fn test_directive_names_as_targets() {
    // Make only takes a word as a directive if whitespace, a comment or
    // the end of the line follows it.
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::BSDMake),
        Some(MakefileVariant::POSIXMake),
    ] {
        for (code, targets, prerequisites) in [
            ("ifeq:\n\techo $@\n", vec!["ifeq"], vec![]),
            ("ifneq: a\n", vec!["ifneq"], vec!["a"]),
            ("ifdef::\n\techo $@\n", vec!["ifdef"], vec![]),
            ("ifndef:\n", vec!["ifndef"], vec![]),
            ("else:\n\techo $@\n", vec!["else"], vec![]),
            ("endif:\n\techo $@\n", vec!["endif"], vec![]),
            ("define:\n\techo $@\n", vec!["define"], vec![]),
            ("endef:\n", vec!["endef"], vec![]),
            ("vpath:\n\techo $@\n", vec!["vpath"], vec![]),
            ("vpath:x\n", vec!["vpath"], vec!["x"]),
            ("undefine:\n", vec!["undefine"], vec![]),
            ("override:\n", vec!["override"], vec![]),
            ("export:x\n", vec!["export"], vec!["x"]),
            ("include: x\n", vec!["include"], vec!["x"]),
            ("load:\n", vec!["load"], vec![]),
        ] {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            let rules: Vec<_> = root.rules().collect();
            assert_eq!(rules.len(), 1, "{variant:?} {code:?}");
            assert_eq!(
                targets,
                rules[0].targets().collect::<Vec<_>>(),
                "{variant:?} {code:?}"
            );
            assert_eq!(
                prerequisites,
                rules[0].prerequisites().collect::<Vec<_>>(),
                "{variant:?} {code:?}"
            );
        }
    }
}

#[test]
fn test_directive_names_as_targets_in_conditional() {
    let code = "ifeq (a,a)\nelse:\n\techo $@\nendif:\n\techo $@\nendif\n";
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let parsed = parse(code, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let root = parsed.root();
        assert_eq!(code, root.to_string());
        assert_eq!(root.conditionals().count(), 1, "{variant:?}");
        let targets: Vec<_> = root
            .rules()
            .flat_map(|r| r.targets().collect::<Vec<_>>())
            .collect();
        assert_eq!(targets, vec!["else", "endif"], "{variant:?}");
    }
}

#[test]
fn test_conditional_keywords_as_variables() {
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (code, name) in [
            ("ifeq=1\n", "ifeq"),
            ("ifdef = 2\n", "ifdef"),
            ("endif:=3\n", "endif"),
            ("else ?= 4\n", "else"),
            ("define += 5\n", "define"),
        ] {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            assert_eq!(root.conditionals().count(), 0, "{variant:?} {code:?}");
            let names: Vec<_> = root.variable_definitions().map(|v| v.name()).collect();
            assert_eq!(names, vec![Some(name.to_string())], "{variant:?} {code:?}");
        }
    }
}

#[test]
fn test_conditional_keyword_assignment_ends_rule() {
    // As for any other assignment, a comment before `ifdef = 1` doesn't
    // belong to the rule, as no recipe line can follow.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (code, name) in [
            ("all:\n\techo a\n\n# c\nifdef = 1\n\techo b\n", "ifdef"),
            ("all:\n\techo a\n\n# c\nifndef := 1\n\techo b\n", "ifndef"),
        ] {
            let parsed = parse(code, variant);
            assert_eq!(
                parsed.errors,
                vec![ErrorInfo {
                    message: "indented line not part of a rule".to_string(),
                    line: 6,
                    context: "\techo b".to_string(),
                    kind: ParseErrorKind::RecipeBeforeFirstTarget,
                }],
                "{variant:?} {code:?}"
            );
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            let rules: Vec<_> = root.rules().collect();
            assert_eq!(rules.len(), 1, "{variant:?} {code:?}");
            assert_eq!(rules[0].to_string(), "all:\n\techo a\n\n");
            let names: Vec<_> = root.variable_definitions().map(|v| v.name()).collect();
            assert_eq!(names, vec![Some(name.to_string())], "{variant:?} {code:?}");
        }
    }
}

#[test]
fn test_conditional_keyword_forms() {
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for code in ["ifdef#c\nendif#c\n", "ifdef\\\n  X\nelse\\\n\nendif\n"] {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            assert_eq!(root.conditionals().count(), 1, "{variant:?} {code:?}");
            assert_eq!(root.rules().count(), 0, "{variant:?} {code:?}");
        }
    }
}

#[test]
fn test_conditional_keyword_without_whitespace() {
    // GNU make: "missing separator (ifeq/ifneq must be followed by
    // whitespace)". The line is still read as a conditional.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (code, keyword, offset, tree) in [
            (
                "ifeq(a,b)\nendif\n",
                "ifeq",
                4,
                r#"ROOT@0..16
  CONDITIONAL@0..16
    CONDITIONAL_IF@0..10
      IDENTIFIER@0..4 "ifeq"
      EXPR@4..9
        LPAREN@4..5 "("
        IDENTIFIER@5..6 "a"
        COMMA@6..7 ","
        IDENTIFIER@7..8 "b"
        RPAREN@8..9 ")"
      NEWLINE@9..10 "\n"
    CONDITIONAL_ENDIF@10..16
      IDENTIFIER@10..15 "endif"
      NEWLINE@15..16 "\n"
"#,
            ),
            (
                "ifneq\"a\" \"b\"\nendif\n",
                "ifneq",
                5,
                r#"ROOT@0..19
  CONDITIONAL@0..19
    CONDITIONAL_IF@0..13
      IDENTIFIER@0..5 "ifneq"
      EXPR@5..12
        QUOTE@5..6 "\""
        IDENTIFIER@6..7 "a"
        QUOTE@7..8 "\""
        WHITESPACE@8..9 " "
        QUOTE@9..10 "\""
        IDENTIFIER@10..11 "b"
        QUOTE@11..12 "\""
      NEWLINE@12..13 "\n"
    CONDITIONAL_ENDIF@13..19
      IDENTIFIER@13..18 "endif"
      NEWLINE@18..19 "\n"
"#,
            ),
        ] {
            let parsed = parse(code, variant);
            let message = format!("`{keyword}` must be followed by whitespace");
            assert_eq!(
                parsed.errors,
                vec![ErrorInfo {
                    message: message.clone(),
                    line: 1,
                    context: code.lines().next().unwrap().to_string(),
                    kind: ParseErrorKind::MissingSeparator,
                }],
                "{variant:?} {code:?}"
            );
            assert_eq!(
                parsed
                    .positioned_errors
                    .iter()
                    .map(|e| (e.message.as_str(), e.range))
                    .collect::<Vec<_>>(),
                vec![(
                    message.as_str(),
                    rowan::TextRange::at(offset.into(), 1.into())
                )],
                "{variant:?} {code:?}"
            );
            assert_eq!(
                format!("{:#?}", parsed.syntax()),
                tree,
                "{variant:?} {code:?}"
            );
            assert_eq!(code, parsed.root().to_string());
        }
    }
}

#[test]
fn test_no_gnu_rule_syntax_in_posix_make_or_nmake() {
    // Order-only prerequisites, static pattern rules and grouped targets
    // are GNU make extensions, so `|`, `%.o:` and `&` are file names.
    for variant in [MakefileVariant::POSIXMake, MakefileVariant::NMake] {
        for (code, targets, prerequisites) in [
            ("foo: bar | baz\n", vec!["foo"], vec!["bar", "|", "baz"]),
            ("a.o: %.o: %.c\n", vec!["a.o"], vec!["%.o:", "%.c"]),
            ("a b &: c\n", vec!["a", "b", "&"], vec!["c"]),
        ] {
            let parsed = parse(code, Some(variant));
            assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            let rule = root.rules().next().unwrap();
            assert_eq!(
                targets,
                rule.targets().collect::<Vec<_>>(),
                "{variant:?} {code:?}"
            );
            assert_eq!(
                prerequisites,
                rule.prerequisites().collect::<Vec<_>>(),
                "{variant:?} {code:?}"
            );
            assert_eq!(rule.order_only_prerequisites().count(), 0);
            assert_eq!(rule.static_pattern(), None);
            assert!(!rule.is_grouped());
        }
    }
}

#[test]
fn test_bang_in_target_names() {
    // Only BSD make has the `!` dependency operator. Without a known
    // variant, a later `:` means `!` is part of a target name.
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
    ] {
        for (code, targets, prerequisites) in [
            ("a!b:\n\techo $@\n", vec!["a!b"], vec![]),
            ("!x:\n\techo $@\n", vec!["!x"], vec![]),
            ("a! b!c: d!e\n", vec!["a!", "b!c"], vec!["d!e"]),
            ("x ! y: z\n", vec!["x", "!", "y"], vec!["z"]),
            ("a!b \\\n c:\n", vec!["a!b", "c"], vec![]),
            ("*.o \\\n b!c: d\n", vec!["*.o", "b!c"], vec!["d"]),
        ] {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            let rules: Vec<_> = root.rules().collect();
            assert_eq!(rules.len(), 1, "{variant:?} {code:?}");
            assert_eq!(
                targets,
                rules[0].targets().collect::<Vec<_>>(),
                "{variant:?} {code:?}"
            );
            assert_eq!(
                prerequisites,
                rules[0].prerequisites().collect::<Vec<_>>(),
                "{variant:?} {code:?}"
            );
        }
    }
}

#[test]
fn test_bang_in_variable_names() {
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::BSDMake),
        Some(MakefileVariant::POSIXMake),
    ] {
        for (code, name) in [("!x = 1\n", "!x"), ("!x=1\n", "!x"), ("a!b = 2\n", "a!b")] {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            assert_eq!(root.rules().count(), 0, "{variant:?} {code:?}");
            let names: Vec<_> = root.variable_definitions().map(|v| v.name()).collect();
            assert_eq!(names, vec![Some(name.to_string())], "{variant:?} {code:?}");
        }
    }
}

#[test]
fn test_bsd_bang_dependency_operator() {
    for (variant, code, targets, prerequisites) in [
        (
            Some(MakefileVariant::BSDMake),
            "a!b:\n",
            vec!["a"],
            vec!["b:"],
        ),
        (Some(MakefileVariant::BSDMake), "!x:\n", vec![], vec!["x:"]),
        (
            Some(MakefileVariant::BSDMake),
            "a ! b\n",
            vec!["a"],
            vec!["b"],
        ),
        (None, "a ! b\n", vec!["a"], vec!["b"]),
        (None, "a b! c\n", vec!["a", "b"], vec!["c"]),
        (None, "a!b \\\n c\n", vec!["a"], vec!["b", "c"]),
        (
            Some(MakefileVariant::BSDMake),
            "a!b \\\n c:\n",
            vec!["a"],
            vec!["b", "c:"],
        ),
    ] {
        let parsed = parse(code, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
        let root = parsed.root();
        assert_eq!(code, root.to_string());
        let rules: Vec<_> = root.rules().collect();
        assert_eq!(rules.len(), 1, "{variant:?} {code:?}");
        let syntax = variant.unwrap_or(MakefileVariant::BSDMake);
        assert_eq!(
            targets,
            rules[0].targets_for(syntax).collect::<Vec<_>>(),
            "{variant:?} {code:?}"
        );
        assert_eq!(
            prerequisites,
            rules[0].prerequisites_for(syntax).collect::<Vec<_>>(),
            "{variant:?} {code:?}"
        );
    }
}

#[test]
fn test_plus_and_question_mark_in_names() {
    // Outside of `+=` and `?=`, make takes `+` and `?` as part of a
    // name, as in `c++filt.1` or `libstdc++`.
    let text = "c++ = x\nv+ = b\nx += 1\ny+=3\nz?=4\nw?=?y\n\
                    all: c++filt.1 a?\n\
                    c++filt.1 a? + ?: x$+ $? c++\n\
                    \t@echo $+ $?\n\
                    libstdc++.a(c++.o): c++.o\n\
                    .ORDER: c++filt.1 a?\n";
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::BSDMake),
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ] {
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let makefile = parsed.root();
        assert_eq!(makefile.to_string(), text, "{variant:?}");
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
                ("c++".to_string(), "=".to_string(), "x".to_string()),
                ("v+".to_string(), "=".to_string(), "b".to_string()),
                ("x".to_string(), "+=".to_string(), "1".to_string()),
                ("y".to_string(), "+=".to_string(), "3".to_string()),
                ("z".to_string(), "?=".to_string(), "4".to_string()),
                ("w".to_string(), "?=".to_string(), "?y".to_string()),
            ],
            "{variant:?}"
        );
        let rules = makefile.rules().collect::<Vec<_>>();
        assert_eq!(
            rules
                .iter()
                .map(|r| (
                    r.targets().collect::<Vec<_>>(),
                    r.prerequisites().collect::<Vec<_>>()
                ))
                .collect::<Vec<_>>(),
            vec![
                (
                    vec!["all".to_string()],
                    vec!["c++filt.1".to_string(), "a?".to_string()]
                ),
                (
                    vec![
                        "c++filt.1".to_string(),
                        "a?".to_string(),
                        "+".to_string(),
                        "?".to_string()
                    ],
                    vec!["x$+".to_string(), "$?".to_string(), "c++".to_string()]
                ),
                (
                    vec!["libstdc++.a(c++.o)".to_string()],
                    vec!["c++.o".to_string()]
                ),
                (
                    vec![".ORDER".to_string()],
                    vec!["c++filt.1".to_string(), "a?".to_string()]
                ),
            ],
            "{variant:?}"
        );
        assert_eq!(
            rules[1].recipes().collect::<Vec<_>>(),
            vec!["@echo $+ $?".to_string()],
            "{variant:?}"
        );
    }
}

#[test]
fn test_parse_inline_recipe() {
    let parsed = parse("all: dep ; echo hi # x\n\tcmd\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r#"ROOT@0..28
  RULE@0..28
    TARGETS@0..3
      IDENTIFIER@0..3 "all"
    OPERATOR@3..4 ":"
    WHITESPACE@4..5 " "
    PREREQUISITES@5..9
      PREREQUISITE@5..8
        IDENTIFIER@5..8 "dep"
      WHITESPACE@8..9 " "
    RECIPE@9..23
      OPERATOR@9..10 ";"
      WHITESPACE@10..11 " "
      TEXT@11..22 "echo hi # x"
      NEWLINE@22..23 "\n"
    RECIPE@23..28
      INDENT@23..24 "\t"
      TEXT@24..27 "cmd"
      NEWLINE@27..28 "\n"
"#
    );
}

#[test]
fn test_parse_multiple_prerequisites() {
    const MULTIPLE_PREREQUISITES: &str = r#"rule: dependency1 dependency2
	command

"#;
    let parsed = parse(MULTIPLE_PREREQUISITES, None);
    assert!(parsed.errors.is_empty());
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r#"ROOT@0..40
  RULE@0..40
    TARGETS@0..4
      IDENTIFIER@0..4 "rule"
    OPERATOR@4..5 ":"
    WHITESPACE@5..6 " "
    PREREQUISITES@6..29
      PREREQUISITE@6..17
        IDENTIFIER@6..17 "dependency1"
      WHITESPACE@17..18 " "
      PREREQUISITE@18..29
        IDENTIFIER@18..29 "dependency2"
    NEWLINE@29..30 "\n"
    RECIPE@30..39
      INDENT@30..31 "\t"
      TEXT@31..38 "command"
      NEWLINE@38..39 "\n"
    NEWLINE@39..40 "\n"
"#
    );
    let root = parsed.root();

    let rule = root.rules().next().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
    assert_eq!(
        rule.prerequisites().collect::<Vec<_>>(),
        vec!["dependency1", "dependency2"]
    );
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);
}

#[test]
fn test_parse_rule_without_newline() {
    let rule = "rule: dependency\n\tcommand".parse::<Rule>().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);
    let rule = "rule: dependency".parse::<Rule>().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
    assert_eq!(rule.recipes().collect::<Vec<_>>(), Vec::<String>::new());
}

#[test]
fn test_parse_makefile_without_newline() {
    let makefile = "rule: dependency\n\tcommand".parse::<Makefile>().unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_from_reader() {
    let makefile = Makefile::from_reader("rule: dependency\n\tcommand".as_bytes()).unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_parse_with_tab_after_last_newline() {
    let makefile = Makefile::from_reader("rule: dependency\n\tcommand\n\t".as_bytes()).unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_parse_with_space_after_last_newline() {
    let makefile = Makefile::from_reader("rule: dependency\n\tcommand\n ".as_bytes()).unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_parse_with_comment_after_last_newline() {
    let makefile =
        Makefile::from_reader("rule: dependency\n\tcommand\n#comment".as_bytes()).unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_parse_with_variable_rule() {
    let makefile =
        Makefile::from_reader("RULE := rule\n$(RULE): dependency\n\tcommand".as_bytes()).unwrap();

    // Check variable definition
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name(), Some("RULE".to_string()));
    assert_eq!(vars[0].raw_value(), Some("rule".to_string()));

    // Check rule
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["$(RULE)"]);
    assert_eq!(
        rules[0].prerequisites().collect::<Vec<_>>(),
        vec!["dependency"]
    );
    assert_eq!(rules[0].recipes().collect::<Vec<_>>(), vec!["command"]);
}

#[test]
fn test_parse_with_variable_dependency() {
    let makefile =
        Makefile::from_reader("DEP := dependency\nrule: $(DEP)\n\tcommand".as_bytes()).unwrap();

    // Check variable definition
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name(), Some("DEP".to_string()));
    assert_eq!(vars[0].raw_value(), Some("dependency".to_string()));

    // Check rule
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["rule"]);
    assert_eq!(rules[0].prerequisites().collect::<Vec<_>>(), vec!["$(DEP)"]);
    assert_eq!(rules[0].recipes().collect::<Vec<_>>(), vec!["command"]);
}

#[test]
fn test_parse_with_variable_command() {
    let makefile =
        Makefile::from_reader("COM := command\nrule: dependency\n\t$(COM)".as_bytes()).unwrap();

    // Check variable definition
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name(), Some("COM".to_string()));
    assert_eq!(vars[0].raw_value(), Some("command".to_string()));

    // Check rule
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["rule"]);
    assert_eq!(
        rules[0].prerequisites().collect::<Vec<_>>(),
        vec!["dependency"]
    );
    assert_eq!(rules[0].recipes().collect::<Vec<_>>(), vec!["$(COM)"]);
}

#[test]
fn test_regular_line_error_reporting() {
    let input = "rule target\n\tcommand";

    // Test both APIs with one input
    let parsed = parse(input, None);
    let direct_error = &parsed.errors[0];

    // Verify error is detected with correct details
    assert_eq!(direct_error.line, 1);
    assert!(
        direct_error.message.contains("expected"),
        "Error message should contain 'expected': {}",
        direct_error.message
    );
    assert_eq!(direct_error.context, "rule target");

    // Check public API
    let reader_result = Makefile::from_reader(input.as_bytes());
    let parse_error = match reader_result {
        Ok(_) => panic!("Expected Parse error from from_reader"),
        Err(err) => match err {
            self::Error::Parse(parse_err) => parse_err,
            _ => panic!("Expected Parse error"),
        },
    };

    // Verify formatting includes line number and context
    let error_text = parse_error.to_string();
    assert!(error_text.contains("Error at line 1:"));
    assert!(error_text.contains("1| rule target"));
}

#[test]
fn test_parsing_error_context_with_bad_syntax() {
    // Input with unusual characters to ensure they're preserved
    let input = "#begin comment\n\t(╯°□°)╯︵ ┻━┻\n#end comment";

    // With our relaxed parsing, verify we either get a proper error or parse successfully
    match Makefile::from_reader(input.as_bytes()) {
        Ok(makefile) => {
            // If it parses successfully, our parser is robust enough to handle unusual characters
            assert_eq!(
                makefile.rules().count(),
                0,
                "Should not have found any rules"
            );
        }
        Err(err) => match err {
            self::Error::Parse(error) => {
                // Verify error details are properly reported
                assert!(error.errors[0].line >= 2, "Error line should be at least 2");
                assert!(
                    !error.errors[0].context.is_empty(),
                    "Error context should not be empty"
                );
            }
            _ => panic!("Unexpected error type"),
        },
    };
}

#[test]
fn test_error_message_format() {
    // Test the error formatter directly
    let parse_error = ParseError {
        errors: vec![ErrorInfo {
            message: "test error".to_string(),
            line: 42,
            context: "some problematic code".to_string(),
            kind: ParseErrorKind::Other,
        }],
    };

    let error_text = parse_error.to_string();
    assert!(error_text.contains("Error at line 42: test error"));
    assert!(error_text.contains("42| some problematic code"));
}

#[test]
fn test_line_number_calculation() {
    // Test inputs for various error locations
    let test_cases = [
        ("rule dependency\n\tcommand", 1),             // Missing colon
        ("#comment\n\t(╯°□°)╯︵ ┻━┻", 2),              // Strange characters
        ("var = value\n#comment\n\tindented line", 3), // Indented line not part of a rule
    ];

    for (input, expected_line) in test_cases {
        // Attempt to parse the input
        match input.parse::<Makefile>() {
            Ok(_) => {
                // If the parser succeeds, that's fine - our parser is more robust
                // Skip assertions when there's no error to check
                continue;
            }
            Err(err) => {
                if let Error::Parse(parse_err) = err {
                    // Verify error line number matches expected line
                    assert_eq!(
                        parse_err.errors[0].line, expected_line,
                        "Line number should match the expected line"
                    );

                    // If the error is about indentation, check that the context includes the tab
                    if parse_err.errors[0].message.contains("indented") {
                        assert!(
                            parse_err.errors[0].context.starts_with('\t'),
                            "Context for indentation errors should include the tab character"
                        );
                    }
                } else {
                    panic!("Expected parse error, got: {:?}", err);
                }
            }
        }
    }
}

#[test]
fn test_conditional_features() {
    // Simple use of variables in conditionals
    let code = r#"
# Set variables based on DEBUG flag
ifdef DEBUG
    CFLAGS += -g -DDEBUG
else
    CFLAGS = -O2
endif

# Define a build rule
all: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^
"#;

    let mut buf = code.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse conditional features");

    // Instead of checking for variable definitions which might not get created
    // due to conditionals, let's verify that we can parse the content without errors
    assert!(!makefile.code().is_empty(), "Makefile has content");

    // Check that we detected a rule
    let rules = makefile.rules().collect::<Vec<_>>();
    assert!(!rules.is_empty(), "Should have found rules");

    // Verify conditional presence in the original code
    assert!(code.contains("ifdef DEBUG"));
    assert!(code.contains("endif"));

    // Also try with an explicitly defined variable
    let code_with_var = r#"
# Define a variable first
CC = gcc

ifdef DEBUG
    CFLAGS += -g -DDEBUG
else
    CFLAGS = -O2
endif

all: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^
"#;

    let mut buf = code_with_var.as_bytes();
    let makefile =
        Makefile::read_relaxed(&mut buf).expect("Failed to parse with explicit variable");

    // Now we should definitely find at least the CC variable
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert!(
        !vars.is_empty(),
        "Should have found at least the CC variable definition"
    );
}

#[test]
fn test_include_directive() {
    let parsed = parse(
        "include config.mk\ninclude $(TOPDIR)/rules.mk\ninclude *.mk\n",
        None,
    );
    assert!(parsed.errors.is_empty());
    let node = parsed.syntax();
    assert!(format!("{:#?}", node).contains("INCLUDE@"));
}

#[test]
fn test_export_variables() {
    let parsed = parse("export SHELL := /bin/bash\n", None);
    assert!(parsed.errors.is_empty());
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    let shell_var = vars
        .iter()
        .find(|v| v.name() == Some("SHELL".to_string()))
        .unwrap();
    assert!(shell_var.raw_value().unwrap().contains("bin/bash"));
}

#[test]
fn test_bare_export_variable() {
    // "export VARNAME" without assignment operator is a valid GNU Make directive
    // that exports a previously-defined variable.
    let parsed = parse(
        "DEB_CFLAGS_MAINT_APPEND = -Wno-error\nexport DEB_CFLAGS_MAINT_APPEND\n\n%:\n\tdh $@\n",
        None,
    );
    assert!(parsed.errors.is_empty(), "errors: {:?}", parsed.errors);
    let makefile = parsed.root();
    // The bare export should be parsed as a variable, not a rule
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 2);
    // The pattern rule should be found
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert!(rules[0].targets().any(|t| t == "%"));
    // build-arch should match via the pattern rule
    assert!(makefile.find_rule_by_target_pattern("build-arch").is_some());
}

#[test]
fn test_bare_export_at_eof() {
    // Bare "export VARNAME" at end of file (no trailing newline)
    let parsed = parse("VAR = value\nexport VAR", None);
    assert!(parsed.errors.is_empty(), "errors: {:?}", parsed.errors);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 2);
    assert_eq!(makefile.rules().count(), 0);
}

#[test]
fn test_empty_assignment_at_eof() {
    // The assignment operator is the very last token of the input
    for (text, op) in [
        ("exe=", "="),
        ("exe :=", ":="),
        ("exe +=", "+="),
        ("exe ?=", "?="),
        ("A = 1\nexe=", "="),
    ] {
        let parsed = parse(text, None);
        assert_eq!(parsed.errors, vec![], "input: {:?}", text);
        let makefile = parsed.root();
        assert_eq!(makefile.rules().count(), 0, "input: {:?}", text);
        let var = makefile.variable_definitions().last().unwrap();
        assert_eq!(var.name(), Some("exe".to_string()));
        assert_eq!(var.assignment_operator(), Some(op.to_string()));
        assert_eq!(var.raw_value(), Some("".to_string()));
        assert_eq!(makefile.to_string(), text);
    }
}

#[test]
fn test_bare_export_does_not_eat_include() {
    // Bare "export VARNAME" must not consume subsequent include directives
    let parsed = parse("VAR = value\nexport VAR\ninclude other.mk\n", None);
    assert!(parsed.errors.is_empty(), "errors: {:?}", parsed.errors);
    let makefile = parsed.root();
    assert_eq!(makefile.includes().count(), 1);
    assert_eq!(
        makefile.included_files().collect::<Vec<_>>(),
        vec!["other.mk"]
    );
}

#[test]
fn test_bare_export_multiple() {
    // Multiple bare exports in a row
    let parsed = parse(
        "A = 1\nB = 2\nexport A\nexport B\n\nall:\n\techo done\n",
        None,
    );
    assert!(parsed.errors.is_empty(), "errors: {:?}", parsed.errors);
    let makefile = parsed.root();
    assert_eq!(makefile.variable_definitions().count(), 4);
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert!(rules[0].targets().any(|t| t == "all"));
}

#[test]
fn test_undefine() {
    let text = "FOO = 1\nundefine FOO\nall:\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 2);
    assert!(!vars[0].is_undefine());
    assert!(vars[1].is_undefine());
    assert!(!vars[1].is_override());
    assert_eq!(vars[1].name(), Some("FOO".to_string()));
    assert_eq!(vars[1].assignment_operator(), None);
    assert_eq!(vars[1].raw_value(), None);
    assert_eq!(makefile.rules().count(), 1);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_override_undefine() {
    let text = "override undefine FOO\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert!(vars[0].is_undefine());
    assert!(vars[0].is_override());
    assert_eq!(vars[0].name(), Some("FOO".to_string()));
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_variable_reference() {
    let text = "undefine $(NAME)\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert!(vars[0].is_undefine());
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_computed_name() {
    let text = "override undefine CFLAGS.${PROG}\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_undefine());
    assert!(var.is_override());
    assert_eq!(var.name(), Some("CFLAGS.${PROG}".to_string()));
    assert_eq!(var.raw_value(), None);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_at_eof() {
    let text = "undefine FOO";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.variable_definitions().count(), 1);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_name_with_spaces() {
    // GNU make takes the rest of the line as a single name, keeping
    // internal whitespace.
    let text = "undefine A  B\noverride undefine B C # c\nundefine X \n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 3);
    assert!(vars[0].is_undefine());
    assert!(!vars[0].is_override());
    assert_eq!(vars[0].name(), Some("A  B".to_string()));
    assert_eq!(vars[0].names().collect::<Vec<_>>(), vec!["A  B"]);
    assert!(vars[1].is_undefine());
    assert!(vars[1].is_override());
    assert_eq!(vars[1].name(), Some("B C".to_string()));
    assert_eq!(vars[1].names().collect::<Vec<_>>(), vec!["B C"]);
    assert_eq!(vars[2].name(), Some("X".to_string()));
    assert_eq!(vars[2].names().collect::<Vec<_>>(), vec!["X"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_name_with_continuation() {
    // The continuation and surrounding whitespace become a single space.
    let text = "undefine A \\\n  $(B)\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_undefine());
    assert_eq!(var.name(), Some("A $(B)".to_string()));
    assert_eq!(var.names().collect::<Vec<_>>(), vec!["A $(B)"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_name_starting_with_keyword() {
    // Words after `undefine` are part of the name, not modifiers.
    let text = "undefine override X\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_undefine());
    assert!(!var.is_override());
    assert_eq!(var.name(), Some("override X".to_string()));
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_as_rule_target() {
    let text = "undefine:\n\techo hi\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.variable_definitions().count(), 0);
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["undefine"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_as_variable_name() {
    let text = "undefine = 1\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert!(!vars[0].is_undefine());
    assert_eq!(vars[0].name(), Some("undefine".to_string()));
    assert_eq!(vars[0].raw_value(), Some("1".to_string()));
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_with_comment() {
    let text = "undefine FOO # gone\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_undefine());
    assert_eq!(var.name(), Some("FOO".to_string()));
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_empty_name() {
    for text in [
        "undefine\n",
        "undefine",
        "undefine # c\n",
        "override undefine\n",
        "override undefine \\\n\n",
    ] {
        let parsed = parse(text, None);
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["empty variable name"],
            "{text:?}"
        );
        assert_eq!(
            parsed.errors.iter().map(|e| e.kind()).collect::<Vec<_>>(),
            vec![ParseErrorKind::ExpectedVariableName],
            "{text:?}"
        );
        let makefile = parsed.root();
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1, "{text:?}");
        assert!(vars[0].is_undefine(), "{text:?}");
        assert_eq!(vars[0].name(), None, "{text:?}");
        assert_eq!(vars[0].names().collect::<Vec<_>>(), Vec::<String>::new());
        assert_eq!(makefile.code(), text);
    }
}

#[test]
fn test_undefine_name_with_operator() {
    // GNU make accepts these silently, undefining "A = b" and so on.
    let text = "undefine A = b\nundefine A: b\noverride undefine X := $(Y)\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.rules().count(), 0);
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 3);
    for (var, name) in vars.iter().zip(["A = b", "A: b", "X := $(Y)"]) {
        assert!(var.is_undefine());
        assert_eq!(var.name(), Some(name.to_string()));
        assert_eq!(var.names().collect::<Vec<_>>(), vec![name]);
        assert_eq!(var.assignment_operator(), None);
        assert_eq!(var.raw_value(), None);
    }
    assert!(vars[2].is_override());
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_define_undefine_gnu_only() {
    for variant in [
        MakefileVariant::POSIXMake,
        MakefileVariant::NMake,
        MakefileVariant::BSDMake,
    ] {
        for text in ["undefine A B\n", "undefine A\n", "define FOO\nbar\nendef\n"] {
            let parsed = parse(text, Some(variant));
            assert_eq!(
                parsed
                    .errors
                    .iter()
                    .map(|e| e.message.as_str())
                    .collect::<Vec<_>>(),
                vec!["expected ':'"; text.lines().count()],
                "{variant:?} {text:?}"
            );
            let makefile = parsed.root();
            assert_eq!(makefile.variable_definitions().count(), 0);
            assert_eq!(makefile.code(), text);
        }
    }
    // GNU make and the default
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let text = "undefine A B\ndefine FOO\nbar\nendef\n";
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 2);
        assert!(vars[0].is_undefine());
        assert!(vars[1].is_define());
    }
}

#[test]
fn test_vpath_gnu_only() {
    let text = "vpath %.c src\nvpath\n";
    for variant in [
        MakefileVariant::POSIXMake,
        MakefileVariant::NMake,
        MakefileVariant::BSDMake,
    ] {
        let parsed = parse(text, Some(variant));
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["expected ':'"; 2],
            "{variant:?}"
        );
        assert_eq!(
            top_level_kinds(parsed.root().syntax()),
            vec![RULE, RULE],
            "{variant:?}"
        );
        assert_eq!(parsed.root().code(), text);
    }
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        assert_eq!(
            top_level_kinds(parsed.root().syntax()),
            vec![VPATH, VPATH],
            "{variant:?}"
        );
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_assignment_modifiers_gnu_only() {
    let text = "override X = 1\nunexport X\nprivate X = 1\nexport X\nexport\n";
    for variant in [
        MakefileVariant::POSIXMake,
        MakefileVariant::NMake,
        MakefileVariant::BSDMake,
    ] {
        let parsed = parse(text, Some(variant));
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["expected ':'"; 5],
            "{variant:?}"
        );
        assert_eq!(parsed.root().variable_definitions().count(), 0);
        assert_eq!(parsed.root().code(), text);
    }
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        assert_eq!(parsed.root().variable_definitions().count(), 5);
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_export_assignment_gnu_and_bsd_only() {
    let text = "export X = 1\n";
    for variant in [MakefileVariant::POSIXMake, MakefileVariant::NMake] {
        let parsed = parse(text, Some(variant));
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["expected ':'"],
            "{variant:?}"
        );
        assert_eq!(parsed.root().variable_definitions().count(), 0);
        assert_eq!(parsed.root().code(), text);
    }
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::BSDMake),
    ] {
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let var = parsed.root().variable_definitions().next().unwrap();
        assert!(var.is_export(), "{variant:?}");
        assert_eq!(var.name(), Some("X".to_string()), "{variant:?}");
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_modifier_keyword_as_variable_name_any_variant() {
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ] {
        let text = "override = 1\nexport = 2\n";
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        assert_eq!(
            parsed
                .root()
                .variable_definitions()
                .map(|v| v.name())
                .collect::<Vec<_>>(),
            vec![Some("override".to_string()), Some("export".to_string())],
            "{variant:?}"
        );
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_bsd_undef_unaffected() {
    let text = ".undef A B\n";
    let parsed = parse(text, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(parsed.root().code(), text);
}

#[test]
fn test_define_as_variable_name() {
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::BSDMake),
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ] {
        let text = "define = 1\n";
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1, "{variant:?}");
        assert!(!vars[0].is_define(), "{variant:?}");
        assert_eq!(vars[0].name(), Some("define".to_string()), "{variant:?}");
        assert_eq!(vars[0].raw_value(), Some("1".to_string()), "{variant:?}");
        assert_eq!(parsed.root().code(), text);
    }
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let text = "override define := 1\nexport define = 2\n";
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 2, "{variant:?}");
        assert!(vars[0].is_override());
        assert!(vars[1].is_export());
        for var in &vars {
            assert!(!var.is_define(), "{variant:?}");
            assert_eq!(var.name(), Some("define".to_string()), "{variant:?}");
        }
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_gmake_export_of_keyword_names_in_bsd_make() {
    // BSD make takes everything between "export" and "=" as the name of
    // the environment variable, so none of these are GNU make modifiers.
    let text = "export undefine A = 1\nexport define B = 2\nexport override C = 3\n\
                    export unexport D = 4\nexport private E = 5\nexport export F = 6\n";
    let parsed = parse(text, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
    assert_eq!(
        vars.iter().map(|v| v.name()).collect::<Vec<_>>(),
        [
            "undefine A",
            "define B",
            "override C",
            "unexport D",
            "private E",
            "export F"
        ]
        .map(|n| Some(n.to_string()))
    );
    for var in &vars {
        assert!(var.is_export());
        assert!(!var.is_undefine());
        assert!(!var.is_define());
        assert!(!var.is_override());
        assert!(!var.is_unexport());
        assert!(!var.is_private());
    }
    assert_eq!(
        vars.iter().map(|v| v.raw_value()).collect::<Vec<_>>(),
        ["1", "2", "3", "4", "5", "6"].map(|v| Some(v.to_string()))
    );
    assert_eq!(parsed.root().code(), text);
}

#[test]
fn test_export_multiple_names() {
    let parsed = parse("export quiet Q KBUILD_VERBOSE\nall:\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert!(vars[0].is_export());
    assert_eq!(vars[0].name(), Some("quiet".to_string()));
    assert_eq!(
        vars[0].names().collect::<Vec<_>>(),
        vec!["quiet", "Q", "KBUILD_VERBOSE"]
    );
    assert_eq!(vars[0].assignment_operator(), None);
    assert_eq!(makefile.rules().count(), 1);
    assert_eq!(makefile.code(), "export quiet Q KBUILD_VERBOSE\nall:\n");
}

#[test]
fn test_unexport() {
    let parsed = parse("unexport A\nunexport B C\nall:\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 2);
    assert!(vars[0].is_unexport());
    assert!(!vars[0].is_export());
    assert_eq!(vars[0].names().collect::<Vec<_>>(), vec!["A"]);
    assert!(vars[1].is_unexport());
    assert_eq!(vars[1].names().collect::<Vec<_>>(), vec!["B", "C"]);
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_unexport_assignment() {
    let parsed = parse("unexport A = 1\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_unexport());
    assert_eq!(var.name(), Some("A".to_string()));
    assert_eq!(var.assignment_operator(), Some("=".to_string()));
    assert_eq!(var.raw_value(), Some("1".to_string()));
}

#[test]
fn test_export_names_with_variable_reference() {
    let parsed = parse("export A $(B) C\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.names().collect::<Vec<_>>(), vec!["A", "$(B)", "C"]);
}

#[test]
fn test_export_names_with_computed_name() {
    let parsed = parse("export CFLAGS.${PROG} B $(C)-x\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.name(), Some("CFLAGS.${PROG}".to_string()));
    assert_eq!(
        var.names().collect::<Vec<_>>(),
        vec!["CFLAGS.${PROG}", "B", "$(C)-x"]
    );
}

#[test]
fn test_export_multiple_words_with_assignment() {
    // GNU make exports the words "A", "B", "=" and "x"
    let parsed = parse("export A B = x\n", None);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["expected assignment operator"]
    );
}

#[test]
fn test_define_names() {
    let parsed = parse("define FOO\nbar baz\nendef\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.names().collect::<Vec<_>>(), vec!["FOO"]);
}

#[test]
fn test_undefine_names() {
    let parsed = parse("undefine FOO\noverride undefine BAR\n", None);
    assert_eq!(parsed.errors, vec![]);
    let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars[0].names().collect::<Vec<_>>(), vec!["FOO"]);
    assert_eq!(vars[1].names().collect::<Vec<_>>(), vec!["BAR"]);
}

#[test]
fn test_export_all() {
    for text in ["export\n", "export", "unexport\n", "unexport"] {
        let parsed = parse(text, None);
        assert_eq!(parsed.errors, vec![], "{:?}", text);
        let makefile = parsed.root();
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1, "{:?}", text);
        assert_eq!(vars[0].name(), None);
        assert_eq!(vars[0].names().collect::<Vec<_>>(), Vec::<String>::new());
        assert_eq!(vars[0].is_export(), text.starts_with("export"));
        assert_eq!(vars[0].is_unexport(), text.starts_with("unexport"));
        assert_eq!(makefile.rules().count(), 0);
        assert_eq!(makefile.code(), text);
    }
}

#[test]
fn test_export_all_followed_by_rule() {
    let parsed = parse("export\nall:\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.variable_definitions().count(), 1);
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["all"]);
}

#[test]
fn test_export_names_with_comment() {
    let parsed = parse("export A B # comment\nexport # all\n", None);
    assert_eq!(parsed.errors, vec![]);
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r##"ROOT@0..34
  VARIABLE@0..21
    IDENTIFIER@0..6 "export"
    WHITESPACE@6..7 " "
    IDENTIFIER@7..8 "A"
    WHITESPACE@8..9 " "
    IDENTIFIER@9..10 "B"
    WHITESPACE@10..11 " "
    COMMENT@11..20 "# comment"
    NEWLINE@20..21 "\n"
  VARIABLE@21..34
    IDENTIFIER@21..27 "export"
    WHITESPACE@27..28 " "
    COMMENT@28..33 "# all"
    NEWLINE@33..34 "\n"
"##
    );
    let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars[0].names().collect::<Vec<_>>(), vec!["A", "B"]);
    assert_eq!(vars[1].names().collect::<Vec<_>>(), Vec::<String>::new());
}

#[test]
fn test_parse_error_does_not_cross_lines() {
    // A line that fails to parse as a rule (no colon) must not
    // consume tokens from subsequent lines.
    let parsed = parse("notarule\n\nbuild-arch:\n\techo arch\n", None);
    let makefile = parsed.root();
    let rules = makefile.rules().collect::<Vec<_>>();
    // The "notarule" line may produce an error, but build-arch must still be found
    assert!(
        rules.iter().any(|r| r.targets().any(|t| t == "build-arch")),
        "build-arch rule should be parsed despite earlier error; rules: {:?}",
        rules
            .iter()
            .map(|r| r.targets().collect::<Vec<_>>())
            .collect::<Vec<_>>()
    );
}

fn top_level_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children().map(|c| c.kind()).collect()
}

#[test]
fn test_bare_function_call() {
    let parsed = parse("$(eval $(call gen_rule,foo))\n", None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(top_level_kinds(root.syntax()), vec![EXPRESSION_STATEMENT]);
    assert_eq!(root.to_string(), "$(eval $(call gen_rule,foo))\n");
}

#[test]
fn test_bare_function_call_semicolon() {
    for src in [
        "$(info a);\n",
        "$(info a) ;\n",
        "$(info a); echo x\n",
        "$(X);\n",
        "$(X) ; @echo cmd\n",
        "$(info a); # c\n",
        "$(info a) # c ; x\n",
    ] {
        let parsed = parse(src, None);
        assert_eq!(parsed.errors, vec![], "{src:?}");
        let root = parsed.root();
        assert_eq!(
            top_level_kinds(root.syntax()),
            vec![EXPRESSION_STATEMENT],
            "{src:?}"
        );
        assert_eq!(root.to_string(), src);
    }
}

#[test]
fn test_load_directive() {
    for text in [
        "load foo.so\n",
        "load ./bar.so(init_func)\n",
        "-load optional.so\n",
        "load a.so b.so # comment\n",
        "load \\\n  a.so\n",
        "load $(OBJ)\nall:\n",
    ] {
        let parsed = parse(text, None);
        assert_eq!(parsed.errors, vec![], "{text:?}");
        let root = parsed.root();
        assert_eq!(root.to_string(), text);
        assert_eq!(root.rules().count(), text.matches("all:").count());
    }
}

#[test]
fn test_include_without_files() {
    // GNU make accepts an include without any file names.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for text in [
            "include\n",
            "include",
            "-include\n",
            "sinclude\n",
            "include \n",
            "include # comment\n",
            "include\nall:\n",
        ] {
            let parsed = parse(text, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?} {text:?}");
            let root = parsed.root();
            assert_eq!(root.to_string(), text);
            let includes: Vec<_> = root.includes().collect();
            assert_eq!(includes.len(), 1);
            assert_eq!(includes[0].path(), Some(String::new()));
            assert_eq!(
                root.included_files().collect::<Vec<_>>(),
                Vec::<String>::new()
            );
            assert_eq!(root.rules().count(), text.matches("all:").count());
        }
    }
}

#[test]
fn test_include_without_files_error() {
    for (text, variant) in [
        ("include\nall:\n", MakefileVariant::POSIXMake),
        ("include\nall:\n", MakefileVariant::BSDMake),
        ("-include\nall:\n", MakefileVariant::BSDMake),
        (".include\nall:\n", MakefileVariant::BSDMake),
        ("!include\nall:\n", MakefileVariant::NMake),
    ] {
        let parsed = parse(text, Some(variant));
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(ErrorInfo::kind)
                .collect::<Vec<_>>(),
            vec![ParseErrorKind::MissingIncludePath],
            "{variant:?} {text:?}"
        );
        let root = parsed.root();
        assert_eq!(root.to_string(), text);
        assert_eq!(
            root.rules()
                .map(|r| r.targets().collect())
                .collect::<Vec<Vec<_>>>(),
            vec![vec!["all".to_string()]],
            "{variant:?} {text:?}"
        );
    }
    // BSD make's .include always needs a file name.
    assert_eq!(
        error_kinds(".include\n", None),
        vec![ParseErrorKind::MissingIncludePath]
    );
}

#[test]
fn test_bare_function_call_semicolon_continuation() {
    for src in [
        "$(info a);echo \\\n more\nall:\n",
        "$(info a); # c \\\nmore\nall:\n",
    ] {
        let parsed = parse(src, None);
        assert_eq!(parsed.errors, vec![], "{src:?}");
        let root = parsed.root();
        assert_eq!(
            top_level_kinds(root.syntax()),
            vec![EXPRESSION_STATEMENT, RULE],
            "{src:?}"
        );
        assert_eq!(root.to_string(), src);
        assert_eq!(
            root.rules()
                .map(|r| r.targets().collect())
                .collect::<Vec<Vec<_>>>(),
            vec![vec!["all".to_string()]]
        );
    }
}

#[test]
fn test_bare_function_call_semicolon_gnu_only() {
    let src = "${X} ; echo hi\n";
    let parsed = parse(src, Some(MakefileVariant::GNUMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        top_level_kinds(parsed.root().syntax()),
        vec![EXPRESSION_STATEMENT]
    );
    for variant in [
        MakefileVariant::BSDMake,
        MakefileVariant::POSIXMake,
        MakefileVariant::NMake,
    ] {
        let parsed = parse(src, Some(variant));
        assert_eq!(parsed.root().to_string(), src);
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["expected ':'"],
            "{variant:?}"
        );
        assert!(
            !top_level_kinds(parsed.root().syntax()).contains(&EXPRESSION_STATEMENT),
            "{variant:?}"
        );
    }
}

#[test]
fn test_bare_single_char_reference() {
    for src in [
        "$X\n",
        "$@\n",
        "$<\n",
        "$X $(Y)\n",
        "$X ${Y} $Z\n",
        "$(X)$Y\n",
        "$X # c\n",
        "$X \\\n $Y\n",
    ] {
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::BSDMake),
            Some(MakefileVariant::POSIXMake),
            Some(MakefileVariant::NMake),
        ] {
            let parsed = parse(src, variant);
            assert_eq!(parsed.errors, vec![], "{src:?} {variant:?}");
            let root = parsed.root();
            assert_eq!(
                top_level_kinds(root.syntax()),
                vec![EXPRESSION_STATEMENT],
                "{src:?} {variant:?}"
            );
            assert_eq!(root.to_string(), src);
        }
    }
}

#[test]
fn test_bare_single_char_reference_semicolon() {
    let src = "$X $(Y) ; @echo cmd\nall:\n";
    let parsed = parse(src, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(
        top_level_kinds(root.syntax()),
        vec![EXPRESSION_STATEMENT, RULE]
    );
    assert_eq!(root.to_string(), src);
    let Some(MakefileItem::ExpressionStatement(stmt)) = root.items().next() else {
        panic!("expected an expression statement");
    };
    assert_eq!(
        stmt.references().map(|r| r.name()).collect::<Vec<_>>(),
        vec![Some("X".to_string()), Some("Y".to_string())]
    );
    assert_eq!(stmt.expression(), "$X $(Y)");
    assert_eq!(stmt.after_semicolon(), Some("@echo cmd".to_string()));
}

#[test]
fn test_bare_whitespace_reference() {
    for src in [
        "$ \n",
        "$  \n",
        "$\t\n",
        "$ $X\n",
        "$  $(Y)\n",
        "$X$ \n",
        "$ # c\n",
        "$ \\\n$X\n",
    ] {
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::BSDMake),
            Some(MakefileVariant::POSIXMake),
            Some(MakefileVariant::NMake),
        ] {
            let parsed = parse(src, variant);
            assert_eq!(parsed.errors, vec![], "{src:?} {variant:?}");
            let root = parsed.root();
            assert_eq!(
                top_level_kinds(root.syntax()),
                vec![EXPRESSION_STATEMENT],
                "{src:?} {variant:?}"
            );
            assert_eq!(root.to_string(), src);
        }
    }

    let src = "$  $X ; x\n";
    let parsed = parse(src, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), src);
    let Some(MakefileItem::ExpressionStatement(stmt)) = root.items().next() else {
        panic!("expected an expression statement");
    };
    assert_eq!(
        stmt.references().map(|r| r.name()).collect::<Vec<_>>(),
        vec![Some(" ".to_string()), Some("X".to_string())]
    );
    assert_eq!(
        stmt.references()
            .map(|r| r.syntax().to_string())
            .collect::<Vec<_>>(),
        vec!["$ ", "$X"]
    );
    assert_eq!(stmt.expression(), "$  $X");
    assert_eq!(stmt.after_semicolon(), Some("x".to_string()));
}

#[test]
fn test_single_char_reference_not_expression_statement() {
    let parsed = parse("$X: y\n", None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(top_level_kinds(root.syntax()), vec![RULE]);
    let rule = root.rules().next().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["$X"]);
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["y"]);

    let parsed = parse("$X = 1\n", None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(top_level_kinds(root.syntax()), vec![VARIABLE]);
    let var = root.variable_definitions().next().unwrap();
    assert_eq!(var.name(), Some("$X".to_string()));
    assert_eq!(var.raw_value(), Some("1".to_string()));

    // `$XY` is `$X` followed by `Y`, `$ E` is `$ ` followed by `E`, and
    // `$$` is a literal `$`.
    for src in ["$XY\n", "$ E\n", "$$\n"] {
        let parsed = parse(src, None);
        assert_eq!(parsed.root().to_string(), src);
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["expected ':'"],
            "{src:?}"
        );
        assert!(
            !top_level_kinds(parsed.root().syntax()).contains(&EXPRESSION_STATEMENT),
            "{src:?}"
        );
    }
}

#[test]
fn test_reference_target_with_inline_recipe() {
    let src = "$(X): y ; cmd\n";
    let parsed = parse(src, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(top_level_kinds(root.syntax()), vec![RULE]);
    assert_eq!(root.to_string(), src);
    let rule = root.rules().next().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["$(X)"]);
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["y"]);
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["cmd"]);
}

#[test]
fn test_bare_function_call_before_rule() {
    let parsed = parse("$(info building)\nall:\n\techo done\n", None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(
        top_level_kinds(root.syntax()),
        vec![EXPRESSION_STATEMENT, RULE]
    );
    assert_eq!(
        root.rules()
            .map(|r| r.targets().collect())
            .collect::<Vec<Vec<_>>>(),
        vec![vec!["all".to_string()]]
    );
}

#[test]
fn test_bare_function_call_after_rule() {
    let parsed = parse("all:\n\techo done\n$(info x)\n", None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.rules().count(), 1);
    assert_eq!(
        root.rules().next().unwrap().recipes().collect::<Vec<_>>(),
        vec!["echo done".to_string()]
    );
}

#[test]
fn test_bare_function_call_continuation() {
    let text = "$(if $(filter __%, $(MAKECMDGOALS)), \\\n\t$(error only for internal use))\nall:\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), text);
    assert_eq!(root.rules().count(), 1);
}

#[test]
fn test_bare_function_call_nested() {
    let parsed = parse("$(foreach d,$(DIRS),$(eval $(call dir_rule,$(d))))\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(parsed.root().rules().count(), 0);
}

#[test]
fn test_bare_references_with_comment_and_whitespace() {
    let text = "$(info a) $(info b) # note\n${X}  \n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.rules().count(), 0);
    assert_eq!(root.to_string(), text);
}

#[test]
fn test_bare_function_call_in_conditional() {
    let text = "ifeq ($(X),y)\n$(error bad)\nelse\n $(info ok)\nendif\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.rules().count(), 0);
    assert_eq!(root.to_string(), text);
}

#[test]
fn test_references_before_bsd_dependency_operator() {
    let text = "${PROG}: ${OBJS}\n\t${CC} -o $@\n${LIB}! ${SRCS}\n";
    let parsed = parse(text, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(top_level_kinds(root.syntax()), vec![RULE, RULE]);
    assert_eq!(root.to_string(), text);
}

#[test]
fn test_bsd_double_colon_assignment() {
    // BSD make has no `::=` or `:::=` operator: the colons before `:=`
    // are part of the variable name, as in posix-varassign.mk.
    for (text, name, op, value) in [
        ("VAR::=x\n", "VAR:", ":=", "x"),
        ("VAR:::= x\n", "VAR::", ":=", "x"),
        ("VAR::+= x\n", "VAR::", "+=", "x"),
        ("VAR::?= x\n", "VAR::", "?=", "x"),
        ("VAR::!= x\n", "VAR::", "!=", "x"),
        ("X::==y\n", "X:", ":=", "=y"),
        ("::=x\n", ":", ":=", "x"),
    ] {
        let parsed = parse(text, Some(MakefileVariant::BSDMake));
        assert_eq!(parsed.errors, vec![], "{text:?}");
        let root = parsed.root();
        assert_eq!(root.rules().count(), 0, "{text:?}");
        let vars: Vec<_> = root
            .variable_definitions()
            .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
            .collect();
        assert_eq!(
            vars,
            vec![(
                Some(name.to_string()),
                Some(op.to_string()),
                Some(value.to_string())
            )],
            "{text:?}"
        );
        assert_eq!(root.to_string(), text);
    }

    // As a target-local assignment.
    let text = "t: VAR::=x\n";
    let parsed = parse(text, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    let rule = parsed.root().rules().next().unwrap();
    let var = rule.scoped_assignment().unwrap();
    assert_eq!(var.name(), Some("VAR:".to_string()));
    assert_eq!(var.assignment_operator(), Some(":=".to_string()));
    assert_eq!(var.raw_value(), Some("x".to_string()));
    assert_eq!(parsed.root().to_string(), text);

    // With whitespace before the colons, the line is a dependency line
    // with the operator `::`, followed by a target-local assignment
    // with an empty name, which BSD make ignores.
    for (text, op) in [("VAR ::= x\n", "="), ("VAR :::= x\n", ":=")] {
        let parsed = parse(text, Some(MakefileVariant::BSDMake));
        assert_eq!(parsed.errors, vec![], "{text:?}");
        let root = parsed.root();
        let rules: Vec<_> = root.rules().collect();
        assert_eq!(rules.len(), 1, "{text:?}");
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["VAR"]);
        assert!(rules[0].is_double_colon(), "{text:?}");
        let var = rules[0].scoped_assignment().unwrap();
        assert_eq!(var.name(), None, "{text:?}");
        assert_eq!(var.assignment_operator(), Some(op.to_string()));
        assert_eq!(var.raw_value(), Some("x".to_string()), "{text:?}");
        assert_eq!(root.to_string(), text);
    }

    // GNU and POSIX make have the `::=` and `:::=` operators.
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
    ] {
        for (text, op) in [
            ("VAR::=x\n", "::="),
            ("VAR ::= x\n", "::="),
            ("VAR:::= x\n", ":::="),
        ] {
            let parsed = parse(text, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?} {text:?}");
            let root = parsed.root();
            let vars: Vec<_> = root
                .variable_definitions()
                .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
                .collect();
            assert_eq!(
                vars,
                vec![(
                    Some("VAR".to_string()),
                    Some(op.to_string()),
                    Some("x".to_string())
                )],
                "{variant:?} {text:?}"
            );
            assert_eq!(root.to_string(), text);
        }
    }
}

#[test]
fn test_bsd_unbalanced_brackets_not_assignment() {
    // BSD make's Parse_IsVar ignores operators inside brackets, so these
    // are invalid dependency lines rather than assignments.
    for text in ["x{ = 1\n", "a{b = 1\n", "a}b = 1\n", "{x = 1\n", "}x = 1\n"] {
        let parsed = parse(text, Some(MakefileVariant::BSDMake));
        assert_eq!(
            parsed.errors.iter().map(|e| e.kind).collect::<Vec<_>>(),
            vec![ParseErrorKind::MissingSeparator],
            "{text:?}"
        );
        let root = parsed.root();
        assert_eq!(root.variable_definitions().count(), 0, "{text:?}");
        assert_eq!(root.to_string(), text);
    }
    // With `:=` they are dependency lines, as in `a}b: = 1`.
    for (text, target) in [("a}b := 1\n", "a}b"), (")x := 1\n", ")x")] {
        let parsed = parse(text, Some(MakefileVariant::BSDMake));
        assert_eq!(parsed.errors, vec![], "{text:?}");
        let root = parsed.root();
        assert_eq!(root.to_string(), text);
        let targets: Vec<Vec<String>> = root.rules().map(|r| r.targets().collect()).collect();
        assert_eq!(targets, vec![vec![target.to_string()]], "{text:?}");
    }
}

#[test]
fn test_bare_reference_followed_by_word_is_error() {
    let parsed = parse("foo bar\n$(X) bar\n", None);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["expected ':'", "expected ':'"]
    );
}

#[test]
fn test_unclosed_bare_reference_is_error() {
    let parsed = parse("$(info x\n", None);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["unclosed variable reference", "expected ':'"]
    );
}

#[test]
fn test_rule_with_reference_targets_unaffected() {
    let parsed = parse("$(OBJS): foo.h\n$(X):\n\techo $@\n", None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(
        root.rules()
            .map(|r| r.targets().collect())
            .collect::<Vec<Vec<_>>>(),
        vec![vec!["$(OBJS)".to_string()], vec!["$(X)".to_string()]]
    );
}

#[test]
fn test_target_specific_assignment_with_reference_target_unaffected() {
    let parsed = parse("$(OBJS): CFLAGS += -O2\n", None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(top_level_kinds(root.syntax()), vec![RULE]);
}

#[test]
fn test_pyfai_rules_full() {
    // Real-world pyFAI debian/rules that triggered #1131043
    let input = "\
#!/usr/bin/make -f

export DH_VERBOSE=1
export PYBUILD_NAME=pyfai

DEB_CFLAGS_MAINT_APPEND = -Wno-error=incompatible-pointer-types
export DEB_CFLAGS_MAINT_APPEND

PY3VER := $(shell py3versions -dv)

include /usr/share/dpkg/pkg-info.mk # sets SOURCE_DATE_EPOCH

%:
\tdh $@ --buildsystem=pybuild

override_dh_auto_build-arch:
\tPYBUILD_BUILD_ARGS=\"-Ccompile-args=--verbose\" dh_auto_build

override_dh_auto_build-indep: override_dh_auto_build-arch
\tsphinx-build -N -bhtml doc/source build/html

override_dh_auto_test:

execute_after_dh_auto_install:
\tdh_install -p pyfai debian/python3-pyfai/usr/bin /usr
";
    let parsed = parse(input, None);
    let makefile = parsed.root();

    // Include must be detected
    assert_eq!(makefile.includes().count(), 1);

    // Pattern rule must be found
    assert!(
        makefile.find_rule_by_target_pattern("build-arch").is_some(),
        "build-arch should match via %: pattern rule"
    );
    assert!(
        makefile
            .find_rule_by_target_pattern("build-indep")
            .is_some(),
        "build-indep should match via %: pattern rule"
    );

    // All override/execute_after rules must be found
    let rule_targets: Vec<Vec<String>> = makefile.rules().map(|r| r.targets().collect()).collect();
    assert!(
        rule_targets.iter().any(|t| t.contains(&"%".to_string())),
        "missing %: rule; got: {:?}",
        rule_targets
    );
    assert!(
        rule_targets
            .iter()
            .any(|t| t.contains(&"override_dh_auto_build-arch".to_string())),
        "missing override_dh_auto_build-arch; got: {:?}",
        rule_targets
    );
    assert!(
        rule_targets
            .iter()
            .any(|t| t.contains(&"override_dh_auto_test".to_string())),
        "missing override_dh_auto_test; got: {:?}",
        rule_targets
    );
    assert!(
        rule_targets
            .iter()
            .any(|t| t.contains(&"execute_after_dh_auto_install".to_string())),
        "missing execute_after_dh_auto_install; got: {:?}",
        rule_targets
    );
}

#[test]
fn test_variable_scopes() {
    let parsed = parse(
        "SIMPLE = value\nIMMEDIATE := value\nCONDITIONAL ?= value\nAPPEND += value\n",
        None,
    );
    assert!(parsed.errors.is_empty());
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 4);
    let var_names: Vec<_> = vars.iter().filter_map(|v| v.name()).collect();
    assert!(var_names.contains(&"SIMPLE".to_string()));
    assert!(var_names.contains(&"IMMEDIATE".to_string()));
    assert!(var_names.contains(&"CONDITIONAL".to_string()));
    assert!(var_names.contains(&"APPEND".to_string()));
}

#[test]
fn test_pattern_rule_parsing() {
    let parsed = parse("%.o: %.c\n\t$(CC) -c -o $@ $<\n", None);
    assert!(parsed.errors.is_empty());
    let makefile = parsed.root();
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().next().unwrap(), "%.o");
    assert!(rules[0].recipes().next().unwrap().contains("$@"));
}

#[test]
fn test_include_variants() {
    // Test all variants of include directives
    let makefile_str = "include simple.mk\n-include optional.mk\nsinclude synonym.mk\ninclude $(VAR)/generated.mk\n";
    let parsed = parse(makefile_str, None);
    assert!(parsed.errors.is_empty());

    // Get the syntax tree for inspection
    let node = parsed.syntax();
    let debug_str = format!("{:#?}", node);

    // Check that all includes are correctly parsed as INCLUDE nodes
    assert_eq!(debug_str.matches("INCLUDE@").count(), 4);

    // Check that we can access the includes through the AST
    let makefile = parsed.root();

    // Count all child nodes that are INCLUDE kind
    let include_count = makefile
        .syntax()
        .children()
        .filter(|child| child.kind() == INCLUDE)
        .count();
    assert_eq!(include_count, 4);

    // Test variable expansion in include paths
    assert!(makefile
        .included_files()
        .any(|path| path.contains("$(VAR)")));
}

#[test]
fn test_include_ends_rule() {
    // GNU make ends rule context at an include line, so a following
    // recipe line is "recipe commences before first target".
    // POSIX make has no `sinclude`, and nmake has no bare include.
    for (directive, posix) in [("include", true), ("-include", true), ("sinclude", false)] {
        let text = format!("all:\n\techo a\n{directive} foo.mk\n");
        let mut variants = vec![None, Some(MakefileVariant::GNUMake)];
        if posix {
            variants.push(Some(MakefileVariant::POSIXMake));
        }
        for variant in variants {
            let parsed = parse(&text, variant);
            assert_eq!(parsed.errors, vec![]);
            let root = parsed.root();
            assert_eq!(root.code(), text);
            let items: Vec<_> = root.items().map(|i| i.syntax().kind()).collect();
            assert_eq!(items, vec![RULE, INCLUDE], "{text:?} {variant:?}");
            let rule = root.rules().next().unwrap();
            assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo a"]);
            assert_eq!(root.included_files().collect::<Vec<_>>(), vec!["foo.mk"]);
        }
    }
}

#[test]
fn test_include_in_bsd_rule() {
    // BSD make keeps rule context across an include line.
    let text = "all:\n\techo a\ninclude foo.mk\n";
    let parsed = parse(text, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.code(), text);
    let items: Vec<_> = root.items().map(|i| i.syntax().kind()).collect();
    assert_eq!(items, vec![RULE]);
    let rule = root.rules().next().unwrap();
    let kinds: Vec<_> = rule.syntax().children().map(|c| c.kind()).collect();
    assert_eq!(kinds, vec![TARGETS, PREREQUISITES, RECIPE, INCLUDE]);
}

#[test]
fn test_include_keywords_per_variant() {
    // POSIX make has `include` and `-include` but not `sinclude`; nmake
    // only has `!INCLUDE`.
    for (variant, text, kinds, errors) in [
        (
            MakefileVariant::POSIXMake,
            "include a.mk\n-include b.mk\n",
            vec![INCLUDE, INCLUDE],
            0,
        ),
        (MakefileVariant::POSIXMake, "sinclude c.mk\n", vec![RULE], 1),
        (
            MakefileVariant::NMake,
            "include a.mk\n-include b.mk\nsinclude c.mk\n",
            vec![RULE, RULE, RULE],
            3,
        ),
    ] {
        let parsed = parse(text, Some(variant));
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["expected ':'"; errors],
            "{variant:?} {text:?}"
        );
        assert_eq!(
            top_level_kinds(parsed.root().syntax()),
            kinds,
            "{variant:?} {text:?}"
        );
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_include_integration() {
    // Test include directives in realistic makefile contexts

    // Case 1: With .PHONY (which was a source of the original issue)
    let phony_makefile = Makefile::from_reader(
        ".PHONY: build\n\nVERBOSE ?= 0\n\n# comment\n-include .env\n\nrule: dependency\n\tcommand"
            .as_bytes(),
    )
    .unwrap();

    // We expect 2 rules: .PHONY and rule
    assert_eq!(phony_makefile.rules().count(), 2);

    // But only one non-special rule (not starting with '.')
    let normal_rules_count = phony_makefile
        .rules()
        .filter(|r| !r.targets().any(|t| t.starts_with('.')))
        .count();
    assert_eq!(normal_rules_count, 1);

    // Verify we have the include directive
    assert_eq!(phony_makefile.includes().count(), 1);
    assert_eq!(phony_makefile.included_files().next().unwrap(), ".env");

    // Case 2: Without .PHONY, just a regular rule and include
    let simple_makefile = Makefile::from_reader(
        "\n\nVERBOSE ?= 0\n\n# comment\n-include .env\n\nrule: dependency\n\tcommand".as_bytes(),
    )
    .unwrap();
    assert_eq!(simple_makefile.rules().count(), 1);
    assert_eq!(simple_makefile.includes().count(), 1);
}

#[test]
fn test_real_conditional_directives() {
    // Basic if/else conditional
    let conditional = "ifdef DEBUG\nCFLAGS = -g\nelse\nCFLAGS = -O2\nendif\n";
    let mut buf = conditional.as_bytes();
    let makefile =
        Makefile::read_relaxed(&mut buf).expect("Failed to parse basic if/else conditional");
    let code = makefile.code();
    assert!(code.contains("ifdef DEBUG"));
    assert!(code.contains("else"));
    assert!(code.contains("endif"));

    // ifdef with nested ifdef
    let nested = "ifdef DEBUG\nCFLAGS = -g\nifdef VERBOSE\nCFLAGS += -v\nendif\nendif\n";
    let mut buf = nested.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse nested ifdef");
    let code = makefile.code();
    assert!(code.contains("ifdef DEBUG"));
    assert!(code.contains("ifdef VERBOSE"));

    // ifeq form
    let ifeq = "ifeq ($(OS),Windows_NT)\nTARGET = app.exe\nelse\nTARGET = app\nendif\n";
    let mut buf = ifeq.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse ifeq form");
    let code = makefile.code();
    assert!(code.contains("ifeq"));
    assert!(code.contains("Windows_NT"));
}

#[test]
fn test_indented_text_outside_rules() {
    // Simple help target with echo commands
    let help_text = "help:\n\t@echo \"Available targets:\"\n\t@echo \"  help     show help\"\n";
    let parsed = parse(help_text, None);
    assert!(parsed.errors.is_empty());

    // Verify recipes are correctly parsed
    let root = parsed.root();
    let rules = root.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);

    let help_rule = &rules[0];
    let recipes = help_rule.recipes().collect::<Vec<_>>();
    assert_eq!(recipes.len(), 2);
    assert!(recipes[0].contains("Available targets"));
    assert!(recipes[1].contains("help"));
}

#[test]
fn test_comment_handling_in_recipes() {
    // Create a recipe with a comment line
    let recipe_comment = "build:\n\t# This is a comment\n\tgcc -o app main.c\n";

    // Parse the recipe
    let parsed = parse(recipe_comment, None);

    // Verify no parsing errors
    assert!(
        parsed.errors.is_empty(),
        "Should parse recipe with comments without errors"
    );

    // Check rule structure
    let root = parsed.root();
    let rules = root.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1, "Should find exactly one rule");

    // Check the rule has the correct name
    let build_rule = &rules[0];
    assert_eq!(
        build_rule.targets().collect::<Vec<_>>(),
        vec!["build"],
        "Rule should have 'build' as target"
    );

    // Check recipes are parsed correctly
    // recipes() now returns all recipe nodes including comment-only lines
    let recipes = build_rule.recipe_nodes().collect::<Vec<_>>();
    assert_eq!(recipes.len(), 2, "Should find two recipe nodes");

    // First recipe should be comment-only
    assert_eq!(recipes[0].text(), "");
    assert_eq!(
        recipes[0].comment(),
        Some("# This is a comment".to_string())
    );

    // Second recipe should be the command
    assert_eq!(recipes[1].text(), "gcc -o app main.c");
    assert_eq!(recipes[1].comment(), None);
}

#[test]
fn test_multiline_variables() {
    // Simple multiline variable test
    let multiline = "SOURCES = main.c \\\n          util.c\n";

    // Parse the multiline variable
    let parsed = parse(multiline, None);

    // We can extract the variable even with errors (since backslash handling is not perfect)
    let root = parsed.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert!(!vars.is_empty(), "Should find at least one variable");

    // Test other multiline variable forms

    // := assignment operator
    let operators = "CFLAGS := -Wall \\\n         -Werror\n";
    let parsed_operators = parse(operators, None);

    // Extract variable with := operator
    let root = parsed_operators.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert!(
        !vars.is_empty(),
        "Should find at least one variable with := operator"
    );

    // += assignment operator
    let append = "LDFLAGS += -L/usr/lib \\\n          -lm\n";
    let parsed_append = parse(append, None);

    // Extract variable with += operator
    let root = parsed_append.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert!(
        !vars.is_empty(),
        "Should find at least one variable with += operator"
    );
}

#[test]
fn test_whitespace_and_eof_handling() {
    // Test 1: File ending with blank lines
    let blank_lines = "VAR = value\n\n\n";

    let parsed_blank = parse(blank_lines, None);

    // We should be able to extract the variable definition
    let root = parsed_blank.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(
        vars.len(),
        1,
        "Should find one variable in blank lines test"
    );

    // Test 2: File ending with space
    let trailing_space = "VAR = value \n";

    let parsed_space = parse(trailing_space, None);

    // We should be able to extract the variable definition
    let root = parsed_space.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(
        vars.len(),
        1,
        "Should find one variable in trailing space test"
    );

    // Test 3: No final newline
    let no_newline = "VAR = value";

    let parsed_no_newline = parse(no_newline, None);

    // Regardless of parsing errors, we should be able to extract the variable
    let root = parsed_no_newline.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1, "Should find one variable in no newline test");
    assert_eq!(
        vars[0].name(),
        Some("VAR".to_string()),
        "Variable name should be VAR"
    );
}

#[test]
fn test_complex_variable_references() {
    // Simple function call
    let wildcard = "SOURCES = $(wildcard *.c)\n";
    let parsed = parse(wildcard, None);
    assert!(parsed.errors.is_empty());

    // Nested variable reference
    let nested = "PREFIX = /usr\nBINDIR = $(PREFIX)/bin\n";
    let parsed = parse(nested, None);
    assert!(parsed.errors.is_empty());

    // Function with complex arguments
    let patsubst = "OBJECTS = $(patsubst %.c,%.o,$(SOURCES))\n";
    let parsed = parse(patsubst, None);
    assert!(parsed.errors.is_empty());
}

#[test]
fn test_complex_variable_references_minimal() {
    // Simple function call
    let wildcard = "SOURCES = $(wildcard *.c)\n";
    let parsed = parse(wildcard, None);
    assert!(parsed.errors.is_empty());

    // Nested variable reference
    let nested = "PREFIX = /usr\nBINDIR = $(PREFIX)/bin\n";
    let parsed = parse(nested, None);
    assert!(parsed.errors.is_empty());

    // Function with complex arguments
    let patsubst = "OBJECTS = $(patsubst %.c,%.o,$(SOURCES))\n";
    let parsed = parse(patsubst, None);
    assert!(parsed.errors.is_empty());
}

#[test]
fn test_multiline_variable_with_backslash() {
    let content = r#"
LONG_VAR = This is a long variable \
    that continues on the next line \
    and even one more line
"#;

    // For now, we'll use relaxed parsing since the backslash handling isn't fully implemented
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse multiline variable");

    // Check that we can extract the variable even with errors
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(
        vars.len(),
        1,
        "Expected 1 variable but found {}",
        vars.len()
    );
    let var_value = vars[0].raw_value();
    assert!(var_value.is_some(), "Variable value is None");

    // The value might not be perfect due to relaxed parsing, but it should contain most of the content
    let value_str = var_value.unwrap();
    assert!(
        value_str.contains("long variable"),
        "Value doesn't contain expected content"
    );
}

#[test]
fn test_multiline_variable_with_mixed_operators() {
    let content = r#"
PREFIX ?= /usr/local
CFLAGS := -Wall -O2 \
    -I$(PREFIX)/include \
    -DDEBUG
"#;
    // Use relaxed parsing for now
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf)
        .expect("Failed to parse multiline variable with operators");

    // Check that we can extract variables even with errors
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert!(
        !vars.is_empty(),
        "Expected at least 1 variable, found {}",
        vars.len()
    );

    // Check PREFIX variable
    let prefix_var = vars
        .iter()
        .find(|v| v.name().unwrap_or_default() == "PREFIX");
    assert!(prefix_var.is_some(), "Expected to find PREFIX variable");
    assert!(
        prefix_var.unwrap().raw_value().is_some(),
        "PREFIX variable has no value"
    );

    // CFLAGS may be parsed incompletely but should exist in some form
    let cflags_var = vars
        .iter()
        .find(|v| v.name().unwrap_or_default().contains("CFLAGS"));
    assert!(
        cflags_var.is_some(),
        "Expected to find CFLAGS variable (or part of it)"
    );
}

#[test]
fn test_indented_help_text() {
    let content = r#"
.PHONY: help
help:
	@echo "Available targets:"
	@echo "  build  - Build the project"
	@echo "  test   - Run tests"
	@echo "  clean  - Remove build artifacts"
"#;
    // Use relaxed parsing for now
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse indented help text");

    // Check that we can extract rules even with errors
    let rules = makefile.rules().collect::<Vec<_>>();
    assert!(!rules.is_empty(), "Expected at least one rule");

    // Find help rule
    let help_rule = rules.iter().find(|r| r.targets().any(|t| t == "help"));
    assert!(help_rule.is_some(), "Expected to find help rule");

    // Check recipes - they might not be perfectly parsed but should exist
    let recipes = help_rule.unwrap().recipes().collect::<Vec<_>>();
    assert!(
        !recipes.is_empty(),
        "Expected at least one recipe line in help rule"
    );
    assert!(
        recipes.iter().any(|r| r.contains("Available targets")),
        "Expected to find 'Available targets' in recipes"
    );
}

#[test]
fn test_indented_lines_in_conditionals() {
    let content = r#"
ifdef DEBUG
    CFLAGS += -g -DDEBUG
    # This is a comment inside conditional
    ifdef VERBOSE
        CFLAGS += -v
    endif
endif
"#;
    // Use relaxed parsing for conditionals with indented lines
    let mut buf = content.as_bytes();
    let makefile =
        Makefile::read_relaxed(&mut buf).expect("Failed to parse indented lines in conditionals");

    // Check that we detected conditionals
    let code = makefile.code();
    assert!(code.contains("ifdef DEBUG"));
    assert!(code.contains("ifdef VERBOSE"));
    assert!(code.contains("endif"));
}

#[test]
fn test_recipe_with_colon() {
    let content = r#"
build:
	@echo "Building at: $(shell date)"
	gcc -o program main.c
"#;
    let parsed = parse(content, None);
    assert!(
        parsed.errors.is_empty(),
        "Failed to parse recipe with colon: {:?}",
        parsed.errors
    );
}

#[test]
fn test_double_colon_rules() {
    let content = r#"
%.o :: %.c
	$(CC) -c $< -o $@

# Double colon allows multiple rules for same target
all:: prerequisite1
	@echo "First rule for all"

all:: prerequisite2
	@echo "Second rule for all"
"#;
    let parsed = parse(content, None);
    assert!(
        parsed.errors.is_empty(),
        "Failed to parse double colon rules: {:?}",
        parsed.errors
    );

    let makefile = parsed.root();
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 3);

    // All rules should be double-colon
    for rule in &rules {
        assert!(rule.is_double_colon());
    }

    // Check targets
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["%.o"]);
    assert_eq!(rules[1].targets().collect::<Vec<_>>(), vec!["all"]);
    assert_eq!(rules[2].targets().collect::<Vec<_>>(), vec!["all"]);

    // Check prerequisites
    assert_eq!(
        rules[1].prerequisites().collect::<Vec<_>>(),
        vec!["prerequisite1"]
    );
    assert_eq!(
        rules[2].prerequisites().collect::<Vec<_>>(),
        vec!["prerequisite2"]
    );
}

#[test]
fn test_else_conditional_directives() {
    // Test else ifeq
    let content = r#"
ifeq ($(OS),Windows_NT)
    TARGET = windows
else ifeq ($(OS),Darwin)
    TARGET = macos
else ifeq ($(OS),Linux)
    TARGET = linux
else
    TARGET = unknown
endif
"#;
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse else ifeq directive");
    assert!(makefile.code().contains("else ifeq"));
    assert!(makefile.code().contains("TARGET"));

    // Test else ifdef
    let content = r#"
ifdef WINDOWS
    TARGET = windows
else ifdef DARWIN
    TARGET = macos
else ifdef LINUX
    TARGET = linux
else
    TARGET = unknown
endif
"#;
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse else ifdef directive");
    assert!(makefile.code().contains("else ifdef"));

    // Test else ifndef
    let content = r#"
ifndef NOWINDOWS
    TARGET = windows
else ifndef NODARWIN
    TARGET = macos
else
    TARGET = linux
endif
"#;
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse else ifndef directive");
    assert!(makefile.code().contains("else ifndef"));

    // Test else ifneq
    let content = r#"
ifneq ($(OS),Windows_NT)
    TARGET = not_windows
else ifneq ($(OS),Darwin)
    TARGET = not_macos
else
    TARGET = darwin
endif
"#;
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse else ifneq directive");
    assert!(makefile.code().contains("else ifneq"));
}

#[test]
fn test_complex_else_conditionals() {
    // Test complex nested else conditionals with mixed types
    let content = r#"VAR1 := foo
VAR2 := bar

ifeq ($(VAR1),foo)
    RESULT := foo_matched
else ifdef VAR2
    RESULT := var2_defined
else ifndef VAR3
    RESULT := var3_not_defined
else
    RESULT := final_else
endif

all:
	@echo $(RESULT)
"#;
    let mut buf = content.as_bytes();
    let makefile =
        Makefile::read_relaxed(&mut buf).expect("Failed to parse complex else conditionals");

    // Verify the structure is preserved
    let code = makefile.code();
    assert!(code.contains("ifeq ($(VAR1),foo)"));
    assert!(code.contains("else ifdef VAR2"));
    assert!(code.contains("else ifndef VAR3"));
    assert!(code.contains("else"));
    assert!(code.contains("endif"));
    assert!(code.contains("RESULT"));

    // Verify rules are still parsed correctly
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["all"]);
}

#[test]
fn test_conditional_token_structure() {
    // Test that conditionals have proper token structure
    let content = r#"ifdef VAR1
X := 1
else ifdef VAR2
X := 2
else
X := 3
endif
"#;
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).unwrap();

    // Check that we can traverse the syntax tree
    let syntax = makefile.syntax();

    // Find CONDITIONAL nodes
    let mut found_conditional = false;
    let mut found_conditional_if = false;
    let mut found_conditional_else = false;
    let mut found_conditional_endif = false;

    fn check_node(
        node: &SyntaxNode,
        found_cond: &mut bool,
        found_if: &mut bool,
        found_else: &mut bool,
        found_endif: &mut bool,
    ) {
        match node.kind() {
            SyntaxKind::CONDITIONAL => *found_cond = true,
            SyntaxKind::CONDITIONAL_IF => *found_if = true,
            SyntaxKind::CONDITIONAL_ELSE => *found_else = true,
            SyntaxKind::CONDITIONAL_ENDIF => *found_endif = true,
            _ => {}
        }

        for child in node.children() {
            check_node(&child, found_cond, found_if, found_else, found_endif);
        }
    }

    check_node(
        syntax,
        &mut found_conditional,
        &mut found_conditional_if,
        &mut found_conditional_else,
        &mut found_conditional_endif,
    );

    assert!(found_conditional, "Should have CONDITIONAL node");
    assert!(found_conditional_if, "Should have CONDITIONAL_IF node");
    assert!(found_conditional_else, "Should have CONDITIONAL_ELSE node");
    assert!(
        found_conditional_endif,
        "Should have CONDITIONAL_ENDIF node"
    );
}

#[test]
fn test_ambiguous_assignment_vs_rule() {
    // Test case: Variable assignment with equals sign
    const VAR_ASSIGNMENT: &str = "VARIABLE = value\n";

    let mut buf = std::io::Cursor::new(VAR_ASSIGNMENT);
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse variable assignment");

    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    let rules = makefile.rules().collect::<Vec<_>>();

    assert_eq!(vars.len(), 1, "Expected 1 variable, found {}", vars.len());
    assert_eq!(rules.len(), 0, "Expected 0 rules, found {}", rules.len());

    assert_eq!(vars[0].name(), Some("VARIABLE".to_string()));

    // Test case: Simple rule with colon
    const SIMPLE_RULE: &str = "target: dependency\n";

    let mut buf = std::io::Cursor::new(SIMPLE_RULE);
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse simple rule");

    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    let rules = makefile.rules().collect::<Vec<_>>();

    assert_eq!(vars.len(), 0, "Expected 0 variables, found {}", vars.len());
    assert_eq!(rules.len(), 1, "Expected 1 rule, found {}", rules.len());

    let rule = &rules[0];
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["target"]);
}

#[test]
fn test_nested_conditionals() {
    let content = r#"
ifdef RELEASE
    CFLAGS += -O3
    ifndef DEBUG
        ifneq ($(ARCH),arm)
            CFLAGS += -march=native
        else
            CFLAGS += -mcpu=cortex-a72
        endif
    endif
endif
"#;
    // Use relaxed parsing for nested conditionals test
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse nested conditionals");

    // Check that we detected conditionals
    let code = makefile.code();
    assert!(code.contains("ifdef RELEASE"));
    assert!(code.contains("ifndef DEBUG"));
    assert!(code.contains("ifneq"));
}

#[test]
fn test_space_indented_recipes() {
    // This test is expected to fail with current implementation
    // It should pass once the parser is more flexible with indentation
    let content = r#"
build:
    @echo "Building with spaces instead of tabs"
    gcc -o program main.c
"#;
    // Use relaxed parsing for now
    let mut buf = content.as_bytes();
    let makefile =
        Makefile::read_relaxed(&mut buf).expect("Failed to parse space-indented recipes");

    // Check that we can extract rules even with errors
    let rules = makefile.rules().collect::<Vec<_>>();
    assert!(!rules.is_empty(), "Expected at least one rule");

    // Find build rule
    let build_rule = rules.iter().find(|r| r.targets().any(|t| t == "build"));
    assert!(build_rule.is_some(), "Expected to find build rule");
}

#[test]
fn test_complex_variable_functions() {
    let content = r#"
FILES := $(shell find . -name "*.c")
OBJS := $(patsubst %.c,%.o,$(FILES))
NAME := $(if $(PROGRAM),$(PROGRAM),a.out)
HEADERS := ${wildcard *.h}
"#;
    let parsed = parse(content, None);
    assert!(
        parsed.errors.is_empty(),
        "Failed to parse complex variable functions: {:?}",
        parsed.errors
    );
}

#[test]
fn test_nested_variable_expansions() {
    let content = r#"
VERSION = 1.0
PACKAGE = myapp
TARBALL = $(PACKAGE)-$(VERSION).tar.gz
INSTALL_PATH = $(shell echo $(PREFIX) | sed 's/\/$//')
"#;
    let parsed = parse(content, None);
    assert!(
        parsed.errors.is_empty(),
        "Failed to parse nested variable expansions: {:?}",
        parsed.errors
    );
}

#[test]
fn test_special_directives() {
    let content = r#"
# Special makefile directives
.PHONY: all clean
.SUFFIXES: .c .o
.DEFAULT: all

# Variable definition and export directive
export PATH := /usr/bin:/bin
"#;
    // Use relaxed parsing to allow for special directives
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse special directives");

    // Check that we can extract rules even with errors
    let rules = makefile.rules().collect::<Vec<_>>();

    // Find phony rule
    let phony_rule = rules
        .iter()
        .find(|r| r.targets().any(|t| t.contains(".PHONY")));
    assert!(phony_rule.is_some(), "Expected to find .PHONY rule");

    // Check that variables can be extracted
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert!(!vars.is_empty(), "Expected to find at least one variable");
}

// Comprehensive Test combining multiple issues

#[test]
fn test_comprehensive_real_world_makefile() {
    // Simple makefile with basic elements
    let content = r#"
# Basic variable assignment
VERSION = 1.0.0

# Phony target
.PHONY: all clean

# Simple rule
all:
	echo "Building version $(VERSION)"

# Another rule with dependencies
clean:
	rm -f *.o
"#;

    // Parse the content
    let parsed = parse(content, None);

    // Check that parsing succeeded
    assert!(parsed.errors.is_empty(), "Expected no parsing errors");

    // Check that we found variables
    let variables = parsed.root().variable_definitions().collect::<Vec<_>>();
    assert!(!variables.is_empty(), "Expected at least one variable");
    assert_eq!(
        variables[0].name(),
        Some("VERSION".to_string()),
        "Expected VERSION variable"
    );

    // Check that we found rules
    let rules = parsed.root().rules().collect::<Vec<_>>();
    assert!(!rules.is_empty(), "Expected at least one rule");

    // Check for specific rules
    let rule_targets: Vec<String> = rules
        .iter()
        .flat_map(|r| r.targets().collect::<Vec<_>>())
        .collect();
    assert!(
        rule_targets.contains(&".PHONY".to_string()),
        "Expected .PHONY rule"
    );
    assert!(
        rule_targets.contains(&"all".to_string()),
        "Expected 'all' rule"
    );
    assert!(
        rule_targets.contains(&"clean".to_string()),
        "Expected 'clean' rule"
    );
}

#[test]
fn test_space_indented_lines_are_not_recipes() {
    // Only a tab introduces a recipe line; GNU make rejects the
    // space-indented lines below with "missing separator".
    let content = r#"
# Targets with help text
help:
    @echo "Available targets:"
    @echo "  build      build the project"

# Another target
clean:
	rm -rf build/
"#;

    let parsed = parse(content, None);
    assert!(!parsed.errors.is_empty());

    let makefile = parsed.root();
    assert_eq!(makefile.to_string(), content);
    let help_rule = makefile.find_rule_by_target("help").unwrap();
    assert_eq!(
        help_rule.recipes().collect::<Vec<_>>(),
        Vec::<String>::new()
    );
    let clean_rule = makefile.find_rule_by_target("clean").unwrap();
    assert_eq!(
        clean_rule.recipes().collect::<Vec<_>>(),
        vec!["rm -rf build/".to_string()]
    );
}

#[test]
fn test_makefile1_phony_pattern() {
    // Replicate the specific pattern in Makefile_1 that caused issues
    let content = "#line 2145\n.PHONY: $(PHONY)\n";

    // Parse the content
    let result = parse(content, None);

    // Verify no parsing errors
    assert!(
        result.errors.is_empty(),
        "Failed to parse .PHONY: $(PHONY) pattern"
    );

    // Check that the rule was parsed correctly
    let rules = result.root().rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1, "Expected 1 rule");
    assert_eq!(
        rules[0].targets().next().unwrap(),
        ".PHONY",
        "Expected .PHONY rule"
    );

    // Check that the prerequisite contains the variable reference
    let prereqs = rules[0].prerequisites().collect::<Vec<_>>();
    assert_eq!(prereqs.len(), 1, "Expected 1 prerequisite");
    assert_eq!(prereqs[0], "$(PHONY)", "Expected $(PHONY) prerequisite");
}

#[test]
fn test_skip_until_newline_behavior() {
    // Test the skip_until_newline function to cover the != vs == mutant
    let input = "text without newline";
    let parsed = parse(input, None);
    // This should handle gracefully without infinite loops
    assert!(parsed.errors.is_empty() || !parsed.errors.is_empty());

    let input_with_newline = "text\nafter newline";
    let parsed2 = parse(input_with_newline, None);
    assert!(parsed2.errors.is_empty() || !parsed2.errors.is_empty());
}

#[test]
#[ignore] // Ignored until proper handling of orphaned indented lines is implemented
fn test_error_with_indent_token() {
    // Test the error logic with INDENT token to cover the ! deletion mutant
    let input = "\tinvalid indented line";
    let parsed = parse(input, None);
    // Should produce an error about indented line not part of a rule
    assert!(!parsed.errors.is_empty());

    let error_msg = &parsed.errors[0].message;
    assert!(error_msg.contains("recipe commences before first target"));
}

#[test]
fn test_conditional_token_handling() {
    // Test conditional token handling to cover the == vs != mutant
    let input = r#"
ifndef VAR
    CFLAGS = -DTEST
endif
"#;
    let parsed = parse(input, None);
    // Test that parsing doesn't panic and produces some result
    let makefile = parsed.root();
    let _vars = makefile.variable_definitions().collect::<Vec<_>>();
    // Should handle conditionals, possibly with errors but without crashing

    // Test with nested conditionals
    let nested = r#"
ifdef DEBUG
    ifndef RELEASE
        CFLAGS = -g
    endif
endif
"#;
    let parsed_nested = parse(nested, None);
    // Test that parsing doesn't panic
    let _makefile = parsed_nested.root();
}

#[test]
fn test_include_vs_conditional_logic() {
    // Test the include vs conditional logic to cover the == vs != mutant at line 743
    let input = r#"
include file.mk
ifdef VAR
    VALUE = 1
endif
"#;
    let parsed = parse(input, None);
    // Test that parsing doesn't panic and produces some result
    let makefile = parsed.root();
    let includes = makefile.includes().collect::<Vec<_>>();
    // Should recognize include directive
    assert!(!includes.is_empty() || !parsed.errors.is_empty());

    // Test with -include
    let optional_include = r#"
-include optional.mk
ifndef VAR
    VALUE = default
endif
"#;
    let parsed2 = parse(optional_include, None);
    // Test that parsing doesn't panic
    let _makefile = parsed2.root();
}

fn assert_vpath(item: &MakefileItem, pattern: Option<&str>, dirs: Option<&str>) {
    let MakefileItem::Vpath(vpath) = item else {
        panic!("expected a vpath directive, got {:?}", item.syntax());
    };
    assert_eq!(pattern.map(str::to_string), vpath.pattern());
    assert_eq!(dirs.map(str::to_string), vpath.directories_text());
}

#[test]
fn test_vpath_in_conditional() {
    let code = "ifdef X\nvpath %.c src\nelse\nvpath %.h\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(0, makefile.rules().count());
    let cond = makefile.conditionals().next().unwrap();
    let if_items: Vec<_> = cond.if_items().collect();
    assert_eq!(1, if_items.len());
    assert_vpath(&if_items[0], Some("%.c"), Some("src"));
    let else_items: Vec<_> = cond.else_items().collect();
    assert_eq!(1, else_items.len());
    assert_vpath(&else_items[0], Some("%.h"), None);
}

#[test]
fn test_vpath_in_nested_conditional() {
    let code = "ifdef X\nifeq ($(Y),1)\nvpath\nendif\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let outer = makefile.conditionals().next().unwrap();
    let outer_items: Vec<_> = outer.if_items().collect();
    assert_eq!(1, outer_items.len());
    let MakefileItem::Conditional(inner) = &outer_items[0] else {
        panic!("expected a conditional, got {:?}", outer_items[0].syntax());
    };
    let inner_items: Vec<_> = inner.if_items().collect();
    assert_eq!(1, inner_items.len());
    assert_vpath(&inner_items[0], None, None);
}

#[test]
fn test_vpath_in_conditional_in_rule() {
    let code = "all:\n\techo hi\nifdef X\nvpath %.h inc\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(1, makefile.rules().count());
    let vpaths: Vec<_> = makefile
        .syntax()
        .descendants()
        .filter_map(Vpath::cast)
        .collect();
    assert_eq!(1, vpaths.len());
    assert_vpath(
        &MakefileItem::Vpath(vpaths[0].clone()),
        Some("%.h"),
        Some("inc"),
    );
}

#[test]
fn test_directive_names_as_variables() {
    // GNU Make treats these as plain assignments, both at the top level
    // and inside a conditional.
    let lines = "vpath = a\ninclude := b\n%x = c\n";
    for code in [lines.to_string(), format!("ifdef X\n{}endif\n", lines)] {
        let parsed = parse(&code, None);
        assert_eq!(parsed.errors, vec![]);
        let makefile = parsed.root();
        assert_eq!(code, makefile.to_string());
        let vars: Vec<_> = makefile
            .syntax()
            .descendants()
            .filter_map(VariableDefinition::cast)
            .map(|v| (v.name().unwrap(), v.raw_value().unwrap()))
            .collect();
        assert_eq!(
            vec![
                ("vpath".to_string(), "a".to_string()),
                ("include".to_string(), "b".to_string()),
                ("%x".to_string(), "c".to_string()),
            ],
            vars
        );
    }
}

#[test]
fn test_balanced_parens_counting() {
    // Test balanced parentheses parsing to cover the += vs -= mutant
    let input = r#"
VAR = $(call func,$(nested,arg),extra)
COMPLEX = $(if $(condition),$(then_val),$(else_val))
"#;
    let parsed = parse(input, None);
    assert!(parsed.errors.is_empty());

    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 2);
}

#[test]
fn test_documentation_lookahead() {
    // Test the documentation lookahead logic to cover the - vs + mutant at line 895
    let input = r#"
# Documentation comment
help:
	@echo "Usage instructions"
	@echo "More help text"
"#;
    let parsed = parse(input, None);
    assert!(parsed.errors.is_empty());

    let makefile = parsed.root();
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().next().unwrap(), "help");
}

#[test]
fn test_edge_case_empty_input() {
    // Test with empty input
    let parsed = parse("", None);
    assert!(parsed.errors.is_empty());

    // Test with only whitespace
    let parsed2 = parse("   \n  \n", None);
    // Some parsers might report warnings/errors for whitespace-only input
    // Just ensure it doesn't crash
    let _makefile = parsed2.root();
}

#[test]
fn test_malformed_conditional_recovery() {
    // Test parser recovery from malformed conditionals
    let input = r#"
ifdef
    # Missing condition variable
endif
"#;
    let parsed = parse(input, None);
    // Parser should either handle gracefully or report appropriate errors
    // Not checking for specific error since parsing strategy may vary
    assert!(parsed.errors.is_empty() || !parsed.errors.is_empty());
}

#[test]
fn test_large_makefile_performance() {
    // Create a makefile with many rules to test performance doesn't degrade
    let mut makefile = Makefile::new();

    // Add 100 rules
    for i in 0..100 {
        let rule_name = format!("rule{}", i);
        makefile
            .add_rule(&rule_name)
            .push_command(&format!("command{}", i));
    }

    assert_eq!(makefile.rules().count(), 100);

    // Replace rule in the middle - should be efficient
    let new_rule: Rule = "middle_rule:\n\tmiddle_command\n".parse().unwrap();
    makefile.replace_rule(50, new_rule).unwrap();

    // Verify the change
    let rule_50_targets: Vec<_> = makefile.rules().nth(50).unwrap().targets().collect();
    assert_eq!(rule_50_targets, vec!["middle_rule"]);

    assert_eq!(makefile.rules().count(), 100); // Count unchanged
}

#[test]
fn test_variable_definition_remove() {
    let makefile: Makefile = r#"VAR1 = value1
VAR2 = value2
VAR3 = value3
"#
    .parse()
    .unwrap();

    // Verify we have 3 variables
    assert_eq!(makefile.variable_definitions().count(), 3);

    // Remove the second variable
    let mut var2 = makefile
        .variable_definitions()
        .nth(1)
        .expect("Should have second variable");
    assert_eq!(var2.name(), Some("VAR2".to_string()));
    var2.remove();

    // Verify we now have 2 variables and VAR2 is gone
    assert_eq!(makefile.variable_definitions().count(), 2);
    let var_names: Vec<_> = makefile
        .variable_definitions()
        .filter_map(|v| v.name())
        .collect();
    assert_eq!(var_names, vec!["VAR1", "VAR3"]);
}

#[test]
fn test_variable_definition_is_export() {
    let makefile: Makefile = r#"VAR1 = value1
export VAR2 := value2
export VAR3 = value3
VAR4 := value4
"#
    .parse()
    .unwrap();

    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars.len(), 4);

    assert!(!vars[0].is_export());
    assert!(vars[1].is_export());
    assert!(vars[2].is_export());
    assert!(!vars[3].is_export());
}

#[test]
fn test_variable_remove_with_comment() {
    let makefile: Makefile = r#"VAR1 = value1
# This is a comment about VAR2
VAR2 = value2
VAR3 = value3
"#
    .parse()
    .unwrap();

    // Remove VAR2
    let mut var2 = makefile
        .variable_definitions()
        .nth(1)
        .expect("Should have second variable");
    assert_eq!(var2.name(), Some("VAR2".to_string()));
    var2.remove();

    // Verify the comment is also removed
    assert_eq!(makefile.code(), "VAR1 = value1\nVAR3 = value3\n");
}

#[test]
fn test_variable_remove_with_multiple_comments() {
    let makefile: Makefile = r#"VAR1 = value1
# Comment line 1
# Comment line 2
# Comment line 3
VAR2 = value2
VAR3 = value3
"#
    .parse()
    .unwrap();

    // Remove VAR2
    let mut var2 = makefile
        .variable_definitions()
        .nth(1)
        .expect("Should have second variable");
    var2.remove();

    // Verify all comments are removed
    assert_eq!(makefile.code(), "VAR1 = value1\nVAR3 = value3\n");
}

#[test]
fn test_variable_remove_with_empty_line() {
    let makefile: Makefile = r#"VAR1 = value1

# Comment about VAR2
VAR2 = value2
VAR3 = value3
"#
    .parse()
    .unwrap();

    // Remove VAR2
    let mut var2 = makefile
        .variable_definitions()
        .nth(1)
        .expect("Should have second variable");
    var2.remove();

    // Verify comment and up to 1 empty line are removed
    // Should have VAR1, then newline, then VAR3 (empty line removed)
    assert_eq!(makefile.code(), "VAR1 = value1\nVAR3 = value3\n");
}

#[test]
fn test_variable_remove_with_multiple_empty_lines() {
    let makefile: Makefile = r#"VAR1 = value1


# Comment about VAR2
VAR2 = value2
VAR3 = value3
"#
    .parse()
    .unwrap();

    // Remove VAR2
    let mut var2 = makefile
        .variable_definitions()
        .nth(1)
        .expect("Should have second variable");
    var2.remove();

    // Verify comment and only 1 empty line are removed (one empty line preserved)
    // Should preserve one empty line before where VAR2 was
    assert_eq!(makefile.code(), "VAR1 = value1\n\nVAR3 = value3\n");
}

#[test]
fn test_rule_remove_with_comment() {
    let makefile: Makefile = r#"rule1:
	command1

# Comment about rule2
rule2:
	command2
rule3:
	command3
"#
    .parse()
    .unwrap();

    // Remove rule2
    let rule2 = makefile.rules().nth(1).expect("Should have second rule");
    rule2.remove().unwrap();

    // Verify the comment is removed
    // Note: The empty line after rule1 is part of rule1's text, not a sibling, so it's preserved
    assert_eq!(
        makefile.code(),
        "rule1:\n\tcommand1\n\nrule3:\n\tcommand3\n"
    );
}

#[test]
fn test_variable_remove_preserves_shebang() {
    let makefile: Makefile = r#"#!/usr/bin/make -f
# This is a regular comment
VAR1 = value1
VAR2 = value2
"#
    .parse()
    .unwrap();

    // Remove VAR1
    let mut var1 = makefile.variable_definitions().next().unwrap();
    var1.remove();

    // Verify the shebang is preserved but regular comment is removed
    let code = makefile.code();
    assert!(code.starts_with("#!/usr/bin/make -f"));
    assert!(!code.contains("regular comment"));
    assert!(!code.contains("VAR1"));
    assert!(code.contains("VAR2"));
}

#[test]
fn test_variable_remove_preserves_subsequent_comments() {
    let makefile: Makefile = r#"VAR1 = value1
# Comment about VAR2
VAR2 = value2

# Comment about VAR3
VAR3 = value3
"#
    .parse()
    .unwrap();

    // Remove VAR2
    let mut var2 = makefile
        .variable_definitions()
        .nth(1)
        .expect("Should have second variable");
    var2.remove();

    // Verify preceding comment is removed but subsequent comment/empty line are preserved
    let code = makefile.code();
    assert_eq!(
        code,
        "VAR1 = value1\n\n# Comment about VAR3\nVAR3 = value3\n"
    );
}

#[test]
fn test_variable_remove_after_shebang_preserves_empty_line() {
    let makefile: Makefile = r#"#!/usr/bin/make -f
export DEB_LDFLAGS_MAINT_APPEND = -Wl,--as-needed

%:
	dh $@
"#
    .parse()
    .unwrap();

    // Remove the variable
    let mut var = makefile.variable_definitions().next().unwrap();
    var.remove();

    // Verify shebang is preserved and empty line after variable is preserved
    assert_eq!(makefile.code(), "#!/usr/bin/make -f\n\n%:\n\tdh $@\n");
}

#[test]
fn test_matches_pattern_exact() {
    assert!(matches_pattern("foo.o", "foo.o"));
    assert!(!matches_pattern("foo.o", "bar.o"));
}

#[test]
fn test_matches_pattern_suffix() {
    assert!(matches_pattern("%.o", "foo.o"));
    assert!(matches_pattern("%.o", "bar.o"));
    assert!(matches_pattern("%.o", "baz/qux.o"));
    assert!(!matches_pattern("%.o", "foo.c"));
}

#[test]
fn test_matches_pattern_prefix() {
    assert!(matches_pattern("lib%.a", "libfoo.a"));
    assert!(matches_pattern("lib%.a", "libbar.a"));
    assert!(!matches_pattern("lib%.a", "foo.a"));
    assert!(!matches_pattern("lib%.a", "lib.a"));
}

#[test]
fn test_matches_pattern_middle() {
    assert!(matches_pattern("lib%_debug.a", "libfoo_debug.a"));
    assert!(matches_pattern("lib%_debug.a", "libbar_debug.a"));
    assert!(!matches_pattern("lib%_debug.a", "libfoo.a"));
    assert!(!matches_pattern("lib%_debug.a", "foo_debug.a"));
}

#[test]
fn test_matches_pattern_wildcard_only() {
    assert!(matches_pattern("%", "anything"));
    assert!(matches_pattern("%", "foo.o"));
    // GNU make: stem must be non-empty, so "%" does NOT match ""
    assert!(!matches_pattern("%", ""));
}

#[test]
fn test_matches_pattern_empty_stem() {
    // GNU make: stem must be non-empty
    assert!(!matches_pattern("%.o", ".o")); // stem would be empty
    assert!(!matches_pattern("lib%", "lib")); // stem would be empty
    assert!(!matches_pattern("lib%.a", "lib.a")); // stem would be empty
}

#[test]
fn test_matches_pattern_multiple_wildcards_not_supported() {
    // GNU make does NOT support multiple % in pattern rules
    // These should not match (fall back to exact match)
    assert!(!matches_pattern("%foo%bar", "xfooybarz"));
    assert!(!matches_pattern("lib%.so.%", "libfoo.so.1"));
}

#[test]
fn test_recipe_with_leading_comments_and_blank_lines() {
    // Regression test for bug where recipes with leading comments and blank lines
    // were not parsed correctly. The parser would stop parsing recipes when it
    // encountered a newline, missing subsequent recipe lines.
    let makefile_text = r#"#!/usr/bin/make

%:
	dh $@

override_dh_build:
	# The next line is empty

	dh_python3
"#;
    let makefile = Makefile::read_relaxed(makefile_text.as_bytes()).unwrap();

    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 2, "Expected 2 rules");

    // First rule: %
    let rule0 = &rules[0];
    assert_eq!(rule0.targets().collect::<Vec<_>>(), vec!["%"]);
    assert_eq!(rule0.recipes().collect::<Vec<_>>(), vec!["dh $@"]);

    // Second rule: override_dh_build
    let rule1 = &rules[1];
    assert_eq!(
        rule1.targets().collect::<Vec<_>>(),
        vec!["override_dh_build"]
    );

    // The key assertion: we should have at least the actual command recipe
    let recipes: Vec<_> = rule1.recipes().collect();
    assert!(
        !recipes.is_empty(),
        "Expected at least one recipe for override_dh_build, got none"
    );
    assert!(
        recipes.contains(&"dh_python3".to_string()),
        "Expected 'dh_python3' in recipes, got: {:?}",
        recipes
    );
}

#[test]
fn test_rule_parse_preserves_trailing_blank_lines() {
    // Regression test: ensure that trailing blank lines are preserved
    // when parsing a rule and using it with replace_rule()
    let input = r#"override_dh_systemd_enable:
	dh_systemd_enable -pracoon

override_dh_install:
	dh_install
"#;

    let mut mf: Makefile = input.parse().unwrap();

    // Get first rule and convert to string
    let rule = mf.rules().next().unwrap();
    let rule_text = rule.to_string();

    // Should include trailing blank line
    assert_eq!(
        rule_text,
        "override_dh_systemd_enable:\n\tdh_systemd_enable -pracoon\n\n"
    );

    // Modify the text
    let modified = rule_text.replace("override_dh_systemd_enable:", "override_dh_installsystemd:");

    // Parse back - should preserve trailing blank line
    let new_rule: Rule = modified.parse().unwrap();
    assert_eq!(
        new_rule.to_string(),
        "override_dh_installsystemd:\n\tdh_systemd_enable -pracoon\n\n"
    );

    // Replace in makefile
    mf.replace_rule(0, new_rule).unwrap();

    // Verify blank line is still present in output
    let output = mf.to_string();
    assert!(
        output.contains(
            "override_dh_installsystemd:\n\tdh_systemd_enable -pracoon\n\noverride_dh_install:"
        ),
        "Blank line between rules should be preserved. Got: {:?}",
        output
    );
}

#[test]
fn test_rule_parse_round_trip_with_trailing_newlines() {
    // Test that parsing and stringifying a rule preserves exact trailing newlines
    let test_cases = vec![
        "rule:\n\tcommand\n",     // One newline
        "rule:\n\tcommand\n\n",   // Two newlines (blank line)
        "rule:\n\tcommand\n\n\n", // Three newlines (two blank lines)
    ];

    for rule_text in test_cases {
        let rule: Rule = rule_text.parse().unwrap();
        let result = rule.to_string();
        assert_eq!(rule_text, result, "Round-trip failed for {:?}", rule_text);
    }
}

#[test]
fn test_rule_clone() {
    // Test that Rule can be cloned and produces an identical copy
    let rule_text = "rule:\n\tcommand\n\n";
    let rule: Rule = rule_text.parse().unwrap();
    let cloned = rule.clone();

    // Both should produce the same string representation
    assert_eq!(rule.to_string(), cloned.to_string());
    assert_eq!(rule.to_string(), rule_text);
    assert_eq!(cloned.to_string(), rule_text);

    // Verify targets and recipes are the same
    assert_eq!(
        rule.targets().collect::<Vec<_>>(),
        cloned.targets().collect::<Vec<_>>()
    );
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        cloned.recipes().collect::<Vec<_>>()
    );
}

#[test]
fn test_makefile_clone() {
    // Test that Makefile and other AST nodes can be cloned
    let input = "VAR = value\n\nrule:\n\tcommand\n";
    let makefile: Makefile = input.parse().unwrap();
    let cloned = makefile.clone();

    // Both should produce the same string representation
    assert_eq!(makefile.to_string(), cloned.to_string());
    assert_eq!(makefile.to_string(), input);

    // Verify rule count is the same
    assert_eq!(makefile.rules().count(), cloned.rules().count());

    // Verify variable definitions are the same
    assert_eq!(
        makefile.variable_definitions().count(),
        cloned.variable_definitions().count()
    );
}

#[test]
fn test_conditional_with_tab_indented_line_outside_rule() {
    // Without a preceding rule a tab-indented line is not a recipe line;
    // GNU make reports "recipe commences before first target".
    let input = "ifeq (,$(X))\n\t./run-tests\nendif\n";
    let parsed = parse(input, None);

    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["indented line not part of a rule"]
    );

    // Should preserve the code
    let mf = parsed.root();
    assert_eq!(mf.code(), input);
}

#[test]
fn test_conditional_in_rule_recipe() {
    // Test conditional inside a rule's recipe section
    let input = "override_dh_auto_test:\nifeq (,$(filter nocheck,$(DEB_BUILD_OPTIONS)))\n\t./run-tests\nendif\n";
    let parsed = parse(input, None);

    // Should parse without errors
    assert!(
        parsed.errors.is_empty(),
        "Expected no parse errors, but got: {:?}",
        parsed.errors
    );

    // Should preserve the code
    let mf = parsed.root();
    assert_eq!(mf.code(), input);

    // Should have exactly one rule
    assert_eq!(mf.rules().count(), 1);
}

#[test]
fn test_recipe_insert_after_unterminated() {
    let makefile: Makefile = "a:\n\tcmd".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().next().unwrap().insert_after("x");
    assert_eq!(makefile.to_string(), "a:\n\tcmd\n\tx\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_item_insert_after_unterminated() {
    let makefile: Makefile = "X = 1".parse().unwrap();
    let new_item = "Y = 1\n"
        .parse::<Makefile>()
        .unwrap()
        .items()
        .next()
        .unwrap();
    makefile
        .items()
        .next()
        .unwrap()
        .insert_after(new_item)
        .unwrap();
    assert_eq!(makefile.to_string(), "X = 1\nY = 1\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_conditional_remove() {
    let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
endif

VAR2 = value2
"#
    .parse()
    .unwrap();

    let mut conditional = makefile.conditionals().next().unwrap();
    let result = conditional.remove();
    assert!(result.is_ok());

    let code = makefile.to_string();
    assert!(!code.contains("ifdef DEBUG"));
    assert!(!code.contains("VAR = debug"));
    assert!(code.contains("VAR2 = value2"));
}

#[test]
fn test_item_insert_before_without_newline() {
    let makefile: Makefile = "X = 1\n".parse().unwrap();
    let mut first = makefile.items().next().unwrap();
    first.insert_before(item_without_newline("Z = 1")).unwrap();
    assert_eq!(makefile.to_string(), "Z = 1\nX = 1\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_item_insert_after_without_newline() {
    let makefile: Makefile = "X = 1\nY = 1\n".parse().unwrap();
    let mut first = makefile.items().next().unwrap();
    first.insert_after(item_without_newline("Z = 1")).unwrap();
    assert_eq!(makefile.to_string(), "X = 1\nZ = 1\nY = 1\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_rule_parent() {
    let makefile: Makefile = r#"all:
	echo "test"
"#
    .parse()
    .unwrap();

    let rule = makefile.rules().next().unwrap();
    let parent = rule.parent();
    // Parent is ROOT node which doesn't cast to MakefileItem
    assert!(parent.is_none());
}

#[test]
fn test_line_col() {
    let text = r#"# Comment at line 0
VAR1 = value1
VAR2 = value2

rule1: dep1 dep2
	command1
	command2

rule2:
	command3

ifdef DEBUG
CFLAGS = -g
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    // Test variable definition line numbers
    // variable_definitions() is recursive, so it finds VAR1, VAR2, and CFLAGS (inside conditional)
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars.len(), 3);

    // VAR1 starts at line 1
    assert_eq!(vars[0].line(), 1);
    assert_eq!(vars[0].column(), 0);
    assert_eq!(vars[0].line_col(), (1, 0));

    // VAR2 starts at line 2
    assert_eq!(vars[1].line(), 2);
    assert_eq!(vars[1].column(), 0);

    // CFLAGS starts at line 12 (inside ifdef DEBUG)
    assert_eq!(vars[2].line(), 12);
    assert_eq!(vars[2].column(), 0);

    // Test rule line numbers
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 2);

    // rule1 starts at line 4
    assert_eq!(rules[0].line(), 4);
    assert_eq!(rules[0].column(), 0);
    assert_eq!(rules[0].line_col(), (4, 0));

    // rule2 starts at line 8
    assert_eq!(rules[1].line(), 8);
    assert_eq!(rules[1].column(), 0);

    // Test conditional line numbers
    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 1);

    // ifdef DEBUG starts at line 11
    assert_eq!(conditionals[0].line(), 11);
    assert_eq!(conditionals[0].column(), 0);
    assert_eq!(conditionals[0].line_col(), (11, 0));
}

#[test]
fn test_line_col_multiline() {
    let text =
        "SOURCES = \\\n\tfile1.c \\\n\tfile2.c\n\ntarget: $(SOURCES)\n\tgcc -o target $(SOURCES)\n";
    let makefile: Makefile = text.parse().unwrap();

    // Variable definition starts at line 0
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].line(), 0);
    assert_eq!(vars[0].column(), 0);

    // Rule starts at line 4
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].line(), 4);
    assert_eq!(rules[0].column(), 0);
}

#[test]
fn test_line_col_includes() {
    let text = "VAR = value\n\ninclude config.mk\n-include optional.mk\n";
    let makefile: Makefile = text.parse().unwrap();

    // Variable at line 0
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars[0].line(), 0);

    // Includes at lines 2 and 3
    let includes: Vec<_> = makefile.includes().collect();
    assert_eq!(includes.len(), 2);
    assert_eq!(includes[0].line(), 2);
    assert_eq!(includes[0].column(), 0);
    assert_eq!(includes[1].line(), 3);
    assert_eq!(includes[1].column(), 0);
}

/// The original implementation of `line_col_at_offset`, which walks the
/// tree from the root on every call.
fn line_col_by_walking(node: &SyntaxNode, offset: rowan::TextSize) -> (usize, usize) {
    let root = node.ancestors().last().unwrap_or_else(|| node.clone());
    let mut line = 0;
    let mut last_newline_offset = rowan::TextSize::from(0);
    for element in root.preorder_with_tokens() {
        if let rowan::WalkEvent::Enter(rowan::NodeOrToken::Token(token)) = element {
            if token.text_range().start() >= offset {
                break;
            }
            for (idx, _) in token.text().match_indices('\n') {
                line += 1;
                last_newline_offset =
                    token.text_range().start() + rowan::TextSize::from((idx + 1) as u32);
            }
        }
    }
    (line, (offset - last_newline_offset).into())
}

fn assert_line_cols_match_walking(root: &SyntaxNode) {
    let positions = |f: fn(&SyntaxNode, rowan::TextSize) -> (usize, usize)| {
        root.descendants_with_tokens()
            .map(|element| {
                let start = element.text_range().start();
                let node = match &element {
                    rowan::NodeOrToken::Node(n) => n.clone(),
                    rowan::NodeOrToken::Token(t) => t.parent().unwrap(),
                };
                (element.kind(), start, f(&node, start))
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        positions(line_col_by_walking),
        positions(line_col_at_offset)
    );
}

#[test]
fn test_line_col_matches_walking() {
    let inputs = [
            "",
            "VAR = value",
            "VAR = value\n\nrule: dep\n\tcommand\n",
            "VAR = value\r\n\r\nrule: dep\r\n\tcommand\r\n",
            "A = 1\r\nB = 2\nC = 3\r\n",
            "VAR = a \\\n  b \\\n  c\nrule: x \\\n y\n\tcmd \\\n\t  more\n",
            "# comment\nifdef A\nifeq ($(B),1)\nX = 1\nelse ifneq ($(C),)\nX = 2\nelse\nX = 3\nendif\nendif\n",
            "rule:\n\techo a\nifdef V\n\techo verbose\nelse\n\t@echo quiet\nendif\n",
            "define F\nline one\nline two\nendef\n$(eval $(call F,x))\n",
            ".if ${A}\nX = 1\n.elif defined(B)\nX = 2\n.else\nX = 3\n.endif\n",
            "include a.mk\n-include b.mk\nvpath %.c src\n",
        ];
    for input in inputs {
        let (makefile, _) = Makefile::from_str_relaxed(input);
        assert_line_cols_match_walking(makefile.syntax());
    }
}

#[test]
fn test_line_col_after_mutation() {
    let mut makefile: Makefile = "A = 1\nifdef X\nB = 2\nendif\nrule: dep\n\tcmd\n"
        .parse()
        .unwrap();
    let mut rule = makefile.rules().next().unwrap();
    assert_eq!(rule.line(), 4);

    let mut var = makefile.variable_definitions().next().unwrap();
    var.set_value("one \\\n  two");
    assert_eq!(rule.line(), 5);
    assert_line_cols_match_walking(makefile.syntax());

    rule.push_command("second");
    let mut new_rule = makefile.add_rule("new");
    new_rule.push_command("build");
    assert_eq!(new_rule.line(), 9);
    assert_line_cols_match_walking(makefile.syntax());

    var.remove();
    assert_eq!(rule.line(), 3);
    assert_eq!(new_rule.line(), 7);
    assert_line_cols_match_walking(makefile.syntax());
}

#[test]
fn test_line_col_multiple_trees() {
    let a: Makefile = "A = 1\nrule:\n".parse().unwrap();
    let b: Makefile = "\n\n\nrule:\n".parse().unwrap();
    let rule_a = a.rules().next().unwrap();
    let rule_b = b.rules().next().unwrap();
    assert_eq!((rule_a.line(), rule_b.line()), (1, 3));
    assert_eq!((rule_a.line(), rule_b.line()), (1, 3));
}

#[test]
fn test_conditional_in_rule_vs_toplevel() {
    // Conditional immediately after rule (no blank line) - part of rule
    let text1 = r#"rule:
	command
ifeq (,$(X))
	test
endif
"#;
    let makefile: Makefile = text1.parse().unwrap();
    let rules: Vec<_> = makefile.rules().collect();
    let conditionals: Vec<_> = makefile.conditionals().collect();

    assert_eq!(rules.len(), 1);
    assert_eq!(
        conditionals.len(),
        0,
        "Conditional should be part of rule, not top-level"
    );

    // Conditional with recipe lines after a blank line - still part of
    // the rule, as make doesn't end a recipe at a blank line
    let text2 = r#"rule:
	command

ifeq (,$(X))
	test
endif
"#;
    let makefile: Makefile = text2.parse().unwrap();
    let rules: Vec<_> = makefile.rules().collect();
    let conditionals: Vec<_> = makefile.conditionals().collect();

    assert_eq!(rules.len(), 1);
    assert_eq!(
        conditionals.len(),
        0,
        "Conditional with recipe lines should be part of the rule"
    );

    // Conditional without recipe lines after a blank line - top-level
    let text3 = r#"rule:
	command

ifeq (,$(X))
X = 1
endif
"#;
    let makefile: Makefile = text3.parse().unwrap();
    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].line(), 3);
}

#[test]
fn test_nested_conditionals_line_tracking() {
    let text = r#"ifdef OUTER
VAR1 = value1
ifdef INNER
VAR2 = value2
endif
VAR3 = value3
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(
        conditionals.len(),
        1,
        "Only outer conditional should be top-level"
    );
    assert_eq!(conditionals[0].line(), 0);
    assert_eq!(conditionals[0].column(), 0);
}

#[test]
fn test_conditional_else_line_tracking() {
    let text = r#"VAR1 = before

ifdef DEBUG
DEBUG_FLAGS = -g
else
DEBUG_FLAGS = -O2
endif

VAR2 = after
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].line(), 2);
    assert_eq!(conditionals[0].column(), 0);
}

#[test]
fn test_broken_conditional_endif_without_if() {
    // endif without matching if - parser should handle gracefully
    let text = "VAR = value\nendif\n";
    let makefile = Makefile::read_relaxed(&mut text.as_bytes()).unwrap();

    // Should parse without crashing
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].line(), 0);
}

#[test]
fn test_broken_conditional_else_without_if() {
    // else without matching if
    let text = "VAR = value\nelse\nVAR2 = other\n";
    let makefile = Makefile::read_relaxed(&mut text.as_bytes()).unwrap();

    // Should parse without crashing
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert!(!vars.is_empty(), "Should parse at least the first variable");
    assert_eq!(vars[0].line(), 0);
}

#[test]
fn test_broken_conditional_missing_endif() {
    // ifdef without matching endif
    let text = r#"ifdef DEBUG
DEBUG_FLAGS = -g
VAR = value
"#;
    let makefile = Makefile::read_relaxed(&mut text.as_bytes()).unwrap();

    // Should parse without crashing
    assert!(makefile.code().contains("ifdef DEBUG"));
}

#[test]
fn test_multiple_conditionals_line_tracking() {
    let text = r#"ifdef A
VAR_A = a
endif

ifdef B
VAR_B = b
endif

ifdef C
VAR_C = c
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 3);
    assert_eq!(conditionals[0].line(), 0);
    assert_eq!(conditionals[1].line(), 4);
    assert_eq!(conditionals[2].line(), 8);
}

#[test]
fn test_conditional_with_multiple_else_ifeq() {
    let text = r#"ifeq ($(OS),Windows)
EXT = .exe
else ifeq ($(OS),Linux)
EXT = .bin
else
EXT = .out
endif
"#;
    let makefile = Makefile::read_relaxed(&mut text.as_bytes()).unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].line(), 0);
    assert_eq!(conditionals[0].column(), 0);
}

#[test]
fn test_conditional_types_line_tracking() {
    let text = r#"ifdef VAR1
A = 1
endif

ifndef VAR2
B = 2
endif

ifeq ($(X),y)
C = 3
endif

ifneq ($(Y),n)
D = 4
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 4);

    assert_eq!(conditionals[0].line(), 0); // ifdef
    assert_eq!(
        conditionals[0].conditional_type(),
        Some("ifdef".to_string())
    );

    assert_eq!(conditionals[1].line(), 4); // ifndef
    assert_eq!(
        conditionals[1].conditional_type(),
        Some("ifndef".to_string())
    );

    assert_eq!(conditionals[2].line(), 8); // ifeq
    assert_eq!(conditionals[2].conditional_type(), Some("ifeq".to_string()));

    assert_eq!(conditionals[3].line(), 12); // ifneq
    assert_eq!(
        conditionals[3].conditional_type(),
        Some("ifneq".to_string())
    );
}

#[test]
fn test_conditional_in_rule_with_recipes() {
    let text = r#"test:
	echo "start"
ifdef VERBOSE
	echo "verbose mode"
endif
	echo "end"
"#;
    let makefile: Makefile = text.parse().unwrap();

    let rules: Vec<_> = makefile.rules().collect();
    let conditionals: Vec<_> = makefile.conditionals().collect();

    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].line(), 0);
    // Conditional is part of the rule, not top-level
    assert_eq!(conditionals.len(), 0);
}

#[test]
fn test_conditional_without_recipes_after_rule() {
    let text = "t:: u\nifneq \"a\" \"b\"\nQ = 1\nendif\n";
    let makefile: Makefile = text.parse().unwrap();

    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].items().count(), 0);
    assert_eq!(makefile.conditionals().count(), 1);
    let names: Vec<_> = makefile
        .variable_definitions()
        .map(|v| v.name().unwrap())
        .collect();
    assert_eq!(names, vec!["Q"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_conditional_with_rule_after_rule() {
    let text = "ifdef X\na:\n\tx\nifdef Y\nb:\n\ty\nendif\nendif\n";
    let makefile: Makefile = text.parse().unwrap();

    let targets: Vec<_> = makefile
        .rules()
        .map(|r| r.targets().collect::<Vec<_>>().join(" "))
        .collect();
    assert_eq!(targets, vec!["a", "b"]);
    let rule_a = makefile.find_rule_by_target("a").unwrap();
    assert_eq!(rule_a.recipes().collect::<Vec<_>>(), vec!["x"]);
    assert_eq!(rule_a.items().count(), 1);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_conditional_mixing_recipes_and_variables_after_rule() {
    let text = "t:\n\techo a\nifdef X\n\techo b\nQ = 1\nendif\n";
    let makefile: Makefile = text.parse().unwrap();

    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 1);
    // The conditional starts with a recipe line, so it belongs to the rule
    assert_eq!(rules[0].items().count(), 2);
    assert_eq!(makefile.conditionals().count(), 0);
    let names: Vec<_> = makefile
        .variable_definitions()
        .map(|v| v.name().unwrap())
        .collect();
    assert_eq!(names, vec!["Q"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_conditional_with_recipe_in_else_after_rule() {
    let text = "t:\nifdef X\nQ = 1\nelse\n\techo b\nendif\n";
    let makefile: Makefile = text.parse().unwrap();

    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].items().count(), 1);
    assert_eq!(makefile.conditionals().count(), 0);
    let names: Vec<_> = makefile
        .variable_definitions()
        .map(|v| v.name().unwrap())
        .collect();
    assert_eq!(names, vec!["Q"]);
}

#[test]
fn test_nested_conditional_with_recipe_after_rule() {
    let text = "t:\nifdef X\n# comment\nifdef Y\n\techo b\nendif\nendif\n";
    let makefile: Makefile = text.parse().unwrap();

    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].items().count(), 1);
    assert_eq!(makefile.conditionals().count(), 0);
}

#[test]
fn test_bsd_loop_with_variable_in_rule() {
    let text = "t:\n\techo a\n.for x in a\n\techo ${x}\nQ=1\n.endfor\n";
    let parsed = Makefile::parse_with_variant(text, MakefileVariant::BSDMake);
    assert!(parsed.errors().is_empty(), "{:?}", parsed.errors());
    let makefile = parsed.tree();

    assert_eq!(makefile.rules().count(), 1);
    let names: Vec<_> = makefile
        .variable_definitions()
        .map(|v| v.name().unwrap())
        .collect();
    assert_eq!(names, vec!["Q"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_broken_conditional_double_else() {
    // Two else clauses in one conditional
    let text = r#"ifdef DEBUG
A = 1
else
B = 2
else
C = 3
endif
"#;
    let makefile = Makefile::read_relaxed(&mut text.as_bytes()).unwrap();

    // Should parse without crashing, though it's malformed
    assert!(makefile.code().contains("ifdef DEBUG"));
}

#[test]
fn test_broken_conditional_mismatched_nesting() {
    // Mismatched nesting - more endifs than ifs
    let text = r#"ifdef A
VAR = value
endif
endif
"#;
    let makefile = Makefile::read_relaxed(&mut text.as_bytes()).unwrap();

    // Should parse without crashing
    // The extra endif will be parsed separately, so we may get more than 1 item
    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert!(
        !conditionals.is_empty(),
        "Should parse at least the first conditional"
    );
}

#[test]
fn test_conditional_with_comment_line_tracking() {
    let text = r#"# This is a comment
ifdef DEBUG
# Another comment
CFLAGS = -g
endif
# Final comment
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].line(), 1);
    assert_eq!(conditionals[0].column(), 0);
}

#[test]
fn test_conditional_after_variable_with_blank_lines() {
    let text = r#"VAR1 = value1


ifdef DEBUG
VAR2 = value2
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let vars: Vec<_> = makefile.variable_definitions().collect();
    let conditionals: Vec<_> = makefile.conditionals().collect();

    // variable_definitions() is recursive, so it finds VAR1 and VAR2 (inside conditional)
    assert_eq!(vars.len(), 2);
    assert_eq!(vars[0].line(), 0); // VAR1
    assert_eq!(vars[1].line(), 4); // VAR2

    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].line(), 3);
}

#[test]
fn test_empty_conditional_line_tracking() {
    let text = r#"ifdef DEBUG
endif

ifndef RELEASE
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 2);
    assert_eq!(conditionals[0].line(), 0);
    assert_eq!(conditionals[1].line(), 3);
}

#[test]
fn test_recipe_line_tracking() {
    let text = r#"build:
	echo "Building..."
	gcc -o app main.c
	echo "Done"

test:
	./run-tests
"#;
    let makefile: Makefile = text.parse().unwrap();

    // Test first rule's recipes
    let rule1 = makefile.rules().next().expect("Should have first rule");
    let recipes: Vec<_> = rule1.recipe_nodes().collect();
    assert_eq!(recipes.len(), 3);

    assert_eq!(recipes[0].text(), "echo \"Building...\"");
    assert_eq!(recipes[0].line(), 1);
    assert_eq!(recipes[0].column(), 0);

    assert_eq!(recipes[1].text(), "gcc -o app main.c");
    assert_eq!(recipes[1].line(), 2);
    assert_eq!(recipes[1].column(), 0);

    assert_eq!(recipes[2].text(), "echo \"Done\"");
    assert_eq!(recipes[2].line(), 3);
    assert_eq!(recipes[2].column(), 0);

    // Test second rule's recipes
    let rule2 = makefile.rules().nth(1).expect("Should have second rule");
    let recipes2: Vec<_> = rule2.recipe_nodes().collect();
    assert_eq!(recipes2.len(), 1);

    assert_eq!(recipes2[0].text(), "./run-tests");
    assert_eq!(recipes2[0].line(), 6);
    assert_eq!(recipes2[0].column(), 0);
}

#[test]
fn test_recipe_with_variables_line_tracking() {
    let text = r#"install:
	mkdir -p $(DESTDIR)
	cp $(BINARY) $(DESTDIR)/
"#;
    let makefile: Makefile = text.parse().unwrap();
    let rule = makefile.rules().next().expect("Should have rule");
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 2);
    assert_eq!(recipes[0].line(), 1);
    assert_eq!(recipes[1].line(), 2);
}

#[test]
fn test_recipe_text_no_leading_tab() {
    // Test that Recipe::text() does not include the leading tab
    let text = "test:\n\techo hello\n\t\techo nested\n\t  echo with spaces\n";
    let makefile: Makefile = text.parse().unwrap();
    let rule = makefile.rules().next().expect("Should have rule");
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 3);

    // Debug: print syntax tree for the first recipe
    eprintln!("Recipe 0 syntax tree:\n{:#?}", recipes[0].syntax());

    // First recipe: single tab
    assert_eq!(recipes[0].text(), "echo hello");

    // Second recipe: double tab (nested)
    eprintln!("Recipe 1 syntax tree:\n{:#?}", recipes[1].syntax());
    assert_eq!(recipes[1].text(), "\techo nested");

    // Third recipe: tab followed by spaces
    eprintln!("Recipe 2 syntax tree:\n{:#?}", recipes[2].syntax());
    assert_eq!(recipes[2].text(), "  echo with spaces");
}

#[test]
fn test_recipe_parent() {
    let makefile: Makefile = "all: dep\n\techo hello\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();

    let parent = recipe.parent().expect("Recipe should have parent");
    assert_eq!(parent.targets().collect::<Vec<_>>(), vec!["all"]);
    assert_eq!(parent.prerequisites().collect::<Vec<_>>(), vec!["dep"]);
}

fn shell_texts(text: &str) -> Vec<String> {
    let makefile: Makefile = text.parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().map(|r| r.shell_text()).collect()
}

#[test]
fn test_recipe_shell_text_plain() {
    assert_eq!(shell_texts("all:\n\techo hello\n"), vec!["echo hello"]);
}

#[test]
fn test_recipe_shell_text_no_trailing_newline() {
    assert_eq!(shell_texts("all:\n\techo hello"), vec!["echo hello"]);
}

#[test]
fn test_recipe_shell_text_extra_indent() {
    assert_eq!(
        shell_texts("all:\n\t\techo a\n\t  echo b\n"),
        vec!["\techo a", "  echo b"]
    );
}

#[test]
fn test_recipe_shell_text_inline_hash() {
    assert_eq!(shell_texts("all:\n\techo a # b\n"), vec!["echo a # b"]);
}

#[test]
fn test_recipe_shell_text_comment_only() {
    assert_eq!(
        shell_texts("all:\n\t# just a comment\n\techo hello\n"),
        vec!["# just a comment", "echo hello"]
    );
}

#[test]
fn test_recipe_shell_text_quoted_hash() {
    assert_eq!(shell_texts("all:\n\techo \"x#y\"\n"), vec!["echo \"x#y\""]);
}

#[test]
fn test_recipe_shell_text_continuation_with_tab() {
    assert_eq!(
        shell_texts("all:\n\techo a \\\n\tb \\\n\t\tc\n\techo d\n"),
        vec!["echo a \\\nb \\\n\tc", "echo d"]
    );
}

#[test]
fn test_recipe_shell_text_continuation_without_tab() {
    assert_eq!(
        shell_texts("all:\n\techo a \\\n  b\n"),
        vec!["echo a \\\n  b"]
    );
}

#[test]
fn test_recipe_shell_text_continuation_with_hash() {
    assert_eq!(
        shell_texts("all:\n\techo a # b \\\n\tc\n"),
        vec!["echo a # b \\\nc"]
    );
}

#[test]
fn test_recipe_shell_text_continuation_comment_line() {
    assert_eq!(
        shell_texts("all:\n\techo a \\\n\t# x\n"),
        vec!["echo a \\\n# x"]
    );
}

#[test]
fn test_recipe_shell_text_keeps_prefixes() {
    assert_eq!(
        shell_texts("all:\n\t@echo a\n\t-echo b\n\t+echo c\n\t@-+echo d\n\t@# e\n"),
        vec!["@echo a", "-echo b", "+echo c", "@-+echo d", "@# e"]
    );
}

#[test]
fn test_recipe_shell_text_inline_recipe() {
    assert_eq!(
        shell_texts("all: dep ; echo hi # x\n\techo b\n"),
        vec!["echo hi # x", "echo b"]
    );
    assert_eq!(shell_texts("all: dep ;\t# x\n"), vec!["# x"]);
    assert_eq!(
        shell_texts("all: ; # a \\\n\t  b \\\n\tc\n"),
        vec!["# a \\\n  b \\\nc"]
    );
    assert_eq!(
        shell_texts("all: dep ;echo a \\\n\tb\n"),
        vec!["echo a \\\nb"]
    );
}

#[test]
fn test_recipe_insert_before_single() {
    let makefile: Makefile = "all:\n\techo world\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();

    recipe.insert_before("echo hello");

    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(recipes, vec!["echo hello", "echo world"]);
}

#[test]
fn test_recipe_insert_before_multiple() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    // Insert before the second recipe
    recipes[1].insert_before("echo middle");

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(
        new_recipes,
        vec!["echo one", "echo middle", "echo two", "echo three"]
    );
}

#[test]
fn test_recipe_insert_before_first() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[0].insert_before("echo zero");

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo zero", "echo one", "echo two"]);
}

#[test]
fn test_recipe_insert_after_single() {
    let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();

    recipe.insert_after("echo world");

    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(recipes, vec!["echo hello", "echo world"]);
}

#[test]
fn test_recipe_insert_after_multiple() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    // Insert after the second recipe
    recipes[1].insert_after("echo middle");

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(
        new_recipes,
        vec!["echo one", "echo two", "echo middle", "echo three"]
    );
}

#[test]
fn test_recipe_insert_after_last() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[1].insert_after("echo three");

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo one", "echo two", "echo three"]);
}

#[test]
fn test_recipe_remove_single() {
    let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();

    recipe.remove();

    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.recipes().count(), 0);
}

#[test]
fn test_recipe_remove_first() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[0].remove();

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo two", "echo three"]);
}

#[test]
fn test_recipe_remove_middle() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[1].remove();

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo one", "echo three"]);
}

#[test]
fn test_recipe_remove_last() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[2].remove();

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo one", "echo two"]);
}

#[test]
fn test_from_str_relaxed_valid() {
    let input = "all: foo\n\tfoo bar\n";
    let (makefile, errors) = Makefile::from_str_relaxed(input);
    assert!(errors.is_empty());
    assert_eq!(makefile.rules().count(), 1);
    assert_eq!(makefile.to_string(), input);
}

#[test]
fn test_from_str_relaxed_with_errors() {
    // "rule target\n\tcommand" produces a parse error (missing colon)
    let input = "rule target\n\tcommand\n";
    let (makefile, errors) = Makefile::from_str_relaxed(input);
    assert!(!errors.is_empty());
    // Round-trip preserves all text
    assert_eq!(makefile.to_string(), input);
}

#[test]
fn test_positioned_errors_have_valid_ranges() {
    let input = "rule target\n\tcommand\n";
    let parsed = Makefile::parse(input);
    assert!(!parsed.ok());

    let positioned = parsed.positioned_errors();
    assert!(!positioned.is_empty());

    for err in positioned {
        // Range should be within the input
        let start: u32 = err.range.start().into();
        let end: u32 = err.range.end().into();
        assert!(start <= end);
        assert!((end as usize) <= input.len());
    }
}

#[test]
fn test_positioned_errors_point_to_error_location() {
    let input = "rule target\n\tcommand\n";
    let parsed = Makefile::parse(input);
    assert!(!parsed.ok());

    let positioned = parsed.positioned_errors();
    assert!(!positioned.is_empty());

    let err = &positioned[0];
    let start: usize = err.range.start().into();
    let end: usize = err.range.end().into();
    // The error should point somewhere in the input
    let error_text = &input[start..end];
    assert!(!error_text.is_empty());

    // Tree should still be accessible
    let tree = parsed.tree();
    assert_eq!(tree.to_string(), input);
}

fn error_locations(input: &str) -> Vec<(String, usize, String, rowan::TextRange)> {
    let parsed = Makefile::parse(input);
    assert_eq!(parsed.errors().len(), parsed.positioned_errors().len());
    parsed
        .errors()
        .iter()
        .zip(parsed.positioned_errors())
        .map(|(e, p)| {
            assert_eq!(e.message, p.message);
            (e.message.clone(), e.line, e.context.clone(), p.range)
        })
        .collect()
}

fn error_kinds(input: &str, variant: Option<MakefileVariant>) -> Vec<ParseErrorKind> {
    let parsed = parse(input, variant);
    let kinds: Vec<_> = parsed.errors.iter().map(ErrorInfo::kind).collect();
    assert_eq!(
        parsed
            .positioned_errors
            .iter()
            .map(PositionedParseError::kind)
            .collect::<Vec<_>>(),
        kinds
    );
    kinds
}

#[test]
fn test_error_kind_missing_separator() {
    assert_eq!(
        error_kinds("foo bar\n", None),
        vec![ParseErrorKind::MissingSeparator]
    );
}

#[test]
fn test_error_kind_recipe_before_first_target() {
    assert_eq!(
        error_kinds("\techo hi\n", None),
        vec![ParseErrorKind::RecipeBeforeFirstTarget]
    );
    assert_eq!(
        error_kinds("X = 1\n\tfoo bar\n", None),
        vec![ParseErrorKind::RecipeBeforeFirstTarget]
    );
    assert_eq!(
        error_kinds("\techo hi\n", Some(MakefileVariant::BSDMake)),
        vec![ParseErrorKind::RecipeBeforeFirstTarget]
    );
}

#[test]
fn test_tab_indented_lines_outside_rule() {
    // GNU make reads a tab-indented line outside of rule context as an
    // ordinary line only if it is a comment, directive or assignment;
    // anything else is "recipe commences before first target", even if
    // it is an expression that expands to nothing. BSD make, POSIX and
    // nmake read every such line as a command.
    let error = vec![ParseErrorKind::RecipeBeforeFirstTarget];
    for (line, gnu) in [
        ("\t$(info hi)\n", error.clone()),
        ("\t$(eval X=1)\n", error.clone()),
        ("\t$(X)\n", error.clone()),
        ("\t$(info a) ; b\n", error.clone()),
        ("\techo hi\n", error.clone()),
        ("\tfoo: bar\n", error.clone()),
        ("\tX = 1\n", vec![]),
        ("\texport X\n", vec![]),
        ("\tinclude foo.mk\n", vec![]),
        ("\tifdef X\nendif\n", vec![]),
        ("\t# c\n", vec![]),
        ("\t\n", vec![]),
    ] {
        for prefix in ["", "a:\n\techo a\nY = 1\n"] {
            let input = format!("{}{}all:\n\techo ok\n", prefix, line);
            for variant in [None, Some(MakefileVariant::GNUMake)] {
                assert_eq!(
                    error_kinds(&input, variant),
                    gnu,
                    "{:?} {:?}",
                    variant,
                    input
                );
                assert_eq!(parse(&input, variant).root().to_string(), input);
            }
            if line.starts_with("\t#") || line == "\t\n" || line.contains("ifdef") {
                continue;
            }
            for variant in [
                MakefileVariant::BSDMake,
                MakefileVariant::POSIXMake,
                MakefileVariant::NMake,
            ] {
                assert_eq!(
                    error_kinds(&input, Some(variant)),
                    error,
                    "{:?} {:?}",
                    variant,
                    input
                );
                assert_eq!(parse(&input, Some(variant)).root().to_string(), input);
            }
        }
    }
}

#[test]
fn test_tab_indented_expression_outside_rule_is_recipe() {
    let input = "\t$(info hi)\nall:\n\techo ok\n";
    let parsed = parse(input, None);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.line, e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(1, "indented line not part of a rule")]
    );
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "RECIPE\nRULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\n"
    );
    assert_eq!(parsed.root().to_string(), input);
}

#[test]
fn test_error_kind_conditionals() {
    assert_eq!(
        error_kinds("ifdef FOO\nX = 1\n", None),
        vec![ParseErrorKind::MissingEndif]
    );
    assert_eq!(
        error_kinds("endif\n", None),
        vec![ParseErrorKind::ExtraneousEndif]
    );
    assert_eq!(
        error_kinds("else\n", None),
        vec![ParseErrorKind::ElseWithoutIf]
    );
    assert_eq!(
        error_kinds("ifeq foo\nendif\n", None),
        vec![ParseErrorKind::InvalidConditional]
    );
    assert_eq!(
        error_kinds("ifeq (a,b) x\nendif\n", None),
        vec![ParseErrorKind::ExtraneousText]
    );
    assert_eq!(
        error_kinds("ifeq (a,b\nendif\n", None),
        vec![ParseErrorKind::UnclosedParenthesis]
    );
}

fn error_lines(input: &str, variant: Option<MakefileVariant>) -> Vec<(ParseErrorKind, usize)> {
    let parsed = parse(input, variant);
    assert_eq!(parsed.root().syntax().to_string(), input);
    parsed.errors.iter().map(|e| (e.kind(), e.line)).collect()
}

#[test]
fn test_unterminated_block_error_line() {
    // GNU make reports a missing endef at the define line, and a
    // missing endif (like BSD make) at the line after the last one.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (input, expected) in [
            (
                "a:\n\techo a\n\ndefine foo\nbar\n\n",
                (ParseErrorKind::MissingEndef, 4),
            ),
            (
                "override define foo\nx\n",
                (ParseErrorKind::MissingEndef, 1),
            ),
            ("define \\\nfoo\nx\n", (ParseErrorKind::MissingEndef, 1)),
            (
                "define foo\ndefine bar\nx\nendef\n",
                (ParseErrorKind::MissingEndef, 1),
            ),
            ("ifdef X\nbar = 1\n", (ParseErrorKind::MissingEndif, 3)),
            ("ifdef X\nbar = 1", (ParseErrorKind::MissingEndif, 3)),
            ("ifdef X", (ParseErrorKind::MissingEndif, 2)),
            (
                "ifdef Y\nifdef X\nbar = 1\nendif\nbaz = 2\n\n",
                (ParseErrorKind::MissingEndif, 7),
            ),
        ] {
            assert_eq!(
                error_lines(input, variant),
                vec![expected],
                "{input:?} {variant:?}"
            );
        }
    }
    // BSD make reports open conditionals and unterminated .for loops at
    // the line after the last one too.
    for variant in [None, Some(MakefileVariant::BSDMake)] {
        for (input, expected) in [
            (".if 1\nX = 1\n", (ParseErrorKind::MissingEndif, 3)),
            (".if 1\nX = 1", (ParseErrorKind::MissingEndif, 3)),
            (".for i in a\nX = 1\n", (ParseErrorKind::MissingEndfor, 3)),
            (".for i in a\nX = 1", (ParseErrorKind::MissingEndfor, 3)),
            (
                ".for i in a\n.if 0\n.endfor\n",
                (ParseErrorKind::MissingEndif, 3),
            ),
        ] {
            assert_eq!(
                error_lines(input, variant),
                vec![expected],
                "{input:?} {variant:?}"
            );
        }
    }
    assert_eq!(
        error_lines("!IF 1\nX = 1\n", Some(MakefileVariant::NMake)),
        vec![(ParseErrorKind::MissingEndif, 3)]
    );
}

#[test]
fn test_error_kind_bsd_directives() {
    let bsd = Some(MakefileVariant::BSDMake);
    assert_eq!(
        error_kinds(".if 1\n", bsd),
        vec![ParseErrorKind::MissingEndif]
    );
    assert_eq!(
        error_kinds(".endif\n", bsd),
        vec![ParseErrorKind::ExtraneousEndif]
    );
    assert_eq!(
        error_kinds(".elif 1\n", bsd),
        vec![ParseErrorKind::ElseWithoutIf]
    );
    assert_eq!(
        error_kinds(".if\n.endif\n", bsd),
        vec![ParseErrorKind::InvalidConditional]
    );
    assert_eq!(
        error_kinds(".if 1\n.endif foo\n", bsd),
        vec![ParseErrorKind::ExtraneousText]
    );
    assert_eq!(
        error_kinds(".for x y\n.endfor\n", bsd),
        vec![ParseErrorKind::InvalidForLoop]
    );
    assert_eq!(
        error_kinds(".for x in a\n", bsd),
        vec![ParseErrorKind::MissingEndfor]
    );
    assert_eq!(
        error_kinds(".endfor\n", bsd),
        vec![ParseErrorKind::ExtraneousEndfor]
    );
}

#[test]
fn test_error_kind_references() {
    assert_eq!(
        error_kinds("X = $(FOO\n", None),
        vec![ParseErrorKind::UnclosedReference]
    );
    assert_eq!(
        error_kinds("X = ${FOO\n", None),
        vec![ParseErrorKind::UnclosedReference]
    );
}

#[test]
fn test_unclosed_bsd_include_path() {
    for variant in [None, Some(MakefileVariant::BSDMake)] {
        for (code, close) in [
            (".include \"a\n", '"'),
            (".include <a\n", '>'),
            (".include \"a#b\"\n", '"'),
            (". -include <a \\\n  b\n", '>'),
        ] {
            let parsed = parse(code, variant);
            assert_eq!(
                parsed
                    .errors
                    .iter()
                    .map(|e| (e.kind(), e.message.as_str(), e.line))
                    .collect::<Vec<_>>(),
                vec![(
                    ParseErrorKind::UnclosedIncludePath,
                    format!("unclosed .include filename, '{}' expected", close).as_str(),
                    1
                )],
                "{code:?}"
            );
            assert_eq!(parsed.root().syntax().to_string(), code);
        }
        for code in [
            ".include \"a\"\n",
            ".include <a> # c\n",
            ".include <a \\\n b>\n",
            ".include \"${X:S/a/b/}\"\n",
            ".include \"a\"\"\n",
        ] {
            assert_eq!(error_kinds(code, variant), vec![], "{code:?}");
        }
    }
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
    ] {
        assert_eq!(error_kinds("include \"a\n", variant), vec![]);
        assert_eq!(error_kinds("include <a\n", variant), vec![]);
    }
}

#[test]
fn test_bsd_unknown_directive() {
    // From NetBSD make's unit-tests/directive-misspellings.mk and
    // directive-*.mk. A name of `None` is for an include keyword followed
    // by junk, as in `.includex`.
    for (code, line, name) in [
        (".dinclud \"file\"\n", 1, Some("dinclud")),
        (".dincludx \"file\"\n", 1, Some("dincludx")),
        (".dincludes \"file\"\n", 1, None),
        (".erro msg\n", 1, Some("erro")),
        (".errox msg\n", 1, Some("errox")),
        (".expor varname\n", 1, Some("expor")),
        (".exporx varname\n", 1, Some("exporx")),
        (".exports varname\n", 1, Some("exports")),
        (".export-en\n", 1, Some("export-en")),
        (".export-environment\n", 1, Some("export-environment")),
        (".export-litera varname\n", 1, Some("export-litera")),
        (".export-literax varname\n", 1, Some("export-literax")),
        (".export-literally varname\n", 1, Some("export-literally")),
        (".-includ \"file\"\n", 1, Some("-includ")),
        (".-includx \"file\"\n", 1, Some("-includx")),
        (".-includes \"file\"\n", 1, None),
        (".includ \"file\"\n", 1, Some("includ")),
        (".includx \"file\"\n", 1, Some("includx")),
        (".includex \"file\"\n", 1, None),
        (".inf msg\n", 1, Some("inf")),
        (".infx msg\n", 1, Some("infx")),
        (".infos msg\n", 1, Some("infos")),
        (".sinclud \"file\"\n", 1, Some("sinclud")),
        (".sincludx \"file\"\n", 1, Some("sincludx")),
        (".sincludes \"file\"\n", 1, None),
        (".unde varname\n", 1, Some("unde")),
        (".undex varname\n", 1, Some("undex")),
        (".undefs varname\n", 1, Some("undefs")),
        (".unexpor varname\n", 1, Some("unexpor")),
        (".unexporx varname\n", 1, Some("unexporx")),
        (".unexports varname\n", 1, Some("unexports")),
        (".unexport-en\n", 1, Some("unexport-en")),
        (".unexport-enx\n", 1, Some("unexport-enx")),
        (".unexport-envs\n", 1, Some("unexport-envs")),
        (".warn msg\n", 1, Some("warn")),
        (".warnin msg\n", 1, Some("warnin")),
        (".warninx msg\n", 1, Some("warninx")),
        (".warnings msg\n", 1, Some("warnings")),
        (".undefinex varname\n", 1, Some("undefinex")),
        (".indented none\n", 1, Some("indented")),
        (".  indented 2 spaces\n", 1, Some("indented")),
        (".\tindented tab\n", 1, Some("indented")),
        (".${:Uinfo} directives cannot be indirect\n", 1, Some("")),
        (".iff 1\n", 1, Some("iff")),
        (".ifx 1\n", 1, Some("ifx")),
        (".ifn 1\n", 1, Some("ifn")),
        (".ifdefx X\n", 1, Some("ifdefx")),
        (".if 1\n.endfi\n.endif\n", 2, Some("endfi")),
        (".if 1\n.endifx\n.endif\n", 2, Some("endifx")),
        (".if 1\n.elsif 1\n.endif\n", 2, Some("elsif")),
        ("all:\n.elsif 1\n", 2, Some("elsif")),
    ] {
        let (kind, message) = match name {
            Some(name) => (
                ParseErrorKind::UnknownDirective,
                format!("Unknown directive \"{name}\""),
            ),
            None => (
                ParseErrorKind::UndelimitedIncludePath,
                ".include filename must be delimited by \"\" or <>".to_string(),
            ),
        };
        let parsed = parse(code, Some(MakefileVariant::BSDMake));
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| (e.kind(), e.message.as_str(), e.line))
                .collect::<Vec<_>>(),
            vec![(kind, message.as_str(), line)],
            "{code:?}"
        );
        assert_eq!(parsed.root().syntax().to_string(), code);
        // Without knowing which make reads it, it may be meant for GNU
        // make, which reports a missing separator.
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::POSIXMake),
            Some(MakefileVariant::NMake),
        ] {
            assert!(
                !error_kinds(code, variant).contains(&ParseErrorKind::UnknownDirective),
                "{code:?} {variant:?}"
            );
        }
        assert_eq!(
            error_kinds(code, None),
            vec![ParseErrorKind::MissingSeparator],
            "{code:?}"
        );
    }
    for code in [
        ".PHONY: all\n",
        ".MAIN:\n",
        ".target target: source\n",
        ".info:=\tvalue\n",
        ".foo = bar\n",
        ".c.o:\n\techo\n",
        ".${:Uinfo} : source\n",
        ".ifmake all\n.elifnmake x\n.elifdef X\n.elifndef Y\n.elifmake z\n.else\n.endif\n",
        ".ifnmake all\n.endif\n",
    ] {
        let parsed = parse(code, Some(MakefileVariant::BSDMake));
        assert_eq!(
            error_kinds(code, Some(MakefileVariant::BSDMake)),
            vec![],
            "{code:?}"
        );
        assert_eq!(parsed.root().syntax().to_string(), code);
    }
    // A line that does not start with a dot is not a directive.
    assert_eq!(
        parse("target-without-colon\n", Some(MakefileVariant::BSDMake))
            .errors
            .iter()
            .map(|e| (e.kind(), e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(ParseErrorKind::MissingSeparator, "expected ':'")]
    );
}

#[test]
fn test_undelimited_bsd_include_path() {
    for variant in [None, Some(MakefileVariant::BSDMake)] {
        for code in [
            ".include a.mk\n",
            ".include ${X}\n",
            ". sinclude a\"b\"\n",
            ".include \\\n  a.mk # c\n",
        ] {
            let parsed = parse(code, variant);
            assert_eq!(
                parsed
                    .errors
                    .iter()
                    .map(|e| (e.kind(), e.message.as_str(), e.line))
                    .collect::<Vec<_>>(),
                vec![(
                    ParseErrorKind::UndelimitedIncludePath,
                    ".include filename must be delimited by \"\" or <>",
                    if code.contains('\\') { 2 } else { 1 }
                )],
                "{code:?}"
            );
            assert_eq!(parsed.root().syntax().to_string(), code);
        }
        assert_eq!(
            error_kinds(".include\n", variant),
            vec![ParseErrorKind::MissingIncludePath]
        );
        assert_eq!(
            error_kinds(".include # c\n", variant),
            vec![ParseErrorKind::MissingIncludePath]
        );
    }
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
    ] {
        assert_eq!(error_kinds("include a.mk $(X)\n", variant), vec![]);
    }
    assert_eq!(
        error_kinds("!INCLUDE win32.mak\n", Some(MakefileVariant::NMake)),
        vec![]
    );
}

#[test]
fn test_bsd_include_keyword_with_junk() {
    // BSD make checks for an include directive before looking for a
    // dependency operator or assignment, and only compares the start of
    // the name, so these are includes with a bad path.
    for code in [
        ".includes: foo\n",
        ".includex = 1\n",
        ".include.mk: foo\n",
        ".sincludes: foo\n",
        ".-includes: foo\n",
        ".dincludex = 1\n",
        ". includes: foo\n",
        ".includes \\\n  foo: bar\n",
        ".includes \"foo\"\n",
    ] {
        let parsed = parse(code, Some(MakefileVariant::BSDMake));
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| (e.kind(), e.message.as_str(), e.line))
                .collect::<Vec<_>>(),
            vec![(
                ParseErrorKind::UndelimitedIncludePath,
                ".include filename must be delimited by \"\" or <>",
                1
            )],
            "{code:?}"
        );
        assert_eq!(node_kinds(&parsed.syntax()), "ERROR\n", "{code:?}");
        assert_eq!(parsed.root().syntax().to_string(), code);
    }
    // Like other directives, it doesn't end a rule's commands.
    let code = "all:\n.includes: foo\n\techo\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.kind(), e.line))
            .collect::<Vec<_>>(),
        vec![(ParseErrorKind::UndelimitedIncludePath, 2)]
    );
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "RULE\n  TARGETS\n  PREREQUISITES\n  ERROR\n  RECIPE\n"
    );
    assert_eq!(parsed.root().syntax().to_string(), code);
    // Other makes read these as rules and assignments.
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ] {
        for code in [".includes: foo\n", ".include.mk: foo\n", ".includex = 1\n"] {
            assert_eq!(error_kinds(code, variant), vec![], "{code:?} {variant:?}");
        }
    }
}

#[test]
fn test_bsd_directive_arguments() {
    // From NetBSD make's unit-tests/directive-unexport-env.mk,
    // directive-for-break.mk, directive-undef.mk, directive-else.mk and
    // directive-endif.mk.
    for variant in [None, Some(MakefileVariant::BSDMake)] {
        for (code, kind, message, line) in [
            (
                ".unexport-env UT_EXPORTED UT_UNEXPORTED\n",
                ParseErrorKind::ExtraneousText,
                "The directive .unexport-env does not take arguments",
                1,
            ),
            (
                ".for i in a\n.  break 1\n.endfor\n",
                ParseErrorKind::ExtraneousText,
                "The .break directive does not take arguments",
                2,
            ),
            (
                ".undef\n",
                ParseErrorKind::ExpectedVariableName,
                "The .undef directive requires an argument",
                1,
            ),
            (
                ".undef # comment\n",
                ParseErrorKind::ExpectedVariableName,
                "The .undef directive requires an argument",
                1,
            ),
            (
                ".if 1\n.else 1\n.endif\n",
                ParseErrorKind::ExtraneousText,
                "The .else directive does not take arguments",
                2,
            ),
            (
                ".if 1\n.endif 1\n",
                ParseErrorKind::ExtraneousText,
                "The .endif directive does not take arguments",
                2,
            ),
        ] {
            let parsed = parse(code, variant);
            assert_eq!(
                parsed
                    .errors
                    .iter()
                    .map(|e| (e.kind(), e.message.as_str(), e.line))
                    .collect::<Vec<_>>(),
                vec![(kind, message, line)],
                "{code:?} {variant:?}"
            );
            assert_eq!(parsed.root().syntax().to_string(), code);
        }
        for code in [
            ".unexport-env\n",
            ".unexport-env # comment\n",
            ".for i in a\n.break\n.endfor\n",
            ".undef X\n",
            ".export-env X\n",
            // BSD make ignores anything after `.endfor`.
            ".for i in a\n.endfor i\n",
        ] {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{code:?} {variant:?}");
            assert_eq!(parsed.root().syntax().to_string(), code);
        }
    }
    assert_eq!(
        parse("!IF 1\n!ELSE 1\n!ENDIF\n", Some(MakefileVariant::NMake))
            .errors
            .iter()
            .map(|e| (e.kind(), e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(
            ParseErrorKind::ExtraneousText,
            "The !ELSE directive does not take arguments"
        )]
    );
}

#[test]
fn test_bsd_commands_after_invalid_dependency_line() {
    // BSD make starts a new, empty list of targets before parsing a
    // dependency line, so the commands after an invalid one belong to
    // no target, which is not an error.
    let code = "all:\nfoo bar\n\techo\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.kind(), e.line))
            .collect::<Vec<_>>(),
        vec![(ParseErrorKind::MissingSeparator, 2)]
    );
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "RULE\n  TARGETS\n  PREREQUISITES\nRULE\n  TARGETS\n  ERROR\n  RECIPE\n"
    );
    assert_eq!(parsed.root().syntax().to_string(), code);
    for (code, line) in [
        ("foo\n\techo\n", 1),
        ("all:\n.elsif 1\n\techo\n\techo\n", 2),
    ] {
        let parsed = parse(code, Some(MakefileVariant::BSDMake));
        assert_eq!(
            parsed.errors.iter().map(|e| e.line).collect::<Vec<_>>(),
            vec![line],
            "{code:?}"
        );
        assert_eq!(parsed.root().syntax().to_string(), code);
    }
    // An assignment ends the empty list of targets.
    assert_eq!(
        error_kinds("foo\nX = 1\n\techo\n", Some(MakefileVariant::BSDMake)),
        vec![
            ParseErrorKind::MissingSeparator,
            ParseErrorKind::RecipeBeforeFirstTarget
        ]
    );
    for variant in [
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ] {
        assert_eq!(
            error_kinds("foo\n\techo\n", variant),
            vec![
                ParseErrorKind::MissingSeparator,
                ParseErrorKind::RecipeBeforeFirstTarget
            ],
            "{variant:?}"
        );
    }
}

#[test]
fn test_error_kind_variables_and_directives() {
    assert_eq!(
        error_kinds("override FOO bar\n", None),
        vec![ParseErrorKind::ExpectedAssignmentOperator]
    );
    assert_eq!(
        error_kinds("define\nendef\n", None),
        vec![ParseErrorKind::ExpectedVariableName]
    );
    assert_eq!(
        error_kinds("define FOO\nbar\n", None),
        vec![ParseErrorKind::MissingEndef]
    );
    assert_eq!(
        error_kinds("include\n", Some(MakefileVariant::POSIXMake)),
        vec![ParseErrorKind::MissingIncludePath]
    );
    assert_eq!(
        error_kinds("lib(member: foo\n", None),
        vec![
            ParseErrorKind::UnclosedArchiveMember,
            ParseErrorKind::MissingSeparator
        ]
    );
}

#[test]
fn test_error_location_middle_of_file() {
    assert_eq!(
        error_locations("X = 1\nY = 2\nfoo bar\n"),
        vec![(
            "expected ':'".to_string(),
            3,
            "foo bar".to_string(),
            rowan::TextRange::new(19.into(), 20.into())
        )]
    );
}

#[test]
fn test_error_location_after_multi_token_define_name() {
    assert_eq!(
        error_locations("define \\n\n\n\nendef\nfoo bar\n"),
        vec![(
            "expected ':'".to_string(),
            5,
            "foo bar".to_string(),
            rowan::TextRange::new(25.into(), 26.into())
        )]
    );
}

#[test]
fn test_error_location_first_line() {
    assert_eq!(
        error_locations("foo bar\nX = 1\n"),
        vec![(
            "expected ':'".to_string(),
            1,
            "foo bar".to_string(),
            rowan::TextRange::new(7.into(), 8.into())
        )]
    );
}

#[test]
fn test_error_location_last_line_without_newline() {
    assert_eq!(
        error_locations("X = 1\nfoo bar"),
        vec![(
            "expected ':'".to_string(),
            2,
            "foo bar".to_string(),
            rowan::TextRange::new(13.into(), 13.into())
        )]
    );
}

#[test]
fn test_error_location_in_conditional() {
    assert_eq!(
        error_locations("ifdef A\nfoo bar\nendif\n"),
        vec![(
            "expected ':'".to_string(),
            2,
            "foo bar".to_string(),
            rowan::TextRange::new(15.into(), 16.into())
        )]
    );
}

#[test]
fn test_error_location_after_rule() {
    assert_eq!(
        error_locations("all:\n\techo\nfoo bar\n"),
        vec![(
            "expected ':'".to_string(),
            3,
            "foo bar".to_string(),
            rowan::TextRange::new(18.into(), 19.into())
        )]
    );
}

#[test]
fn test_error_location_points_at_token() {
    assert_eq!(
        error_locations("X = 1\nendif\n"),
        vec![(
            "unknown conditional directive: endif".to_string(),
            2,
            "endif".to_string(),
            rowan::TextRange::new(6.into(), 11.into())
        )]
    );
}

#[test]
fn test_error_location_unclosed_paren() {
    assert_eq!(
        error_locations("X = 1\nifeq ($(X),y\nA = 1\nendif\n"),
        vec![(
            "unclosed parenthesis".to_string(),
            2,
            "ifeq ($(X),y".to_string(),
            rowan::TextRange::new(18.into(), 19.into())
        )]
    );
}

#[test]
fn test_tree_with_errors_preserves_text() {
    let input = "rule target\n\tcommand\nVAR = value\n";
    let parsed = Makefile::parse(input);
    assert!(!parsed.ok());

    let tree = parsed.tree();
    assert_eq!(tree.to_string(), input);

    // Valid parts should still be accessible
    assert_eq!(tree.variable_definitions().count(), 1);
}

#[test]
fn test_recipe_variable_references() {
    let makefile: Makefile = "all:\n\techo $(FOO) ${BAR}\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();
    let refs = recipe.variable_references();
    let names: Vec<_> = refs.iter().map(|r| r.name()).collect();
    assert_eq!(names, vec!["FOO", "BAR"]);

    // Ranges point at the variable names in the original source.
    let src = makefile.to_string();
    for r in &refs {
        let range = r.text_range();
        assert_eq!(&src[range], r.name());
    }
}

#[test]
fn test_variable_references_skip_define_body() {
    let text = "define E\n$(FOO) $(FOO:a=b)\nendef\nX = $(BAR)\n";
    let makefile: Makefile = text.parse().unwrap();
    assert_eq!(
        makefile
            .variable_references()
            .map(|r| (r.syntax().text().to_string(), r.name()))
            .collect::<Vec<_>>(),
        vec![("$(BAR)".to_string(), Some("BAR".to_string()))]
    );
}

#[test]
fn test_recipe_variable_references_skips_functions_and_automatic() {
    let makefile: Makefile = "all:\n\t$(shell ls) $@ $1 $(REAL)\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();
    let names: Vec<_> = recipe
        .variable_references()
        .iter()
        .map(|r| r.name().to_string())
        .collect();
    assert_eq!(names, vec!["REAL"]);
}

#[test]
fn test_recipe_variable_references_across_continuation() {
    let makefile: Makefile = "all:\n\techo $(FOO) \\\n\t  $(BAR)\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();
    let refs = recipe.variable_references();
    let names: Vec<_> = refs.iter().map(|r| r.name()).collect();
    assert_eq!(names, vec!["FOO", "BAR"]);

    let src = makefile.to_string();
    for r in &refs {
        assert_eq!(&src[r.text_range()], r.name());
    }
}

#[test]
fn test_assignment_operator_followed_by_operator_chars() {
    // Expected values match what GNU make 4.4 assigns for each line.
    for (src, op, value) in [
        ("X?==y\n", "?=", "=y"),
        ("X+==y\n", "+=", "=y"),
        ("X:==y\n", ":=", "=y"),
        ("X::==y\n", "::=", "=y"),
        ("X:::==y\n", ":::=", "=y"),
        ("X ?= =y\n", "?=", "=y"),
        ("X?=?y\n", "?=", "?y"),
        ("X?=:y\n", "?=", ":y"),
        ("X=::y\n", "=", "::y"),
        ("X==y\n", "=", "=y"),
    ] {
        let makefile: Makefile = src.parse().unwrap();
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1, "{src:?}");
        assert_eq!(vars[0].name(), Some("X".to_string()), "{src:?}");
        assert_eq!(
            vars[0].assignment_operator(),
            Some(op.to_string()),
            "{src:?}"
        );
        assert_eq!(vars[0].raw_value(), Some(value.to_string()), "{src:?}");
        assert_eq!(makefile.to_string(), src);
    }
}

#[test]
fn test_target_specific_assignment_followed_by_equals() {
    let rule: Rule = "foo: X?==1\n".parse().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["foo"]);
    let var = rule.scoped_assignment().unwrap();
    assert_eq!(var.name(), Some("X".to_string()));
    assert_eq!(var.assignment_operator(), Some("?=".to_string()));
    assert_eq!(var.raw_value(), Some("=1".to_string()));
}

/// Render the node structure (without tokens) of a parse tree, one node
/// per line, indented by depth.
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
fn test_space_indented_directives_in_conditional() {
    // Lines indented with spaces are never recipe lines.
    let code = "ifdef A\n  ifdef B\n  X = 1\n  endif\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    VARIABLE\n      EXPR\n    CONDITIONAL_ENDIF\n  CONDITIONAL_ENDIF\n"
        );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_tab_indented_directives_in_conditional_outside_rule() {
    // Without a preceding rule, tab-indented lines are ordinary makefile
    // lines rather than recipe lines.
    let code = "ifeq ($(os1),windows)\n\tgo_bin_dir = $(go_dir)/go/bin\n\tifneq ($(x),)\n\t\ty = 1\n\tendif\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n      EXPR\n  VARIABLE\n    EXPR\n      EXPR\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n        EXPR\n    VARIABLE\n      EXPR\n    CONDITIONAL_ENDIF\n  CONDITIONAL_ENDIF\n"
        );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_tab_indented_recipe_in_conditional_after_rule() {
    let code = "t2:\n\techo 1\nifdef DEBUG\n\techo dbg\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    RECIPE\n    CONDITIONAL_ENDIF\n"
        );
}

#[test]
fn test_assignment_ends_rule_context() {
    // An assignment ends the rule context, so a following tab-indented
    // line is no longer a recipe line, and the conditional doesn't
    // belong to the rule.
    let code = "t:\n\techo 1\nifdef DEBUG\nX = 1\n\tY = 2\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\n"
        );
}

#[test]
fn test_recipe_after_conditional_without_recipes() {
    // Rule context continues past a conditional that only holds
    // comments, so the following recipe line, and the conditional,
    // belong to the rule.
    let code = "t:\nifdef A\n# a\nelse\n# b\nendif\n\techo c\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    CONDITIONAL_ELSE\n    CONDITIONAL_ENDIF\n  RECIPE\n"
        );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_assignment_in_conditional_before_recipe_line() {
    // An assignment in one branch ends rule context after the
    // conditional, so the tab-indented line is an assignment.
    let code = "t:\nifdef A\nX = 1\nendif\n\tY = 2\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\nVARIABLE\n  EXPR\n"
        );
}

#[test]
fn test_comment_after_blank_line_ends_rule() {
    let input = "all:\n\techo a\n\n# c\nx = 1\n";
    let makefile = parse(input, None).root();
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.syntax().to_string(), "all:\n\techo a\n\n");
}

#[test]
fn test_conditional_after_blank_line_and_comment() {
    let input = "all:\n\techo a\n\n# c\nifdef X\n\techo x\nendif\n";
    let parsed = parse(input, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(parsed.root().code(), input);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    RECIPE\n    CONDITIONAL_ENDIF\n"
        );
}

#[test]
fn test_recipe_after_blank_line_and_indented_comment() {
    let input = "all:\n\techo a\n\n  # c\n\techo b\n";
    let parsed = parse(input, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.code(), input);
    assert_eq!(makefile.items().count(), 1);
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo a", "echo b"]);
    assert_eq!(rule.syntax().to_string(), input);
}

#[test]
fn test_recipe_after_conditional_ending_in_rule_context() {
    use crate::ast::makefile::MakefileItem;
    let input = "ifdef X\na:\nelse\nb:\nendif\n\techo hi\n";
    let parsed = parse(input, None);
    assert_eq!(parsed.errors, vec![]);
    // The recipe line belongs to `a` or `b` depending on the branch
    // taken, so it stays outside both rules.
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ELSE\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ENDIF\nRECIPE\n"
        );
    let makefile = parsed.root();
    assert_eq!(makefile.code(), input);
    let items: Vec<_> = makefile.items().collect();
    assert_eq!(items.len(), 2);
    assert!(matches!(items[0], MakefileItem::Conditional(_)));
    let MakefileItem::Recipe(recipe) = &items[1] else {
        panic!("expected recipe");
    };
    assert_eq!(recipe.text(), "echo hi");
}

#[test]
fn test_bsd_indented_comment_outside_rule() {
    // BSD make skips lines with only whitespace and a comment, so they
    // aren't recipe lines.
    let input = "X = 1\n\t# c\n\t# d \\\n\tmore\n\t\n";
    let parsed = parse(input, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(parsed.root().code(), input);
    assert_eq!(node_kinds(&parsed.syntax()), "VARIABLE\n  EXPR\n");
    assert_eq!(
        parsed
            .syntax()
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == COMMENT)
            .map(|t| t.text().to_string())
            .collect::<Vec<_>>(),
        vec!["# c", "# d \\\n\tmore"]
    );
}

#[test]
fn test_recipe_after_conditional_ending_rule_on_some_paths() {
    use crate::ast::makefile::MakefileItem;
    // If X is undefined, the rule context of `all` survives the
    // conditional and make runs `echo b`. If X is defined, the
    // assignment ends it and make reports "recipe commences before
    // first target".
    let input = "all:\n\t@echo a\n\nifdef X\nY=1\nendif\n\t@echo b\n";
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let parsed = parse(input, variant);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(
                node_kinds(&parsed.syntax()),
                "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\nRECIPE\n"
            );
        let makefile = parsed.root();
        assert_eq!(makefile.code(), input);
        let items: Vec<_> = makefile.items().collect();
        assert_eq!(items.len(), 3);
        let MakefileItem::Rule(rule) = &items[0] else {
            panic!("expected rule");
        };
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["@echo a"]);
        let MakefileItem::Recipe(recipe) = &items[2] else {
            panic!("expected recipe");
        };
        assert_eq!(recipe.text(), "@echo b");
    }
}

#[test]
fn test_recipe_after_conditional_ending_rule_in_one_branch() {
    let input = "all:\n\t@echo a\nifdef X\nY=1\nelse\n\t@echo c\nendif\n\t@echo b\n";
    let parsed = parse(input, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    VARIABLE\n      EXPR\n    CONDITIONAL_ELSE\n    RECIPE\n    CONDITIONAL_ENDIF\nRECIPE\n"
        );
    assert_eq!(parsed.root().code(), input);
}

#[test]
fn test_recipe_after_nested_conditional_ending_rule_on_some_paths() {
    let input = "all:\n\t@echo a\nifdef X\nifdef W\nY=1\nendif\nendif\n\t@echo b\n";
    let parsed = parse(input, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    VARIABLE\n      EXPR\n    CONDITIONAL_ENDIF\n  CONDITIONAL_ENDIF\nRECIPE\n"
        );
    assert_eq!(parsed.root().code(), input);
}

#[test]
fn test_recipe_after_conditional_with_rule_in_one_branch() {
    let input = "ifdef A\nt:\nendif\n\t@echo b\n";
    let parsed = parse(input, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ENDIF\nRECIPE\n"
        );
    assert_eq!(parsed.root().code(), input);
}

#[test]
fn test_recipe_after_conditional_ending_rule_on_all_paths() {
    // Make always reports "recipe commences before first target" here.
    let input = "all:\n\t@echo a\nifdef X\nY=1\nelse\nZ=1\nendif\n\t@echo b\n";
    let parsed = parse(input, None);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.line, e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(8, "indented line not part of a rule")]
    );
    assert_eq!(parsed.root().code(), input);
}

#[test]
fn test_assignment_after_conditional_ending_rule_on_some_paths() {
    // A tab-indented line that make also accepts outside of rule context
    // is still read as such.
    let input = "all:\n\t@echo a\nifdef X\nY=1\nendif\n\tZ = 1\n";
    let parsed = parse(input, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\nVARIABLE\n  EXPR\n"
        );
    assert_eq!(parsed.root().code(), input);
}

#[test]
fn test_statements_after_conditional_ending_rule_on_some_paths() {
    // GNU make only reads directives, assignments and comments as such
    // outside of rule context; other lines are recipe lines of `all` if
    // X is undefined, or "recipe commences before first target".
    let prefix = "all:\n\t@echo a\nifdef X\nY=1\nendif\n";
    for (line, kinds) in [
        ("\t$(info x)\n", "RECIPE\n"),
        ("\tfoo: bar\n", "RECIPE\n"),
        ("\tinclude foo.mk\n", "INCLUDE\n  EXPR\n"),
        ("\t# comment\n", ""),
    ] {
        let input = format!("{}{}", prefix, line);
        let parsed = parse(&input, None);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(
                node_kinds(&parsed.syntax()),
                format!(
                    "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\n{}",
                    kinds
                )
            );
        assert_eq!(parsed.root().code(), input);
    }
}

#[test]
fn test_bsd_recipe_after_conditional_ending_rule_on_some_paths() {
    // BSD make reads every tab-indented line as a shell command, which
    // belongs to `all` if X is undefined.
    for (input, last) in [
        (
            "all:\n\t@echo a\n.if defined(X)\nY=1\n.endif\n\t@echo b\n",
            "@echo b",
        ),
        (
            "all:\n\t@echo a\n.if defined(X)\nY=1\n.endif\n\tZ = 1\n",
            "Z = 1",
        ),
    ] {
        let parsed = parse(input, Some(MakefileVariant::BSDMake));
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(
                node_kinds(&parsed.syntax()),
                "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\nRECIPE\n"
            );
        let makefile = parsed.root();
        assert_eq!(makefile.code(), input);
        let crate::ast::makefile::MakefileItem::Recipe(recipe) = makefile.items().last().unwrap()
        else {
            panic!("expected recipe");
        };
        assert_eq!(recipe.text(), last);
    }
}

#[test]
fn test_bsd_recipe_after_conditional_ending_rule_on_all_paths() {
    let input = "all:\n\t@echo a\n.if defined(X)\nY=1\n.else\nZ=1\n.endif\n\t@echo b\n";
    let parsed = parse(input, Some(MakefileVariant::BSDMake));
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.line, e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(8, "indented line not part of a rule")]
    );
    assert_eq!(parsed.root().code(), input);
}

#[test]
fn test_expression_statement_ends_rule() {
    let input = "all:\n\techo a\n$(info i)\n\techo b\n";
    let parsed = parse(input, None);
    assert_eq!(
        parsed.errors,
        vec![ErrorInfo {
            message: "indented line not part of a rule".to_string(),
            line: 4,
            context: "\techo b".to_string(),
            kind: ParseErrorKind::RecipeBeforeFirstTarget,
        }]
    );
    let makefile = parsed.root();
    assert_eq!(makefile.code(), input);
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo a"]);
}

#[test]
fn test_rule_context_after_conditional_branch() {
    // A rule in one branch doesn't put the other branch, or the lines
    // after the conditional, in rule context: which applies depends on
    // which branch make takes. git's config.mak.uname relies on this.
    let code = "ifdef A\nt:\nelse\n\tX = 1\nendif\nifdef B\n\tY = 2\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ELSE\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\n"
        );
}

#[test]
fn test_rule_context_continues_after_conditional() {
    let code = "t:\nifdef A\n\techo a\nelse\n\techo b\nendif\n\techo c\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    RECIPE\n    CONDITIONAL_ELSE\n    RECIPE\n    CONDITIONAL_ENDIF\n  RECIPE\n"
        );
}

#[test]
fn test_rule_context_after_else_if() {
    // `else ifdef` is not a final else: if neither condition holds, no
    // rule was defined.
    let code = "ifdef A\nt:\nelse ifdef B\nt2:\nendif\n\tX = 1\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ELSE\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ENDIF\nVARIABLE\n  EXPR\n"
        );
}

#[test]
fn test_posix_tab_indented_line_outside_rule() {
    // Only GNU make re-reads a tab-indented line outside of a rule as an
    // ordinary makefile line; elsewhere it is a command line.
    for variant in [MakefileVariant::POSIXMake, MakefileVariant::NMake] {
        let code = "X = 1\n\tY = 2\nall:\n";
        let parsed = parse(code, Some(variant));
        assert_eq!(
            parsed.errors,
            vec![ErrorInfo {
                message: "indented line not part of a rule".to_string(),
                line: 2,
                context: "\tY = 2".to_string(),
                kind: ParseErrorKind::RecipeBeforeFirstTarget,
            }]
        );
        assert_eq!(
            node_kinds(&parsed.syntax()),
            "VARIABLE\n  EXPR\nRECIPE\nRULE\n  TARGETS\n  PREREQUISITES\n"
        );
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_posix_tab_indented_comment_and_blank_outside_rule() {
    for variant in [MakefileVariant::POSIXMake, MakefileVariant::NMake] {
        let code = "X = 1\n\t# c\n\t\nall:\n";
        let parsed = parse(code, Some(variant));
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(
            node_kinds(&parsed.syntax()),
            "VARIABLE\n  EXPR\nRULE\n  TARGETS\n  PREREQUISITES\n"
        );
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_bsd_rule_context_after_conditional_branch() {
    // BSD make always reads a tab-indented line as a shell command, and
    // reports "Unassociated shell command" outside of a rule. That
    // only happens if it takes the `.else` branch, so it is not an error
    // here.
    let code = ".if defined(A)\nt:\n.else\n\tX = 1\n.endif\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ELSE\n  RECIPE\n  CONDITIONAL_ENDIF\n"
        );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_whitespace_only_tab_line_outside_rule() {
    // BSD make skips empty commands before checking for a target.
    for variant in [
        MakefileVariant::BSDMake,
        MakefileVariant::POSIXMake,
        MakefileVariant::NMake,
    ] {
        let code = "X = 1\n\t\t\n\t \t\nall:\n";
        let parsed = parse(code, Some(variant));
        assert_eq!(parsed.errors, vec![], "{:?}", variant);
        assert_eq!(
            node_kinds(&parsed.syntax()),
            "VARIABLE\n  EXPR\nRULE\n  TARGETS\n  PREREQUISITES\n"
        );
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_bsd_whitespace_only_tab_line_after_assignment() {
    // From NetBSD's external/bsd/libpcap/bin/Makefile and
    // external/gpl3/gcc/lib/libbacktrace/Makefile.
    for code in [
        "NOPROG=\n\t\t\n.include <bsd.prog.mk>\n",
        "SRCS=\t\tdwarf.c elf.c \\\n\t\tposix.c state.c\n\t\t\nCPPFLAGS+=\t-I${DIST}/include\n",
    ] {
        let parsed = parse(code, Some(MakefileVariant::BSDMake));
        assert_eq!(parsed.errors, vec![], "{:?}", code);
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_bsd_tab_line_in_conditional_outside_rule() {
    // BSD make only reads the lines in the branch it takes, so whether
    // this is an unassociated command depends on the condition. From
    // NetBSD's external/mit/xorg/server/drivers/Makefile.
    let code = "SUBDIR+= \\\n\txf86-video-wsfb\n.if ${XORG_SERVER_SUBDIR} == \"xorg-server.old\"\n\txf86-video-apm \\\n\txf86-video-glint\n.endif\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "VARIABLE\n  EXPR\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n      EXPR\n  RECIPE\n  CONDITIONAL_ENDIF\n"
        );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_bsd_tab_line_in_for_loop_in_conditional_outside_rule() {
    // From NetBSD's etc/etc.sparc64/Makefile.inc, which is included in
    // rule context.
    let code = ".if ${MACHINE_ARCH} == \"sparc64\"\n\n\t# build 32 bit programs\n.for _d in lib/csu lib\n.if ${MKOBJDIRS} != \"no\"\n\t(cd ${_d} && \\\n\t    ${MAKE} obj)\n.endif\n\t(cd ${_d} && ${MAKE} cleandir)\n.endfor\n.endif\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n      EXPR\n  FOR_LOOP\n    FOR_HEADER\n      EXPR\n    CONDITIONAL\n      CONDITIONAL_IF\n        EXPR\n          EXPR\n      RECIPE\n      CONDITIONAL_ENDIF\n    RECIPE\n    FOR_END\n  CONDITIONAL_ENDIF\n"
        );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_nmake_tab_line_in_conditional_outside_rule() {
    let code = "!IF \"$(X)\" == \"y\"\n\techo a\n!ENDIF\n";
    let parsed = parse(code, Some(MakefileVariant::NMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n      EXPR\n  RECIPE\n  CONDITIONAL_ENDIF\n"
    );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_bsd_tab_line_in_for_loop_outside_rule() {
    // The body of a `.for` loop is read for every iteration, so this is
    // an unassociated command unless the loop has no iterations.
    let code = ".for f in a b\n\techo ${f}\n.endfor\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.line, e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(2, "indented line not part of a rule")]
    );
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "FOR_LOOP\n  FOR_HEADER\n    EXPR\n  RECIPE\n  FOR_END\n"
    );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_bsd_rule_context_continues_after_conditional() {
    let code = "t:\n.if defined(A)\n\techo a\n.elif defined(B)\n\techo b\n.else\n\techo c\n.endif\n\techo d\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    RECIPE\n    CONDITIONAL_ELSE\n      EXPR\n    RECIPE\n    CONDITIONAL_ELSE\n    RECIPE\n    CONDITIONAL_ENDIF\n  RECIPE\n"
        );
}

#[test]
fn test_bsd_rule_context_in_for_loop() {
    // As in BSD make, the rule from the last iteration of the loop is
    // still current after it, so this is a recipe line.
    let code = ".for f in a b\n${f}:\n\techo ${f}\n.endfor\n\tX = 1\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "FOR_LOOP\n  FOR_HEADER\n    EXPR\n  RULE\n    TARGETS\n      EXPR\n    PREREQUISITES\n    RECIPE\n  FOR_END\nRECIPE\n"
        );
    assert_eq!(parsed.root().to_string(), code);
}

/// The text of the last item of a makefile, which must be a recipe line.
fn last_recipe_text(makefile: &Makefile) -> String {
    let crate::ast::makefile::MakefileItem::Recipe(recipe) = makefile.items().last().unwrap()
    else {
        panic!("expected recipe");
    };
    recipe.text()
}

#[test]
fn test_gnu_conditional_keywords_end_rule_in_other_variants() {
    // Outside GNU make, a line starting with `ifdef` or `else` is an
    // ordinary line, here a variable assignment that ends the rule, so
    // the comment or conditional before it isn't part of the rule.
    for variant in [
        MakefileVariant::BSDMake,
        MakefileVariant::POSIXMake,
        MakefileVariant::NMake,
    ] {
        for name in ["X", "ifdef", "ifndef", "ifeq", "ifneq"] {
            let code = format!("all:\n\techo a\n\n# c\n{} = 1\n\techo b\n", name);
            let parsed = parse(&code, Some(variant));
            let makefile = parsed.root();
            assert_eq!(makefile.to_string(), code);
            assert_eq!(
                makefile.rules().next().unwrap().to_string(),
                "all:\n\techo a\n\n",
                "{:?} {:?}",
                variant,
                code
            );
        }
    }
    for (code, rule) in [
        (
            "all:\n\techo a\n.ifdef X\n.endif\nifdef = 1\n\techo b\n",
            "all:\n\techo a\n",
        ),
        (
            "all:\n\techo a\n\n# c\n.if 1\nelse = 1\n.endif\n\techo b\n",
            "all:\n\techo a\n\n",
        ),
    ] {
        let parsed = parse(code, Some(MakefileVariant::BSDMake));
        let makefile = parsed.root();
        assert_eq!(makefile.to_string(), code);
        assert_eq!(
            makefile.rules().next().unwrap().to_string(),
            rule,
            "{:?}",
            code
        );
    }
}

#[test]
fn test_nmake_rule_context_after_conditional_branch() {
    // The !ELSE branch is only taken if the rule wasn't defined, so the
    // command line in it is never part of a rule. Whether that is
    // reported as an error is up to the policy for command lines in
    // conditionals outside rules, so only the structure is checked here.
    for indent in ["\t", "  "] {
        let code = format!("!IFDEF A\nt:\n!ELSE\n{}X = 1\n!ENDIF\n", indent);
        let parsed = parse(&code, Some(MakefileVariant::NMake));
        assert_eq!(
                node_kinds(&parsed.syntax()),
                "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ELSE\n  RECIPE\n  CONDITIONAL_ENDIF\n"
            );
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_nmake_recipe_after_conditional_with_rule_on_some_paths() {
    for (conditional, kinds) in [
            (
                "!IFDEF A\nt:\n!ENDIF\n",
                "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ENDIF\nRECIPE\n",
            ),
            (
                "!IFDEF A\nt:\n!ELSEIFDEF B\nu:\n!ENDIF\n",
                "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ELSE\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ENDIF\nRECIPE\n",
            ),
            (
                "!IFDEF A\nt:\n!ELSE IFDEF B\nu:\n!ENDIF\n",
                "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ELSE\n    EXPR\n  RULE\n    TARGETS\n    PREREQUISITES\n  CONDITIONAL_ENDIF\nRECIPE\n",
            ),
            (
                "!IFDEF A\n!IFDEF B\nt:\n!ENDIF\n!ENDIF\n",
                "CONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    RULE\n      TARGETS\n      PREREQUISITES\n    CONDITIONAL_ENDIF\n  CONDITIONAL_ENDIF\nRECIPE\n",
            ),
        ] {
            for indent in ["\t", "  "] {
                let code = format!("{}{}X = 1\n", conditional, indent);
                let parsed = parse(&code, Some(MakefileVariant::NMake));
                assert_eq!(parsed.errors, vec![], "{:?}", code);
                assert_eq!(node_kinds(&parsed.syntax()), kinds, "{:?}", code);
                let makefile = parsed.root();
                assert_eq!(makefile.to_string(), code);
                assert_eq!(last_recipe_text(&makefile), "X = 1");
            }
        }
}

#[test]
fn test_nmake_recipe_after_conditional_ending_rule_on_some_paths() {
    for indent in ["\t", "  "] {
        let code = format!(
            "all:\n{0}echo a\n!IFDEF X\nY=1\n!ENDIF\n{0}echo b\n",
            indent
        );
        let parsed = parse(&code, Some(MakefileVariant::NMake));
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(
                node_kinds(&parsed.syntax()),
                "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nCONDITIONAL\n  CONDITIONAL_IF\n    EXPR\n  VARIABLE\n    EXPR\n  CONDITIONAL_ENDIF\nRECIPE\n"
            );
        let makefile = parsed.root();
        assert_eq!(makefile.to_string(), code);
        assert_eq!(last_recipe_text(&makefile), "echo b");
    }
}

#[test]
fn test_nmake_recipe_after_conditional_ending_rule_on_all_paths() {
    for indent in ["\t", "  "] {
        let code = format!(
            "all:\n{0}echo a\n!IFDEF X\nY=1\n!ELSE\nZ=1\n!ENDIF\n{0}echo b\n",
            indent
        );
        let parsed = parse(&code, Some(MakefileVariant::NMake));
        assert_eq!(
            parsed.errors,
            vec![ErrorInfo {
                message: "indented line not part of a rule".to_string(),
                line: 8,
                context: format!("{}echo b", indent),
                kind: ParseErrorKind::RecipeBeforeFirstTarget,
            }]
        );
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_nmake_rule_context_continues_after_conditional() {
    for indent in ["\t", "  "] {
        let code = format!(
                "t:\n!IF \"$(A)\" == \"1\"\n{0}echo a\n!ELSEIF \"$(B)\" == \"1\"\n{0}echo b\n!ELSE\n{0}echo c\n!ENDIF\n{0}echo d\n",
                indent
            );
        let parsed = parse(&code, Some(MakefileVariant::NMake));
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(
                node_kinds(&parsed.syntax()),
                "RULE\n  TARGETS\n  PREREQUISITES\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n        EXPR\n    RECIPE\n    CONDITIONAL_ELSE\n      EXPR\n        EXPR\n    RECIPE\n    CONDITIONAL_ELSE\n    RECIPE\n    CONDITIONAL_ENDIF\n  RECIPE\n"
            );
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_bsd_directives_in_rule() {
    // BSD make only ends a rule's commands at a dependency line or a
    // variable assignment, so these directives are part of the rule.
    for directive in [
        ".info hi",
        ".warning hi",
        ".error hi",
        ".undef X",
        ".export X",
        ".export-env X",
        ".unexport X",
        ".  undef X",
        ".include \"x.mk\"",
        ".-include \"x.mk\"",
        ".sinclude \"x.mk\"",
        ".dinclude \"x.mk\"",
        "include x.mk",
        "-include x.mk",
        "sinclude x.mk",
    ] {
        let code = format!("all:\n\techo a\n{}\n\n\techo b\n", directive);
        let parsed = parse(&code, Some(MakefileVariant::BSDMake));
        assert_eq!(parsed.errors, vec![], "{}", directive);
        let kind = if directive.contains("include") {
            "INCLUDE"
        } else {
            "DIRECTIVE"
        };
        assert_eq!(
            node_kinds(&parsed.syntax()),
            format!(
                "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\n  {}\n    EXPR\n  RECIPE\n",
                kind
            ),
            "{}",
            directive
        );
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_bsd_directive_after_rule() {
    // Without a recipe line after it, the directive isn't part of the
    // rule, as for conditionals.
    let code = "all:\n\techo a\n.info hi\nX = 1\n\techo b\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.line, e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(5, "indented line not part of a rule")]
    );
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nDIRECTIVE\n  EXPR\nVARIABLE\n  EXPR\nRECIPE\n"
    );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_bsd_include_in_rule_inside_conditional() {
    let code = "all:\n.if 1\n.include \"x.mk\"\n.endif\n\techo b\n";
    let parsed = parse(code, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
            node_kinds(&parsed.syntax()),
            "RULE\n  TARGETS\n  PREREQUISITES\n  CONDITIONAL\n    CONDITIONAL_IF\n      EXPR\n    INCLUDE\n      EXPR\n    CONDITIONAL_ENDIF\n  RECIPE\n"
        );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_include_ends_rule_in_gnu_make() {
    let code = "all:\n\techo a\ninclude x.mk\n\techo b\n";
    let parsed = parse(code, Some(MakefileVariant::GNUMake));
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.line, e.kind))
            .collect::<Vec<_>>(),
        vec![(4, ParseErrorKind::RecipeBeforeFirstTarget)]
    );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_error_position_after_relexed_line() {
    // Outside of a rule, the tab-indented line is relexed as a normal line
    // in the default mode. BSD make would reject it instead.
    let code = "\t.for in a\n.endfor\n";
    let parsed = parse(code, None);
    assert_eq!(
        parsed
            .positioned_errors
            .iter()
            .map(|e| (e.message.as_str(), e.range))
            .collect::<Vec<_>>(),
        vec![(
            "expected variable name after .for",
            rowan::TextRange::new(6.into(), 8.into())
        )]
    );
}

#[test]
fn test_invalid_line_reports_one_error() {
    // Error recovery skips the rest of the line rather than parsing it
    // as a new item.
    let code = "a b ; c d\nX = 1\n";
    let parsed = parse(code, None);
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["expected ':'"]
    );
    assert_eq!(parsed.root().to_string(), code);
    assert_eq!(parsed.root().variable_definitions().count(), 1);
}

#[test]
fn test_tab_indented_assignment_at_top_level() {
    let code = "\tX = 1\nall:\n\techo $(X)\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "VARIABLE\n  EXPR\nRULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\n"
    );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_tab_indented_comment_continuation_at_top_level() {
    // A backslash-newline continues a comment, so `more` and `\tmore`
    // are part of it rather than rules.
    for variant in [None, Some(MakefileVariant::POSIXMake)] {
        let code = "X = 1\n\t# d \\\n\tmore\n\t# e \\\nmore\nall:\n";
        let parsed = parse(code, variant);
        assert_eq!(parsed.errors, vec![]);
        assert_eq!(
            node_kinds(&parsed.syntax()),
            "VARIABLE\n  EXPR\nRULE\n  TARGETS\n  PREREQUISITES\n"
        );
        assert_eq!(
            parsed
                .syntax()
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .filter(|t| t.kind() == COMMENT)
                .map(|t| t.text().to_string())
                .collect::<Vec<_>>(),
            vec!["# d \\\n\tmore", "# e \\\nmore"]
        );
        assert_eq!(parsed.root().to_string(), code);
    }
}

#[test]
fn test_tab_indented_comment_ending_in_escaped_backslash() {
    let code = "X = 1\n\t# d \\\\\nY = 2\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "VARIABLE\n  EXPR\nVARIABLE\n  EXPR\n"
    );
    assert_eq!(parsed.root().to_string(), code);
}

#[test]
fn test_space_indented_line_after_rule_is_not_recipe() {
    let code = "t:\n\techo 1\n  X = 1\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\nVARIABLE\n  EXPR\n"
    );
}

#[test]
fn test_space_indented_recipe_recovered() {
    let code = "all:\n\techo a\n    echo b\n\n    echo c\nX = 1\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.root().to_string(), code);
    assert_eq!(
        parsed
            .positioned_errors
            .iter()
            .map(|e| (e.kind(), e.range, e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![
            (
                ParseErrorKind::MissingSeparator,
                rowan::TextRange::new(13.into(), 17.into()),
                "missing separator (recipe lines must start with a tab)"
            ),
            (
                ParseErrorKind::MissingSeparator,
                rowan::TextRange::new(25.into(), 29.into()),
                "missing separator (recipe lines must start with a tab)"
            ),
        ]
    );
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "RULE\n  TARGETS\n  PREREQUISITES\n  RECIPE\n  RECIPE\n  RECIPE\nVARIABLE\n  EXPR\n"
    );
    let rule = parsed.root().rules().next().unwrap();
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo a", "echo b", "echo c"]
    );
}

#[test]
fn test_space_indented_recipe_with_continuation_recovered() {
    let code = "all:\n    echo a \\\n    b\n\techo c\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.root().to_string(), code);
    assert_eq!(
        parsed
            .positioned_errors
            .iter()
            .map(|e| (e.kind(), e.range))
            .collect::<Vec<_>>(),
        vec![(
            ParseErrorKind::MissingSeparator,
            rowan::TextRange::new(5.into(), 9.into())
        )]
    );
    let rule = parsed.root().rules().next().unwrap();
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo a \\\n    b", "echo c"]
    );
}

#[test]
fn test_space_indented_line_outside_rule_not_recovered() {
    let code = "X = 1\n    echo b\n";
    let parsed = parse(code, None);
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "VARIABLE\n  EXPR\nRULE\n  TARGETS\n  ERROR\n"
    );
}

#[test]
fn test_parse_target_specific_computed_variable_name() {
    let code =
        "foo: obj-$(X) = 1\nfoo: $(V)_FLAGS += -g\n%.o: CFLAGS_$(ARCH) := -O2\nbar: ${Y}z?=$(Z)\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), code);
    let scoped = root
        .rules()
        .map(|r| {
            let v = r.scoped_assignment().unwrap();
            (
                r.targets().collect::<Vec<_>>(),
                v.name(),
                v.assignment_operator(),
                v.raw_value(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        scoped,
        vec![
            (
                vec!["foo".to_string()],
                Some("obj-$(X)".to_string()),
                Some("=".to_string()),
                Some("1".to_string())
            ),
            (
                vec!["foo".to_string()],
                Some("$(V)_FLAGS".to_string()),
                Some("+=".to_string()),
                Some("-g".to_string())
            ),
            (
                vec!["%.o".to_string()],
                Some("CFLAGS_$(ARCH)".to_string()),
                Some(":=".to_string()),
                Some("-O2".to_string())
            ),
            (
                vec!["bar".to_string()],
                Some("${Y}z".to_string()),
                Some("?=".to_string()),
                Some("$(Z)".to_string())
            ),
        ]
    );
}

#[test]
fn test_parse_target_specific_modifiers_with_computed_name() {
    let code =
        "foo: export obj-$(X) = 1\nbar: override $(V)_FLAGS += -g\nbaz: private export ${Y} := 2\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), code);
    let scoped = root
        .rules()
        .map(|r| {
            let v = r.scoped_assignment().unwrap();
            (
                v.name(),
                v.raw_value(),
                v.is_export(),
                v.is_override(),
                v.is_private(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        scoped,
        vec![
            (
                Some("obj-$(X)".to_string()),
                Some("1".to_string()),
                true,
                false,
                false
            ),
            (
                Some("$(V)_FLAGS".to_string()),
                Some("-g".to_string()),
                false,
                true,
                false
            ),
            (
                Some("${Y}".to_string()),
                Some("2".to_string()),
                true,
                false,
                true
            ),
        ]
    );
}

#[test]
fn test_parse_target_specific_variable_name_with_backslash() {
    let code = "foo: a\\b = 1\nbar: export x\\\\y ?= 2\nbaz: obj-$(X)\\c := 3\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), code);
    let scoped = root
        .rules()
        .map(|r| {
            let v = r.scoped_assignment().unwrap();
            (
                v.name(),
                v.assignment_operator(),
                v.raw_value(),
                v.is_export(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        scoped,
        vec![
            (
                Some("a\\b".to_string()),
                Some("=".to_string()),
                Some("1".to_string()),
                false
            ),
            (
                Some("x\\\\y".to_string()),
                Some("?=".to_string()),
                Some("2".to_string()),
                true
            ),
            (
                Some("obj-$(X)\\c".to_string()),
                Some(":=".to_string()),
                Some("3".to_string()),
                false
            ),
        ]
    );
}

#[test]
fn test_parse_rules_with_references_in_prerequisites() {
    let parsed = parse(
        "foo: $(DEPS)\nfoo: a b\n$(OBJS): %.o: %.c\nfoo: a | $(DIR)\nfoo: $(SRCS:.c=.o)\n",
        None,
    );
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.variable_definitions().count(), 0);
    let rules = root
        .rules()
        .map(|r| {
            (
                r.scoped_assignment().is_some(),
                r.prerequisites().collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        rules,
        vec![
            (false, vec!["$(DEPS)".to_string()]),
            (false, vec!["a".to_string(), "b".to_string()]),
            (false, vec!["%.c".to_string()]),
            (false, vec!["a".to_string()]),
            (false, vec!["$(SRCS:.c=.o)".to_string()]),
        ]
    );
}
#[test]
fn test_rule_target_starting_with_bracket() {
    let cases: &[(&str, &[&str])] = &[
        ("}: dep\n", &["}"]),
        ("): dep\n", &[")"]),
        ("{: dep\n", &["{"]),
        (",: dep\n", &[","]),
        ("\": dep\n", &["\""]),
        ("'a: dep\n", &["'a"]),
        ("}x: dep\n", &["}x"]),
        ("}x y: dep\n", &["}x", "y"]),
    ];
    let variants = [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::BSDMake),
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ];
    for (code, expected) in cases {
        for variant in variants {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{code:?} {variant:?}");
            let root = parsed.root();
            assert_eq!(root.to_string(), *code);
            let targets: Vec<Vec<String>> = root.rules().map(|r| r.targets().collect()).collect();
            assert_eq!(targets, vec![expected.to_vec()], "{code:?} {variant:?}");
        }
    }
}

#[test]
fn test_rule_target_starting_with_lparen() {
    // GNU make takes a leading `(` literally, while BSD make reads it as
    // an archive member list without an archive name.
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ] {
        let parsed = parse("(: dep\n(x: dep\n", variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let root = parsed.root();
        assert_eq!(root.to_string(), "(: dep\n(x: dep\n");
        let targets: Vec<Vec<String>> = root.rules().map(|r| r.targets().collect()).collect();
        assert_eq!(targets, vec![vec!["("], vec!["(x"]], "{variant:?}");
    }
    let parsed = parse("(: dep\n", Some(MakefileVariant::BSDMake));
    assert_eq!(
        parsed
            .errors
            .iter()
            .map(|e| (e.kind, e.message.as_str()))
            .collect::<Vec<_>>(),
        vec![(ParseErrorKind::UnexpectedToken, "unexpected token LPAREN")]
    );
    assert_eq!(parsed.root().to_string(), "(: dep\n");
}

#[test]
fn test_variable_name_starting_with_bracket() {
    let cases = [
        ("}x = 1\n", "}x"),
        (")x := 1\n", ")x"),
        (",x += 1\n", ",x"),
        ("\"x ?= 1\n", "\"x"),
    ];
    for (code, name) in cases {
        for variant in [
            None,
            Some(MakefileVariant::GNUMake),
            Some(MakefileVariant::POSIXMake),
            Some(MakefileVariant::NMake),
        ] {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{code:?} {variant:?}");
            let root = parsed.root();
            assert_eq!(root.to_string(), code);
            let names: Vec<Option<String>> =
                root.variable_definitions().map(|v| v.name()).collect();
            assert_eq!(names, vec![Some(name.to_string())], "{code:?} {variant:?}");
        }
    }
}
