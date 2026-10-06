use super::*;

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
fn test_variable_references_in_define_body() {
    let text = "define E\n$(FOO) $(FOO:a=b)\nendef\nX = $(BAR)\n";
    let makefile: Makefile = text.parse().unwrap();
    assert_eq!(
        makefile
            .variable_references()
            .map(|r| (r.syntax().text().to_string(), r.name()))
            .collect::<Vec<_>>(),
        vec![
            ("$(FOO)".to_string(), Some("FOO".to_string())),
            ("$(FOO:a=b)".to_string(), Some("FOO".to_string())),
            ("$(BAR)".to_string(), Some("BAR".to_string()))
        ]
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
