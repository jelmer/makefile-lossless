use super::*;

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
