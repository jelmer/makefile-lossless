use super::*;

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
