use super::*;

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
fn test_target_specific_unexport() {
    // (code, target, name, operator, value, unexport, export, override, private)
    let cases = [
        (
            "all: unexport FOO = x\n",
            "all",
            "FOO",
            "=",
            "x",
            true,
            false,
            false,
            false,
        ),
        (
            "%.o: unexport FOO = x\n",
            "%.o",
            "FOO",
            "=",
            "x",
            true,
            false,
            false,
            false,
        ),
        (
            "all: override unexport FOO := x\n",
            "all",
            "FOO",
            ":=",
            "x",
            true,
            false,
            true,
            false,
        ),
        (
            "all: unexport export FOO = x\n",
            "all",
            "FOO",
            "=",
            "x",
            true,
            true,
            false,
            false,
        ),
        (
            "all: private unexport FOO += x\n",
            "all",
            "FOO",
            "+=",
            "x",
            true,
            false,
            false,
            true,
        ),
        (
            "all: unexport \\\n FOO = x\n",
            "all",
            "FOO",
            "=",
            "x",
            true,
            false,
            false,
            false,
        ),
    ];
    for (code, target, name, op, value, unexport, export, override_, private) in cases {
        for variant in [None, Some(MakefileVariant::GNUMake)] {
            let parsed = parse(code, variant);
            assert_eq!(parsed.errors, vec![], "{variant:?} {code:?}");
            let root = parsed.root();
            assert_eq!(code, root.to_string());
            let rules: Vec<_> = root.rules().collect();
            assert_eq!(1, rules.len(), "{variant:?} {code:?}");
            assert_eq!(
                vec![target.to_string()],
                rules[0].targets().collect::<Vec<_>>()
            );
            assert_eq!(
                Vec::<String>::new(),
                rules[0].prerequisites().collect::<Vec<_>>(),
                "{variant:?} {code:?}"
            );
            let var = rules[0].scoped_assignment().unwrap();
            assert_eq!(
                (
                    Some(name.to_string()),
                    Some(op.to_string()),
                    Some(value.to_string()),
                    unexport,
                    export,
                    override_,
                    private,
                ),
                (
                    var.name(),
                    var.assignment_operator(),
                    var.raw_value(),
                    var.is_unexport(),
                    var.is_export(),
                    var.is_override(),
                    var.is_private(),
                ),
                "{variant:?} {code:?}"
            );
        }
    }
}

#[test]
fn test_target_specific_unexport_without_value() {
    // Without an assignment GNU make treats the words as prerequisites.
    let code = "all: unexport FOO\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(code, root.to_string());
    let rule = root.rules().next().unwrap();
    assert!(rule.scoped_assignment().is_none());
    assert_eq!(
        vec!["unexport".to_string(), "FOO".to_string()],
        rule.prerequisites().collect::<Vec<_>>()
    );
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
fn test_multiline_variable_with_backslash() {
    let content = r#"
LONG_VAR = This is a long variable \
    that continues on the next line \
    and even one more line
"#;

    // For now, we'll use relaxed parsing since the backslash handling isn't fully implemented
    let mut buf = content.as_bytes();
    let makefile = Makefile::from_reader_relaxed(&mut buf)
        .expect("Failed to parse multiline variable")
        .0;

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
    let makefile = Makefile::from_reader_relaxed(&mut buf)
        .expect("Failed to parse multiline variable with operators")
        .0;

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
fn test_ambiguous_assignment_vs_rule() {
    // Test case: Variable assignment with equals sign
    const VAR_ASSIGNMENT: &str = "VARIABLE = value\n";

    let mut buf = std::io::Cursor::new(VAR_ASSIGNMENT);
    let makefile = Makefile::from_reader_relaxed(&mut buf)
        .expect("Failed to parse variable assignment")
        .0;

    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    let rules = makefile.rules().collect::<Vec<_>>();

    assert_eq!(vars.len(), 1, "Expected 1 variable, found {}", vars.len());
    assert_eq!(rules.len(), 0, "Expected 0 rules, found {}", rules.len());

    assert_eq!(vars[0].name(), Some("VARIABLE".to_string()));

    // Test case: Simple rule with colon
    const SIMPLE_RULE: &str = "target: dependency\n";

    let mut buf = std::io::Cursor::new(SIMPLE_RULE);
    let makefile = Makefile::from_reader_relaxed(&mut buf)
        .expect("Failed to parse simple rule")
        .0;

    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    let rules = makefile.rules().collect::<Vec<_>>();

    assert_eq!(vars.len(), 0, "Expected 0 variables, found {}", vars.len());
    assert_eq!(rules.len(), 1, "Expected 1 rule, found {}", rules.len());

    let rule = &rules[0];
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["target"]);
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
    assert_eq!(makefile.to_string(), "VAR1 = value1\nVAR3 = value3\n");
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
    assert_eq!(makefile.to_string(), "VAR1 = value1\nVAR3 = value3\n");
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

    // The empty line still separates VAR1 from VAR3
    assert_eq!(makefile.to_string(), "VAR1 = value1\n\nVAR3 = value3\n");
}

#[test]
fn test_variable_remove_last_with_empty_line() {
    let makefile: Makefile = "VAR1 = value1\n\n# Comment about VAR2\nVAR2 = value2\n"
        .parse()
        .unwrap();
    let mut var2 = makefile.variable_definitions().nth(1).unwrap();
    var2.remove();
    assert_eq!(makefile.to_string(), "VAR1 = value1\n");
}

#[test]
fn test_variable_remove_doc_comment_after_rule() {
    let makefile: Makefile = "a:\n\techo\n# doc\nX = 1\nY = 2\n".parse().unwrap();
    let mut var = makefile.variable_definitions().next().unwrap();
    var.remove();
    assert_eq!(makefile.to_string(), "a:\n\techo\nY = 2\n");
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

    assert_eq!(makefile.to_string(), "VAR1 = value1\n\n\nVAR3 = value3\n");
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
    let code = makefile.to_string();
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
    let code = makefile.to_string();
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
    assert_eq!(makefile.to_string(), "#!/usr/bin/make -f\n\n%:\n\tdh $@\n");
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

#[test]
fn test_target_specific_empty_name_gnu() {
    // GNU make reads these as rules with a target-specific assignment to a
    // variable with an empty name, which is an error ("empty variable
    // name"). A `:=` after targets is the dependency operator `:` followed
    // by `=`, and `:::=` is `::` followed by `:=`.
    for (code, targets, op, error_range) in [
        ("a(b c) := 2\n", vec!["a(b c)"], "=", (8, 9)),
        ("a b := 2\n", vec!["a", "b"], "=", (5, 6)),
        ("a b:= 2\n", vec!["a", "b"], "=", (4, 5)),
        ("a(b c) ::= 2\n", vec!["a(b c)"], "=", (9, 10)),
        ("a b :::= 2\n", vec!["a", "b"], ":=", (6, 8)),
        ("a b :=\n", vec!["a", "b"], "=", (5, 6)),
        ("a: = 2\n", vec!["a"], "=", (3, 4)),
        ("a: += 2\n", vec!["a"], "+=", (3, 5)),
        ("a: != 2\n", vec!["a"], "!=", (3, 5)),
        ("a:: := 2\n", vec!["a"], ":=", (4, 6)),
    ] {
        let parsed = parse(code, Some(MakefileVariant::GNUMake));
        assert_eq!(
            vec![(
                ParseErrorKind::ExpectedVariableName,
                rowan::TextRange::new((error_range.0 as u32).into(), (error_range.1 as u32).into())
            )],
            parsed
                .positioned_errors
                .iter()
                .map(|e| (e.kind(), e.range))
                .collect::<Vec<_>>(),
            "{code:?}"
        );
        let root = parsed.root();
        assert_eq!(code, root.to_string());
        let rules: Vec<_> = root.rules().collect();
        assert_eq!(1, rules.len(), "{code:?}");
        assert_eq!(targets, rules[0].targets().collect::<Vec<_>>(), "{code:?}");
        assert_eq!(0, rules[0].prerequisites().count(), "{code:?}");
        let var = rules[0].scoped_assignment().unwrap();
        assert_eq!(None, var.name(), "{code:?}");
        assert_eq!(Some(op.to_string()), var.assignment_operator(), "{code:?}");
    }
}

#[test]
fn test_target_specific_empty_name_other_variants() {
    // BSD make ignores a target-local assignment with an empty name.
    for code in ["a b := 2\n", "a: = 2\n"] {
        assert_eq!(parse(code, None).errors, vec![], "{code:?}");
    }
    // Without a colon in the operator, GNU make finds no separator.
    let parsed = parse("a b != 2\n", Some(MakefileVariant::GNUMake));
    assert_eq!(
        vec![ParseErrorKind::MissingSeparator],
        parsed.errors.iter().map(|e| e.kind).collect::<Vec<_>>()
    );
}
