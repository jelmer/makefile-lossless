use super::*;

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
        assert_eq!(parsed.root().to_string(), text);
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
        assert_eq!(parsed.root().to_string(), text);
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
    assert_eq!(parsed.root().to_string(), text);
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
    assert_eq!(
        makefile.to_string(),
        "export quiet Q KBUILD_VERBOSE\nall:\n"
    );
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
        assert_eq!(makefile.to_string(), text);
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
fn test_export_state() {
    use crate::ExportState::{Export, Unexport};
    // (code, is_export, is_unexport, export_state)
    let cases = [
        ("X = 1\n", false, false, None),
        ("export X = 1\n", true, false, Some(Export)),
        ("unexport X = 1\n", false, true, Some(Unexport)),
        ("unexport export X = 1\n", true, true, Some(Export)),
        ("export unexport X = 1\n", true, true, Some(Unexport)),
        ("export unexport export X = 1\n", true, true, Some(Export)),
        (
            "unexport export unexport X = 1\n",
            true,
            true,
            Some(Unexport),
        ),
        ("export export X = 1\n", true, false, Some(Export)),
        (
            "override unexport export X := 1\n",
            true,
            true,
            Some(Export),
        ),
        (
            "export override unexport X ?= 1\n",
            true,
            true,
            Some(Unexport),
        ),
        ("unexport \\\n export X = 1\n", true, true, Some(Export)),
        (
            "unexport export define X\n1\nendef\n",
            true,
            true,
            Some(Export),
        ),
        (
            "export unexport define X =\n1\nendef\n",
            true,
            true,
            Some(Unexport),
        ),
        (
            "unexport override export define X\n1\nendef\n",
            true,
            true,
            Some(Export),
        ),
        ("all: export X = 1\n", true, false, Some(Export)),
        (
            "all: private export override X = 1\n",
            true,
            false,
            Some(Export),
        ),
        ("all: override X = 1\n", false, false, None),
        ("all: unexport X = 1\n", false, true, Some(Unexport)),
        ("all: unexport export X = 1\n", true, true, Some(Export)),
        ("all: export unexport X = 1\n", true, true, Some(Unexport)),
        (
            "all: override unexport X = 1\n",
            false,
            true,
            Some(Unexport),
        ),
        (
            "all: unexport override export X := 1\n",
            true,
            true,
            Some(Export),
        ),
        ("all: private unexport X = 1\n", false, true, Some(Unexport)),
        ("export X\n", true, false, Some(Export)),
        ("export\n", true, false, Some(Export)),
        ("unexport\n", false, true, Some(Unexport)),
        ("unexport export X\n", false, true, Some(Unexport)),
        ("export unexport X\n", true, false, Some(Export)),
        ("export undefine X\n", true, false, None),
    ];
    for (code, is_export, is_unexport, state) in cases {
        let parsed = parse(code, Some(MakefileVariant::GNUMake));
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let root = parsed.root();
        assert_eq!(code, root.to_string());
        let vars: Vec<_> = root.variable_definitions().collect();
        assert_eq!(1, vars.len(), "{code:?}");
        assert_eq!(
            (is_export, is_unexport, state),
            (
                vars[0].is_export(),
                vars[0].is_unexport(),
                vars[0].export_state()
            ),
            "{code:?}"
        );
    }
}

#[test]
fn test_bare_export_later_keywords_are_names() {
    use crate::ExportState::{Export, Unexport};
    // GNU make only treats the first word of a bare directive as a keyword,
    // so `unexport export X` unexports the variables "export" and "X".
    // (code, names, is_export, is_unexport, is_override, is_private, state)
    let cases = [
        (
            "unexport export X\n",
            vec!["export", "X"],
            false,
            true,
            false,
            false,
            Some(Unexport),
        ),
        (
            "export unexport X\n",
            vec!["unexport", "X"],
            true,
            false,
            false,
            false,
            Some(Export),
        ),
        (
            "export export X\n",
            vec!["export", "X"],
            true,
            false,
            false,
            false,
            Some(Export),
        ),
        (
            "export override X\n",
            vec!["override", "X"],
            true,
            false,
            false,
            false,
            Some(Export),
        ),
        (
            "unexport private X\n",
            vec!["private", "X"],
            false,
            true,
            false,
            false,
            Some(Unexport),
        ),
        (
            "export \\\n unexport X\n",
            vec!["unexport", "X"],
            true,
            false,
            false,
            false,
            Some(Export),
        ),
        (
            "unexport \\\n export \\\n X\n",
            vec!["export", "X"],
            false,
            true,
            false,
            false,
            Some(Unexport),
        ),
        (
            "export export\n",
            vec!["export"],
            true,
            false,
            false,
            false,
            Some(Export),
        ),
        (
            "unexport export # c\n",
            vec!["export"],
            false,
            true,
            false,
            false,
            Some(Unexport),
        ),
    ];
    for (code, names, is_export, is_unexport, is_override, is_private, state) in cases {
        let parsed = parse(code, Some(MakefileVariant::GNUMake));
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let root = parsed.root();
        assert_eq!(code, root.to_string());
        let vars: Vec<_> = root.variable_definitions().collect();
        assert_eq!(1, vars.len(), "{code:?}");
        let var = &vars[0];
        assert_eq!(names, var.names().collect::<Vec<_>>(), "{code:?}");
        assert_eq!(Some(names[0].to_string()), var.name(), "{code:?}");
        assert_eq!(
            (is_export, is_unexport, is_override, is_private, state),
            (
                var.is_export(),
                var.is_unexport(),
                var.is_override(),
                var.is_private(),
                var.export_state()
            ),
            "{code:?}"
        );
        assert_eq!(
            vec![code.split_whitespace().next().unwrap().to_string()],
            var.keyword_ranges()
                .into_iter()
                .map(|(keyword, _)| keyword)
                .collect::<Vec<_>>(),
            "{code:?}"
        );
    }
}

#[test]
fn test_bare_modifier_not_export_is_error() {
    // GNU make: "missing separator", since only `export` and `unexport`
    // can appear without an assignment.
    for code in [
        "override export X\n",
        "private export X\n",
        "override unexport X Y\n",
        "override export\n",
        "override X\n",
        "private X # c\n",
    ] {
        let parsed = parse(code, Some(MakefileVariant::GNUMake));
        assert_eq!(
            vec![ParseErrorKind::ExpectedAssignmentOperator],
            parsed.errors.iter().map(|e| e.kind).collect::<Vec<_>>(),
            "{code:?}"
        );
        assert_eq!(code, parsed.root().to_string());
    }
}
