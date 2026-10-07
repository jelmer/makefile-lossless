use super::*;
use crate::pattern::matches_pattern;

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
fn test_static_pattern_after_single_char_backslash_variable() {
    // `$\` is a reference to the variable `\`, so its backslash doesn't
    // escape the `:` that follows.
    let parsed = parse("a: %$\\: %.c\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r#"ROOT@0..12
  RULE@0..12
    TARGETS@0..1
      IDENTIFIER@0..1 "a"
    OPERATOR@1..2 ":"
    WHITESPACE@2..3 " "
    TARGET_PATTERN@3..6
      IDENTIFIER@3..4 "%"
      EXPR@4..6
        DOLLAR@4..5 "$"
        BACKSLASH@5..6 "\\"
    OPERATOR@6..7 ":"
    WHITESPACE@7..8 " "
    PREREQUISITES@8..11
      PREREQUISITE@8..11
        IDENTIFIER@8..11 "%.c"
    NEWLINE@11..12 "\n"
"#
    );
}

#[test]
fn test_static_pattern_colon_after_backslash_variable_at_eof() {
    for code in ["a:$\\:", "!$\\:", &format!("!${}:", "\\".repeat(25))] {
        let parsed = parse(code, None);
        assert_eq!(parsed.root().to_string(), code);
        let rule = parsed.root().rules().next().unwrap();
        assert_eq!(rule.prerequisites().count(), 0, "{code:?}");
    }
}

#[test]
fn test_space_after_backslash_variable_separates_prerequisites() {
    let parsed = parse("all: x$\\ y\n", None);
    assert_eq!(parsed.errors, vec![]);
    let rule = parsed.root().rules().next().unwrap();
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["x$\\", "y"]);
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
fn test_rule_parse_single_rule() {
    let text = "all: dep\n\techo hi\n";
    let parsed = Rule::parse(text);
    assert!(parsed.ok());
    let rule = parsed.tree();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["all"]);
    assert_eq!(rule.to_string(), text);
    let rule = parsed.to_result().unwrap();
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo hi"]);
}

#[test]
fn test_rule_parse_with_comments_and_blank_lines() {
    for text in [
        "# c\na: b\n",
        "\na: b\n",
        "a: b\n\n# c\n",
        "# c\n\na: b\n\n",
    ] {
        let parsed = Rule::parse(text);
        assert!(parsed.ok(), "{:?}", text);
        assert_eq!(parsed.syntax_node().to_string(), text);
        let rule = parsed.tree();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a"], "{:?}", text);
        assert_eq!(rule.syntax().ancestors().last().unwrap().to_string(), text);
        let rule: Rule = text.parse().unwrap();
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["b"]);
    }
}

#[test]
fn test_rule_parse_not_a_single_rule() {
    for (text, line, context, start, end, target) in [
        ("", 1, "", 0, 0, None),
        ("# c\n", 1, "# c", 0, 0, None),
        ("X = 1\n", 1, "X = 1", 0, 6, None),
        ("a: b\nc: d\n", 2, "c: d", 5, 10, Some("a")),
        ("# c\na: b\nX = 1\n", 3, "X = 1", 9, 15, Some("a")),
    ] {
        let parsed = Rule::parse(text);
        assert!(!parsed.ok(), "{:?}", text);
        assert_eq!(parsed.syntax_node().to_string(), text);
        assert_eq!(
            parsed
                .positioned_errors()
                .iter()
                .map(|e| (e.message.as_str(), e.range))
                .collect::<Vec<_>>(),
            vec![(
                "expected a single rule",
                rowan::TextRange::new(start.into(), end.into())
            )],
            "{:?}",
            text
        );
        if let Some(target) = target {
            assert_eq!(
                parsed.tree().targets().collect::<Vec<_>>(),
                vec![target],
                "{:?}",
                text
            );
        }
        let Err(Error::Parse(err)) = parsed.to_result() else {
            panic!("expected a parse error for {:?}", text);
        };
        assert_eq!(
            err.errors,
            vec![ErrorInfo {
                message: "expected a single rule".to_string(),
                line,
                context: context.to_string(),
                kind: ParseErrorKind::Other,
            }],
            "{:?}",
            text
        );
        assert!(text.parse::<Rule>().is_err(), "{:?}", text);
    }
}

#[test]
#[should_panic(expected = "no node of the requested type in the parsed text")]
fn test_rule_parse_tree_without_rule() {
    Rule::parse("X = 1\n").tree();
}

#[test]
fn test_static_pattern_colon_inside_unclosed_nested_reference() {
    // The `${` reference is not closed, so the `)` and `:` are inside it
    // rather than ending the `$(` reference and starting a target pattern.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let code = "x: $(${): y\n";
        let parsed = parse(code, variant);
        assert_eq!(parsed.root().to_string(), code);
        assert_eq!(
            error_kinds(code, variant),
            vec![
                ParseErrorKind::UnclosedReference,
                ParseErrorKind::UnclosedReference
            ]
        );
        let rule = parsed.root().rules().next().unwrap();
        assert_eq!(rule.static_pattern(), None);
    }
}
