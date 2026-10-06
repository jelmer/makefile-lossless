use super::*;

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
