use super::*;
use crate::MakefileVariant;

#[test]
fn test_recipe_continuation_lines() {
    let makefile_content = r#"override_dh_autoreconf:
	set -x; [ -f binoculars-ng/src/Hkl/H5.hs.orig ] || \
	  dpkg --compare-versions '$(HDF5_VERSION)' '<<' 1.12.0 || \
	  sed -i.orig 's/H5L_info_t/H5L_info1_t/g;s/h5l_iterate/h5l_iterate1/g' binoculars-ng/src/Hkl/H5.hs
	dh_autoreconf
"#;

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let rule = makefile.rules().next().unwrap();

    let recipes: Vec<_> = rule.recipe_nodes().collect();

    // Should have 2 recipe nodes: one multi-line command and one single-line
    assert_eq!(recipes.len(), 2);

    // First recipe should contain all three physical lines with newlines preserved,
    // and the leading tab stripped from each continuation line
    let expected_first = "set -x; [ -f binoculars-ng/src/Hkl/H5.hs.orig ] || \\\n  dpkg --compare-versions '$(HDF5_VERSION)' '<<' 1.12.0 || \\\n  sed -i.orig 's/H5L_info_t/H5L_info1_t/g;s/h5l_iterate/h5l_iterate1/g' binoculars-ng/src/Hkl/H5.hs";
    assert_eq!(recipes[0].text(), expected_first);

    // Second recipe should be the standalone dh_autoreconf line
    assert_eq!(recipes[1].text(), "dh_autoreconf");
}

#[test]
fn test_simple_continuation() {
    let makefile_content = "test:\n\techo hello && \\\n\t  echo world\n";

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 1);
    assert_eq!(recipes[0].text(), "echo hello && \\\n  echo world");
}

#[test]
fn test_multiple_continuations() {
    let makefile_content =
        "test:\n\techo line1 && \\\n\t  echo line2 && \\\n\t  echo line3 && \\\n\t  echo line4\n";

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 1);
    assert_eq!(
        recipes[0].text(),
        "echo line1 && \\\n  echo line2 && \\\n  echo line3 && \\\n  echo line4"
    );
}

#[test]
fn test_continuation_round_trip() {
    let makefile_content = "test:\n\techo hello && \\\n\t  echo world\n\techo done\n";

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let output = makefile.to_string();

    // Should preserve the exact content
    assert_eq!(output, makefile_content);
}

#[test]
fn test_continuation_with_silent_prefix() {
    let makefile_content = "test:\n\t@echo hello && \\\n\t  echo world\n";

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 1);
    assert_eq!(recipes[0].text(), "@echo hello && \\\n  echo world");
    assert!(recipes[0].is_silent());
}

#[test]
fn test_mixed_continued_and_non_continued() {
    let makefile_content = r#"test:
	echo first
	echo second && \
	  echo third
	echo fourth
"#;

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 3);
    assert_eq!(recipes[0].text(), "echo first");
    assert_eq!(recipes[1].text(), "echo second && \\\n  echo third");
    assert_eq!(recipes[2].text(), "echo fourth");
}

#[test]
fn test_continuation_replace_command() {
    let makefile_content = "test:\n\techo hello && \\\n\t  echo world\n\techo done\n";

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let mut rule = makefile.rules().next().unwrap();

    // Replace the multi-line command
    rule.replace_command(0, "echo replaced");

    let recipes: Vec<_> = rule.recipe_nodes().collect();
    assert_eq!(recipes.len(), 2);
    assert_eq!(recipes[0].text(), "echo replaced");
    assert_eq!(recipes[1].text(), "echo done");
}

#[test]
fn test_continuation_count() {
    let makefile_content = "test:\n\techo hello && \\\n\t  echo world\n\techo done\n";

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let rule = makefile.rules().next().unwrap();

    // Even though there are 3 physical lines, there should be 2 logical recipe nodes
    assert_eq!(rule.recipe_count(), 2);
    assert_eq!(rule.recipe_nodes().count(), 2);

    // recipes() should return one string per logical recipe node
    let recipes_list: Vec<_> = rule.recipes().collect();
    assert_eq!(
        recipes_list,
        vec!["echo hello && \\\n  echo world", "echo done"]
    );
}

#[test]
fn test_backslash_in_middle_of_line() {
    // Backslash not at end should not trigger continuation
    let makefile_content = "test:\n\techo hello\\nworld\n\techo done\n";

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 2);
    assert_eq!(recipes[0].text(), "echo hello\\nworld");
    assert_eq!(recipes[1].text(), "echo done");
}

#[test]
fn test_shell_for_loop_with_continuation() {
    // Regression test for Debian bug #1128608 / GitHub issue (if any)
    // Ensures shell for loops with backslash continuations are treated as
    // a single recipe node and preserve the 'done' statement
    let makefile_content = r#"override_dh_installman:
	for i in foo bar; do \
		pod2man --section=1 $$i ; \
	done
"#;

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let rule = makefile.rules().next().unwrap();

    // Should have exactly 1 recipe node containing the entire for loop
    let recipes: Vec<_> = rule.recipe_nodes().collect();
    assert_eq!(recipes.len(), 1);

    // The recipe text should contain the complete for loop including 'done'
    let recipe_text = recipes[0].text();
    let expected_recipe = "for i in foo bar; do \\\n\tpod2man --section=1 $$i ; \\\ndone";
    assert_eq!(recipe_text, expected_recipe);

    // Round-trip should preserve the complete structure
    let output = makefile.to_string();
    assert_eq!(output, makefile_content);
}

#[test]
fn test_shell_for_loop_remove_command() {
    // Regression test: removing other commands shouldn't affect 'done'
    // This simulates lintian-brush modifying debian/rules files
    let makefile_content = r#"override_dh_installman:
	for i in foo bar; do \
		pod2man --section=1 $$i ; \
	done
	echo "Done with man pages"
"#;

    let makefile = Makefile::read_relaxed(makefile_content.as_bytes()).unwrap();
    let mut rule = makefile.rules().next().unwrap();

    // Should have 2 recipe nodes: the for loop and the echo
    assert_eq!(rule.recipe_count(), 2);

    // Remove the second command (the echo)
    rule.remove_command(1);

    // Should now have only the for loop
    let recipes: Vec<_> = rule.recipe_nodes().collect();
    assert_eq!(recipes.len(), 1);

    // The for loop should still be complete with 'done'
    let output = makefile.to_string();
    let expected_output = r#"override_dh_installman:
	for i in foo bar; do \
		pod2man --section=1 $$i ; \
	done
"#;
    assert_eq!(output, expected_output);
}

#[test]
fn test_variable_reference_paren() {
    let makefile: Makefile = "CFLAGS = $(BASE_FLAGS) -Wall\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 1);
    assert_eq!(refs[0].name(), Some("BASE_FLAGS".to_string()));
    assert_eq!(refs[0].to_string(), "$(BASE_FLAGS)");
}

#[test]
fn test_variable_reference_brace() {
    let makefile: Makefile = "CFLAGS = ${BASE_FLAGS} -Wall\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 1);
    assert_eq!(refs[0].name(), Some("BASE_FLAGS".to_string()));
    assert_eq!(refs[0].to_string(), "${BASE_FLAGS}");
}

#[test]
fn test_variable_reference_in_prerequisites() {
    let makefile: Makefile = "all: $(TARGETS)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    let names: Vec<_> = refs.iter().filter_map(|r| r.name()).collect();
    assert!(names.contains(&"TARGETS".to_string()));
}

#[test]
fn test_variable_reference_multiple() {
    let makefile: Makefile =
        "CFLAGS = $(BASE_FLAGS) -Wall\nLDFLAGS = $(BASE_LDFLAGS) -lm\nall: $(TARGETS)\n"
            .parse()
            .unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    let names: Vec<_> = refs.iter().filter_map(|r| r.name()).collect();
    assert!(names.contains(&"BASE_FLAGS".to_string()));
    assert!(names.contains(&"BASE_LDFLAGS".to_string()));
    assert!(names.contains(&"TARGETS".to_string()));
}

#[test]
fn test_variable_reference_nested() {
    let makefile: Makefile = "FOO = $($(INNER))\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    let names: Vec<_> = refs.iter().filter_map(|r| r.name()).collect();
    assert!(names.contains(&"INNER".to_string()));
}

#[test]
fn test_variable_reference_line_col() {
    let makefile: Makefile = "A = 1\nB = $(FOO)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 1);
    assert_eq!(refs[0].name(), Some("FOO".to_string()));
    assert_eq!(refs[0].line(), 1);
    assert_eq!(refs[0].column(), 4);
    assert_eq!(refs[0].line_col(), (1, 4));
}

#[test]
fn test_variable_reference_no_refs() {
    let makefile: Makefile = "A = hello\nall:\n\techo done\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 0);
}

#[test]
fn test_variable_reference_mixed_styles() {
    let makefile: Makefile = "A = $(FOO) ${BAR}\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    let names: Vec<_> = refs.iter().filter_map(|r| r.name()).collect();
    assert_eq!(names.len(), 2);
    assert!(names.contains(&"FOO".to_string()));
    assert!(names.contains(&"BAR".to_string()));
}

#[test]
fn test_brace_variable_in_prerequisites() {
    let makefile: Makefile = "all: ${OBJS}\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 1);
    assert_eq!(refs[0].name(), Some("OBJS".to_string()));
}

#[test]
fn test_parse_brace_variable_roundtrip() {
    let input = "CFLAGS = ${BASE_FLAGS} -Wall\n";
    let makefile: Makefile = input.parse().unwrap();
    assert_eq!(makefile.to_string(), input);
}

#[test]
fn test_parse_nested_variable_in_value_roundtrip() {
    let input = "FOO = $(BAR) baz $(QUUX)\n";
    let makefile: Makefile = input.parse().unwrap();
    assert_eq!(makefile.to_string(), input);
}

#[test]
fn test_is_function_call() {
    let makefile: Makefile = "FILES = $(wildcard *.c)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 1);
    assert!(refs[0].is_function_call());
}

#[test]
fn test_is_function_call_simple_variable() {
    let makefile: Makefile = "CFLAGS = $(CC)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 1);
    assert!(!refs[0].is_function_call());
}

#[test]
fn test_is_function_call_with_commas() {
    let makefile: Makefile = "X = $(subst a,b,text)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 1);
    assert!(refs[0].is_function_call());
}

#[test]
fn test_is_function_call_braces() {
    let makefile: Makefile = "FILES = ${wildcard *.c}\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs.len(), 1);
    assert!(refs[0].is_function_call());
}

#[test]
fn test_argument_count_simple_variable() {
    let makefile: Makefile = "CFLAGS = $(CC)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs[0].argument_count(), 0);
}

#[test]
fn test_argument_count_one_arg() {
    let makefile: Makefile = "FILES = $(wildcard *.c)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs[0].argument_count(), 1);
}

#[test]
fn test_argument_count_three_args() {
    let makefile: Makefile = "X = $(subst a,b,text)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs[0].argument_count(), 3);
}

#[test]
fn test_argument_index_at_offset_subst() {
    let makefile: Makefile = "X = $(subst a,b,text)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    // "X = $(subst a,b,text)"
    //  0123456789012345678901
    //              ^first arg (offset 12)
    //                ^second arg (offset 14)
    //                  ^third arg (offset 16)
    assert_eq!(refs[0].argument_index_at_offset(12), Some(0));
    assert_eq!(refs[0].argument_index_at_offset(14), Some(1));
    assert_eq!(refs[0].argument_index_at_offset(16), Some(2));
}

#[test]
fn test_argument_index_at_offset_outside() {
    let makefile: Makefile = "X = $(subst a,b,text)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    // Before the reference
    assert_eq!(refs[0].argument_index_at_offset(0), None);
    // After the reference
    assert_eq!(refs[0].argument_index_at_offset(22), None);
}

#[test]
fn test_argument_index_at_offset_simple_variable() {
    let makefile: Makefile = "CFLAGS = $(CC)\n".parse().unwrap();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(refs[0].argument_index_at_offset(11), None);
}

#[test]
fn test_lex_braces() {
    use crate::lex::lex;
    let tokens = lex("${FOO}", None);
    let kinds: Vec<_> = tokens.iter().map(|(k, _)| *k).collect();
    assert!(kinds.contains(&DOLLAR));
    assert!(kinds.contains(&LBRACE));
    assert!(kinds.contains(&RBRACE));
}

#[test]
fn test_parse_quoted_string_inside_function_call() {
    // Make does not look at quotes, so parentheses inside them count
    // towards closing the reference. Lone or asymmetric quotes (it's,
    // foo'bar) must not swallow the rest of the line.
    let cases = [
        "X = $(if a,'foo')\n",
        "X = $(if a,'foo (bar)')\n",
        "X = $(if a,')')\n",
        "X = $(if $(SKIP),-k 'not ($(call f,$(s),$(SKIP)))')\n",
        "X = foo'bar\nY = baz\n",
        "X = it's fine\n",
        "X = $(if a,it's)\n",
        "X = '\nY = bar\n",
    ];
    for src in cases {
        let parsed: Makefile = src.parse().unwrap_or_else(|e| {
            panic!("failed to parse {src:?}: {e:?}");
        });
        assert_eq!(parsed.to_string(), src, "round-trip mismatch for {src:?}");
    }

    let src = "X = $(if a,'(')\n";
    let parsed = parse(src, None);
    assert_eq!(parsed.root().to_string(), src);
    assert_eq!(
        parsed.errors.iter().map(|e| e.kind()).collect::<Vec<_>>(),
        vec![ParseErrorKind::UnclosedReference]
    );
}

#[test]
fn test_parse_unclosed_conditional_paren_does_not_panic() {
    // Found by cargo-fuzz: nested LPAREN inside ifeq()/ifneq() opened
    // an EXPR node that was only closed by the matching RPAREN. EOF
    // before the close left the green tree unbalanced and rowan
    // panicked in GreenNodeBuilder::finish.
    let cases = ["ifeq((", "ifeq(((((", "ifneq((", "ifeq(($(X)", "X = $(("];
    for src in cases {
        let parse = crate::parse::Parse::<Makefile>::parse_makefile(src);
        assert_eq!(
            parse.tree().to_string(),
            src,
            "round-trip mismatch for {src:?}"
        );
    }
}

#[test]
fn test_parse_missing_endif_is_error() {
    let (makefile, errors) = Makefile::from_str_relaxed("ifdef X\nY = 1\n");
    assert_eq!(
        errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["unterminated conditional (missing endif)"]
    );
    assert_eq!(makefile.to_string(), "ifdef X\nY = 1\n");
    assert!("ifdef X\nY = 1\n".parse::<Makefile>().is_err());
}

#[test]
fn test_parse_nested_missing_endif_is_error() {
    let (_, errors) = Makefile::from_str_relaxed("ifdef X\nifdef Y\nZ = 1\nendif\n");
    assert_eq!(
        errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["unterminated conditional (missing endif)"]
    );
}

#[test]
fn test_parse_unclosed_conditional_paren_stops_at_eol() {
    let src = "ifeq ($(X),y\nA = 1\nendif\nB = 2\n";
    let (makefile, errors) = Makefile::from_str_relaxed(src);
    assert_eq!(
        errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["unclosed parenthesis"]
    );
    assert_eq!(makefile.to_string(), src);
    let cond = makefile.conditionals().next().unwrap();
    assert_eq!(cond.condition(), Some("($(X),y".to_string()));
    assert_eq!(cond.to_string(), "ifeq ($(X),y\nA = 1\nendif\n");
    assert_eq!(makefile.items().count(), 2);
}

#[test]
fn test_parse_unclosed_variable_ref_in_conditional_stops_at_eol() {
    let src = "ifeq (a,$(X\nA = 1\nendif\n";
    let (makefile, errors) = Makefile::from_str_relaxed(src);
    assert_eq!(
        errors
            .iter()
            .map(|e| e.message.as_str())
            .collect::<Vec<_>>(),
        vec!["unclosed variable reference", "unclosed parenthesis"]
    );
    assert_eq!(makefile.to_string(), src);
    let cond = makefile.conditionals().next().unwrap();
    assert_eq!(cond.condition(), Some("(a,$(X".to_string()));
}

#[test]
fn test_parse_conditional_paren_with_continuation() {
    let src = "ifeq ($(X),\\\n  y)\nA = 1\nendif\n";
    let makefile: Makefile = src.parse().unwrap();
    assert_eq!(makefile.to_string(), src);
    assert_eq!(makefile.conditionals().count(), 1);
}

#[test]
fn test_parse_unexpected_tokens_at_top_level_does_not_panic() {
    // Found by cargo-fuzz: the top-level dispatcher's catch-all arm
    // bumped a token after `error()` had already consumed one, which
    // could pop past the end of the token stack. The parser must
    // tolerate arbitrary garbage without panicking, and the lossless
    // round-trip must still hold.
    let cases = ["(", "(\0(", ")", "(())", "\0", ",", ":", "((((((((((("];
    for src in cases {
        let parse = crate::parse::Parse::<Makefile>::parse_makefile(src);
        assert_eq!(
            parse.tree().to_string(),
            src,
            "round-trip mismatch for {src:?}"
        );
    }
}

/// The text of each line continuation in `text`, with the text before it.
fn continuations(text: &str, variant: MakefileVariant) -> Vec<(&str, &str)> {
    let makefile = Makefile::parse_with_variant(text, variant).tree();
    makefile
        .line_continuations()
        .map(|range| {
            let start = usize::from(range.start());
            (&text[..start], &text[range])
        })
        .collect()
}

#[test]
fn test_line_continuations() {
    let text = "A = a \\\n  b\nall: x \\\n  y\n\techo \\\n\t  z\n# c \\\n d\n";
    assert_eq!(
        continuations(text, MakefileVariant::GNUMake),
        vec![
            ("A = a ", "\\\n"),
            ("A = a \\\n  b\nall: x ", "\\\n"),
            ("A = a \\\n  b\nall: x \\\n  y\n\techo ", "\\\n"),
            (
                "A = a \\\n  b\nall: x \\\n  y\n\techo \\\n\t  z\n# c ",
                "\\\n"
            ),
        ]
    );
}

#[test]
fn test_line_continuations_ranges() {
    let makefile: Makefile = "all: a \\\n  b\n\techo \\\r\n\tc\n".parse().unwrap();
    assert_eq!(
        makefile.line_continuations().collect::<Vec<_>>(),
        vec![
            rowan::TextRange::new(7.into(), 9.into()),
            rowan::TextRange::new(19.into(), 22.into()),
        ]
    );
}

#[test]
fn test_line_continuations_escaped_backslash() {
    assert_eq!(
        continuations(
            "A = a \\\\\nB = b \\\\\\\n  c\nall:\n\techo \\\\\n\techo \\\\\\\n",
            MakefileVariant::GNUMake
        ),
        vec![
            ("A = a \\\\\nB = b \\\\", "\\\n"),
            (
                "A = a \\\\\nB = b \\\\\\\n  c\nall:\n\techo \\\\\n\techo \\\\",
                "\\\n"
            ),
        ]
    );
    // A backslash at the end of the text does not continue anything.
    assert_eq!(continuations("A = a \\", MakefileVariant::GNUMake), vec![]);
}

#[test]
fn test_line_continuations_crlf() {
    let text = "A = a \\\r\n  b\r\n# c \\\r\n d\r\nall:\r\n\techo \\\r\n\t  e\r\n";
    assert_eq!(
        continuations(text, MakefileVariant::GNUMake)
            .into_iter()
            .map(|(_, c)| c)
            .collect::<Vec<_>>(),
        vec!["\\\r\n", "\\\r\n", "\\\r\n"]
    );
}

#[test]
fn test_line_continuations_define_and_conditional() {
    let text = "define X\na \\\nb\nendef\nifdef Y\nZ = $(subst a \\\n  b,c,d)\nendif\n";
    assert_eq!(
        continuations(text, MakefileVariant::GNUMake),
        vec![
            ("define X\na ", "\\\n"),
            ("define X\na \\\nb\nendef\nifdef Y\nZ = $(subst a ", "\\\n"),
        ]
    );
}

#[test]
fn test_line_continuations_bsd() {
    let text =
        ".for f in a \\\n  b\nX += ${f}\n.endfor\n.if defined(A) || \\\n  defined(B)\n.endif\n";
    assert_eq!(
        continuations(text, MakefileVariant::BSDMake),
        vec![
            (".for f in a ", "\\\n"),
            (
                ".for f in a \\\n  b\nX += ${f}\n.endfor\n.if defined(A) || ",
                "\\\n"
            ),
        ]
    );
}

#[test]
fn test_line_continuations_nmake() {
    let text = "A = x ^\\\nB = y \\\n  z\n";
    assert_eq!(
        continuations(text, MakefileVariant::NMake),
        vec![("A = x ^\\\nB = y ", "\\\n")]
    );
}
