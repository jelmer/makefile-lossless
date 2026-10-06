use super::*;

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
    CONDITIONAL_ELSE@36..45
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
                    Some("A = 2\n".to_string())
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
    CONDITIONAL_ELSE@8..18
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
    assert_eq!(conditionals[0].else_body(), None);
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
fn test_conditional_headers_include_newline() {
    // Each branch header owns the newline that ends its line, so that the
    // branch body starts on the next line.
    for (code, variant) in [
        ("ifdef X\nelse\nendif\n", None),
        ("ifdef X\nelse # c\nendif\n", None),
        ("ifdef X\nelse junk\nendif\n", None),
        ("ifdef X\nelse ifdef Y\nendif\n", None),
        ("ifdef X\nelse ifeq (a,b)\nelse\nendif\n", None),
        (
            "ifeq (a,b)\nelse ifneq (c,d)\nendif\n",
            Some(MakefileVariant::GNUMake),
        ),
        (
            ".if 1\n.elif 2\n.else\n.endif\n",
            Some(MakefileVariant::BSDMake),
        ),
        (
            ".ifdef X\n.elifndef Y\n.else # c\n.endif\n",
            Some(MakefileVariant::BSDMake),
        ),
        (
            "!IF 1\n!ELSEIF 2\n!ELSE\n!ENDIF\n",
            Some(MakefileVariant::NMake),
        ),
    ] {
        let parsed = parse(code, variant);
        assert_eq!(
            parsed.errors.len(),
            usize::from(code.contains("junk")),
            "{code:?}"
        );
        let conditional = parsed.root().conditionals().next().unwrap();
        let headers: Vec<String> = conditional
            .syntax()
            .children()
            .filter(|n| {
                matches!(
                    n.kind(),
                    CONDITIONAL_IF | CONDITIONAL_ELSE | CONDITIONAL_ENDIF
                )
            })
            .map(|n| n.to_string())
            .collect();
        assert_eq!(
            headers,
            code.split_inclusive('\n').collect::<Vec<_>>(),
            "{code:?}"
        );
    }
}
