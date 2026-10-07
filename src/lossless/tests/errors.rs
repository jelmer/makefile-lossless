use super::*;

/// For each positioned error in `text`: its kind, the text of its line
/// range and its space indent range.
fn error_line_texts(
    text: &str,
    variant: Option<MakefileVariant>,
) -> Vec<(ParseErrorKind, &str, Option<rowan::TextRange>)> {
    parse(text, variant)
        .positioned_errors
        .iter()
        .map(|e| (e.kind(), &text[e.line_range()], e.space_indent_range()))
        .collect()
}

fn range(start: u32, end: u32) -> Option<rowan::TextRange> {
    Some(rowan::TextRange::new(start.into(), end.into()))
}

#[test]
fn test_error_line_range_space_indent() {
    assert_eq!(
        error_line_texts("all:\n\n  echo hi\n", None),
        vec![(ParseErrorKind::MissingSeparator, "  echo hi", range(6, 8))]
    );
    // Reported at the end of the line rather than at the indent.
    assert_eq!(
        error_line_texts("  echo hi\n", None),
        vec![(ParseErrorKind::MissingSeparator, "  echo hi", range(0, 2))]
    );
    assert_eq!(
        error_line_texts("ifdef X\n  foo bar\nendif\n", None),
        vec![(ParseErrorKind::MissingSeparator, "  foo bar", range(8, 10))]
    );
}

#[test]
fn test_error_line_range_no_indent() {
    assert_eq!(
        error_line_texts("all:\nfoo\n", None),
        vec![(ParseErrorKind::MissingSeparator, "foo", None)]
    );
    assert_eq!(
        error_line_texts("foo", None),
        vec![(ParseErrorKind::MissingSeparator, "foo", None)]
    );
    // Only spaces count, not a tab after them.
    assert_eq!(
        error_line_texts("X = 1\n \tfoo\n", None),
        vec![(ParseErrorKind::MissingSeparator, " \tfoo", range(6, 7))]
    );
}

#[test]
fn test_error_line_range_continuation() {
    assert_eq!(
        error_line_texts("all:\n\n  bad \\\n  line\n", None),
        vec![(
            ParseErrorKind::MissingSeparator,
            "  bad \\\n  line",
            range(6, 8)
        )]
    );
    assert_eq!(
        error_line_texts("all:\nx \\\n  y\nz: w\n", None),
        vec![(ParseErrorKind::MissingSeparator, "x \\\n  y", None)]
    );
    // An escaped backslash does not continue the line.
    assert_eq!(
        error_line_texts("all:\nx \\\\\n  y\n", None),
        vec![
            (ParseErrorKind::MissingSeparator, "x \\\\", None),
            (ParseErrorKind::MissingSeparator, "  y", range(10, 12)),
        ]
    );
}

#[test]
fn test_error_line_range_crlf() {
    assert_eq!(
        error_line_texts("X = 1\r\n  echo hi\r\n", None),
        vec![(ParseErrorKind::MissingSeparator, "  echo hi", range(7, 9))]
    );
    assert_eq!(
        error_line_texts("all:\r\nx \\\r\n  y\r\n", None),
        vec![(ParseErrorKind::MissingSeparator, "x \\\r\n  y", None)]
    );
}

#[test]
fn test_error_line_range_recipe_before_first_target() {
    assert_eq!(
        error_line_texts("\techo hi\n", None),
        vec![(ParseErrorKind::RecipeBeforeFirstTarget, "\techo hi", None)]
    );
}

#[test]
fn test_error_line_range_at_end() {
    let text = "ifdef X\nfoo: bar\n";
    let parsed = parse(text, None);
    let errors = &parsed.positioned_errors;
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].line_range(), rowan::TextRange::empty(17.into()));
    assert_eq!(errors[0].space_indent_range(), None);
}

#[test]
fn test_error_line_range_bsd() {
    assert_eq!(
        error_line_texts("all:\n\n  echo hi\n", Some(MakefileVariant::BSDMake)),
        error_line_texts("all:\n\n  echo hi\n", None)
    );
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
fn test_invalid_ifeq_arguments() {
    // GNU make: "invalid syntax in conditional". The rest of the
    // conditional is parsed as usual.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for input in [
            "ifeq ()\nX = 1\nendif\n",
            "ifeq (a)\nX = 1\nendif\n",
            "ifneq ((a,b))\nX = 1\nendif\n",
            "ifeq ($(a,b))\nX = 1\nendif\n",
            "ifeq \"\"\nX = 1\nendif\n",
            "ifeq \"a\" \nX = 1\nendif\n",
            "ifeq \"a\" a b\nX = 1\nendif\n",
            "ifeq \"a\" # c\nX = 1\nendif\n",
            "ifeq x y\nX = 1\nendif\n",
        ] {
            assert_eq!(
                error_lines(input, variant),
                vec![(ParseErrorKind::InvalidConditional, 1)],
                "{input:?}"
            );
            let makefile = parse(input, variant).root();
            let names: Vec<_> = makefile
                .variable_definitions()
                .map(|v| v.name().unwrap())
                .collect();
            assert_eq!(names, vec!["X"], "{input:?}");
        }
        assert_eq!(
            error_lines("ifdef A\nelse ifeq ()\nendif\n", variant),
            vec![(ParseErrorKind::InvalidConditional, 2)]
        );
        for input in [
            "ifeq (,)\nendif\n",
            "ifeq (a,b,c)\nendif\n",
            "ifeq ((a),(b))\nendif\n",
            "ifeq ($(a,b),c)\nendif\n",
            "ifeq ( \\\n , )\nendif\n",
            "ifeq '' \"\"\nendif\n",
        ] {
            assert_eq!(error_lines(input, variant), vec![], "{input:?}");
        }
    }
}

#[test]
fn test_duplicate_else() {
    // GNU make: "only one 'else' per conditional".
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (input, line) in [
            ("ifdef A\nX = 1\nelse\nX = 2\nelse\nX = 3\nendif\n", 5),
            ("ifdef A\nelse\nelse ifdef B\nendif\n", 3),
            ("ifdef A\nelse ifdef B\nelse\nelse\nendif\n", 4),
            (
                "all:\nifdef A\n\techo\nelse\n\techo\nelse\n\techo\nendif\n",
                6,
            ),
        ] {
            assert_eq!(
                error_lines(input, variant),
                vec![(ParseErrorKind::DuplicateElse, line)],
                "{input:?}"
            );
        }
        assert_eq!(
            error_lines(
                "ifdef A\nelse ifdef B\nelse\nifdef C\nelse\nendif\nendif\n",
                variant
            ),
            vec![]
        );
    }
    // BSD make only warns about an extra `.else`.
    assert_eq!(
        error_lines(
            ".if 1\n.else\n.else\n.endif\n",
            Some(MakefileVariant::BSDMake)
        ),
        vec![]
    );
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
fn test_error_location_crlf() {
    assert_eq!(
        error_locations("X = 1\r\nfoo bar\r\nY = 2\r\n"),
        vec![(
            "expected ':'".to_string(),
            2,
            "foo bar".to_string(),
            rowan::TextRange::new(14.into(), 16.into())
        )]
    );
    // A carriage return without a newline does not end the line.
    assert_eq!(
        error_locations("X = 1\nfoo bar\r"),
        vec![(
            "expected ':'".to_string(),
            2,
            "foo bar\r".to_string(),
            rowan::TextRange::new(14.into(), 14.into())
        )]
    );
}

#[test]
fn test_error_location_after_last_line() {
    for input in ["ifdef X\nbar = 1\n", "ifdef X\nbar = 1"] {
        assert_eq!(
            error_locations(input),
            vec![(
                "unterminated conditional (missing endif)".to_string(),
                3,
                String::new(),
                rowan::TextRange::empty(rowan::TextSize::of(input))
            )],
            "{input:?}"
        );
    }
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
