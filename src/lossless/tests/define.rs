use super::*;

#[test]
fn test_define_endef() {
    let code = "define greeting\n\techo hello\n\techo world\nendef\n\nall:\n\t$(greeting)\n";
    let makefile: Makefile = code.parse().expect("define/endef should parse");
    assert_eq!(code, makefile.to_string());
    assert_eq!(1, makefile.rules().count());
}

#[test]
fn test_define_endef_nested() {
    let code = "define outer\ndefine inner\nbody\nendef\nendef\n";
    let makefile: Makefile = code.parse().expect("nested define/endef should parse");
    assert_eq!(code, makefile.to_string());
}

fn assert_define(item: MakefileItem, name: &str, value: &str) {
    let MakefileItem::Variable(var) = item else {
        panic!("expected a variable, got {:?}", item.syntax());
    };
    assert!(var.is_define());
    assert_eq!(Some(name.to_string()), var.name());
    assert_eq!(Some(value.to_string()), var.raw_value());
}

#[test]
fn test_define_in_conditional() {
    let code = "ifdef X\ndefine FOO\nbody\nendef\nelse\ndefine BAR :=\nother\nendef\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(0, makefile.rules().count());
    let cond = makefile.conditionals().next().unwrap();
    let if_items: Vec<_> = cond.if_items().collect();
    assert_eq!(1, if_items.len());
    assert_define(if_items[0].clone(), "FOO", "body\n");
    let else_items: Vec<_> = cond.else_items().collect();
    assert_eq!(1, else_items.len());
    assert_define(else_items[0].clone(), "BAR", "other\n");
}

#[test]
fn test_define_in_nested_conditional() {
    let code = "ifdef X\nifeq ($(Y),1)\ndefine FOO\nbody\nendef\nendif\nendif\n";
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
    assert_define(inner_items[0].clone(), "FOO", "body\n");
}

#[test]
fn test_define_in_conditional_with_directive_lines() {
    // Conditional directives inside a define body are part of its value.
    let code = "ifdef X\ndefine FOO\nifdef Y\na\nelse\nb\nendif\nendef\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let cond = makefile.conditionals().next().unwrap();
    assert!(!cond.has_else());
    let if_items: Vec<_> = cond.if_items().collect();
    assert_eq!(1, if_items.len());
    assert_define(if_items[0].clone(), "FOO", "ifdef Y\na\nelse\nb\nendif\n");
}

#[test]
fn test_define_in_conditional_in_rule() {
    let code = "all:\n\techo hi\nifdef X\ndefine FOO\nbody\nendef\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(1, makefile.rules().count());
    let defines: Vec<_> = makefile
        .syntax()
        .descendants()
        .filter_map(VariableDefinition::cast)
        .collect();
    assert_eq!(1, defines.len());
    assert_define(MakefileItem::Variable(defines[0].clone()), "FOO", "body\n");
}

#[test]
fn test_define_name_with_backslash() {
    // devscripts defines a newline helper this way.
    let code = "define \\n\n\n\nendef\n";
    let makefile: Makefile = code.parse().unwrap();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len());
    assert_eq!(Some("\\n".to_string()), vars[0].name());
    assert!(vars[0].is_define());
    assert_eq!(None, vars[0].assignment_operator());
    assert_eq!(Some("\n\n".to_string()), vars[0].raw_value());
}

#[test]
fn test_define_name_with_backslash_and_operator() {
    let code = "define a\\b :=\nbody\nendef\n";
    let makefile: Makefile = code.parse().unwrap();
    assert_eq!(code, makefile.to_string());
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(Some("a\\b".to_string()), var.name());
    assert_eq!(Some(":=".to_string()), var.assignment_operator());
    assert_eq!(Some("body\n".to_string()), var.raw_value());
}

#[test]
fn test_define_continuation_before_operator() {
    for (code, name, op, value) in [
        ("define W \\\n =\nhi\nendef\n", "W", "=", "hi\n"),
        ("define W\\\r\n:=\r\nhi\r\nendef\r\n", "W", ":=", "hi\n"),
        ("define a\\\\ \\\n =\nhi\nendef\n", "a\\\\", "=", "hi\n"),
        ("export \\\n define W \\\n =\nhi\nendef\n", "W", "=", "hi\n"),
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let makefile = parsed.root();
        assert_eq!(code, makefile.to_string());
        let vars = makefile
            .variable_definitions()
            .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
            .collect::<Vec<_>>();
        assert_eq!(
            vars,
            vec![(
                Some(name.to_string()),
                Some(op.to_string()),
                Some(value.to_string())
            )],
            "{code:?}"
        );
    }
}

#[test]
fn test_escaped_backslash_before_operator_line() {
    // An escaped backslash at the end of the line does not continue it,
    // so the `=` on the next line is not the operator.
    let code = "define a\\\\\n= 1\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars = makefile
        .variable_definitions()
        .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
        .collect::<Vec<_>>();
    assert_eq!(
        vars,
        vec![(Some("a\\\\".to_string()), None, Some("= 1\n".to_string()))]
    );

    // GNU make reports a missing separator here.
    let parsed = parse("a\\\\\n= 1\n", Some(MakefileVariant::GNUMake));
    assert_eq!(parsed.root().variable_definitions().count(), 0);
}

#[test]
fn test_define_name_with_spaces() {
    // GNU make takes the whole header up to the operator as the name.
    let code = "define foo bar \nbody\nendef\n";
    let makefile: Makefile = code.parse().unwrap();
    assert_eq!(code, makefile.to_string());
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(Some("foo bar".to_string()), var.name());
    assert_eq!(Some("body\n".to_string()), var.raw_value());
}

#[test]
fn test_define_name_with_continuation() {
    // GNU make reads the whole header, so a continuation and the
    // whitespace around it become a single space in the name.
    for (code, name, op) in [
        ("define A \\\nB\nbody\nendef\n", "A B", None),
        ("define A\\\nB\nbody\nendef\n", "A B", None),
        ("define A \\\n  B  \\\n  C\nbody\nendef\n", "A B C", None),
        ("define $(x) \\\n B\nbody\nendef\n", "$(x) B", None),
        ("define A \\\nB :=\nbody\nendef\n", "A B :=", None),
        ("define A \\\nB # c\nbody\nendef\n", "A B", None),
        ("define A \\\n=\nbody\nendef\n", "A", Some("=")),
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let makefile = parsed.root();
        assert_eq!(code, makefile.to_string());
        let vars = makefile
            .variable_definitions()
            .map(|v| {
                (
                    v.name(),
                    v.names().collect::<Vec<_>>(),
                    v.assignment_operator(),
                    v.raw_value(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            vars,
            vec![(
                Some(name.to_string()),
                vec![name.to_string()],
                op.map(str::to_string),
                Some("body\n".to_string())
            )],
            "{code:?}"
        );
    }
}

#[test]
fn test_define_multiword_name_with_operator() {
    // GNU make only recognises an operator after a single word; in
    // `define A B =` the variable is "A B =".
    for (code, name, op) in [
        ("define A B =\nbody\nendef\n", "A B =", None),
        ("define A B := x\nbody\nendef\n", "A B := x", None),
        ("define A =\nbody\nendef\n", "A", Some("=")),
        (
            "define $(subst _, ,A_B) =\nbody\nendef\n",
            "$(subst _, ,A_B)",
            Some("="),
        ),
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        let makefile = parsed.root();
        assert_eq!(code, makefile.to_string());
        let vars = makefile
            .variable_definitions()
            .map(|v| (v.name(), v.assignment_operator(), v.raw_value()))
            .collect::<Vec<_>>();
        assert_eq!(
            vars,
            vec![(
                Some(name.to_string()),
                op.map(str::to_string),
                Some("body\n".to_string())
            )],
            "{code:?}"
        );
    }
}

#[test]
fn test_define_name_with_continuation_modifiers() {
    // Words after `define` are part of the name, not modifiers.
    let code = "override define override \\\n X\nbody\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_define());
    assert!(var.is_override());
    assert_eq!(var.name(), Some("override X".to_string()));
}

#[test]
fn test_define_name_reference_tree() {
    let code = "define $(PREFIX)_FLAGS :=\n$(B)\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r##"ROOT@0..37
  VARIABLE@0..37
    IDENTIFIER@0..6 "define"
    WHITESPACE@6..7 " "
    EXPR@7..16
      DOLLAR@7..8 "$"
      LPAREN@8..9 "("
      IDENTIFIER@9..15 "PREFIX"
      RPAREN@15..16 ")"
    IDENTIFIER@16..22 "_FLAGS"
    WHITESPACE@22..23 " "
    OPERATOR@23..25 ":="
    NEWLINE@25..26 "\n"
    EXPR@26..31
      EXPR@26..30
        DOLLAR@26..27 "$"
        LPAREN@27..28 "("
        IDENTIFIER@28..29 "B"
        RPAREN@29..30 ")"
      NEWLINE@30..31 "\n"
    IDENTIFIER@31..36 "endef"
    NEWLINE@36..37 "\n"
"##
    );
    assert_eq!(code, parsed.root().to_string());
}

#[test]
fn test_define_header_comment() {
    // make drops a comment on the define header line but keeps `#` in
    // the body.
    let code = "define foo # c\nbody # x\nendef\n";
    let parsed = parse(code, None);
    assert!(parsed.errors.is_empty());
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r##"ROOT@0..30
  VARIABLE@0..30
    IDENTIFIER@0..6 "define"
    WHITESPACE@6..7 " "
    IDENTIFIER@7..10 "foo"
    WHITESPACE@10..11 " "
    COMMENT@11..14 "# c"
    NEWLINE@14..15 "\n"
    EXPR@15..24
      IDENTIFIER@15..19 "body"
      WHITESPACE@19..20 " "
      COMMENT@20..23 "# x"
      NEWLINE@23..24 "\n"
    IDENTIFIER@24..29 "endef"
    NEWLINE@29..30 "\n"
"##
    );
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len());
    assert_eq!(Some("foo".to_string()), vars[0].name());
    assert_eq!(Some("body # x\n".to_string()), vars[0].raw_value());
}

#[test]
fn test_define_header_comment_after_operator() {
    let code = "define foo := # c\nb2\nendef\n";
    let makefile: Makefile = code.parse().expect("define with comment should parse");
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len());
    assert_eq!(Some("foo".to_string()), vars[0].name());
    assert_eq!(Some(":=".to_string()), vars[0].assignment_operator());
    assert_eq!(Some("b2\n".to_string()), vars[0].raw_value());
}

/// Parse a makefile with a single define named "A", returning the
/// errors as (kind, line) pairs and the operator and raw value of A.
fn parse_single_define(
    code: &str,
    variant: Option<MakefileVariant>,
) -> (Vec<(ParseErrorKind, usize)>, Option<String>, Option<String>) {
    let parsed = parse(code, variant);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(1, vars.len(), "{code:?}");
    assert_eq!(Some("A".to_string()), vars[0].name(), "{code:?}");
    (
        parsed.errors.iter().map(|e| (e.kind(), e.line)).collect(),
        vars[0].assignment_operator(),
        vars[0].raw_value(),
    )
}

#[test]
fn test_define_extraneous_text_after_operator() {
    // GNU make: "extraneous text after 'define' directive". The text is
    // not part of the value.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (code, op, line) in [
            ("define A =x\nfoo\nendef\n", "=", 1),
            ("define A = x\nfoo\nendef\n", "=", 1),
            ("define A=x\nfoo\nendef\n", "=", 1),
            ("define A ::= $(B) # c\nfoo\nendef\n", "::=", 1),
            ("override define A +=x\nfoo\nendef\n", "+=", 1),
            ("define A = \\\nbar\nfoo\nendef\n", "=", 2),
            ("define A = x \\\nbar\nfoo\nendef\n", "=", 1),
        ] {
            assert_eq!(
                parse_single_define(code, variant),
                (
                    vec![(ParseErrorKind::ExtraneousText, line)],
                    Some(op.to_string()),
                    Some("foo\n".to_string())
                ),
                "{code:?}"
            );
        }
    }
}

#[test]
fn test_define_no_extraneous_text_after_operator() {
    for code in [
        "define A := # c\nfoo\nendef\n",
        "define A =  \nfoo\nendef\n",
        "define A = \\\n# c\nfoo\nendef\n",
        "define A = \\\n\nfoo\nendef\n",
        "define A = \\\n  \nfoo\nendef\n",
    ] {
        let (errors, _, value) = parse_single_define(code, None);
        assert_eq!(
            (errors, value),
            (vec![], Some("foo\n".to_string())),
            "{code:?}"
        );
    }
}

#[test]
fn test_endef_extraneous_text() {
    // GNU make: "extraneous text after 'endef' directive". The line still
    // ends the define.
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        for (code, line) in [
            ("define A\nfoo\nendef junk\n", 3),
            ("define A\nfoo\nendef $(X)\n", 3),
            ("define A\nfoo\nendef junk # c\n", 3),
            ("define A\nfoo\nendef \\\nbar\n", 4),
        ] {
            assert_eq!(
                parse_single_define(code, variant),
                (
                    vec![(ParseErrorKind::ExtraneousText, line)],
                    None,
                    Some("foo\n".to_string())
                ),
                "{code:?}"
            );
        }
    }
}

#[test]
fn test_endef_no_extraneous_text() {
    for code in [
        "define A\nfoo\nendef # c\n",
        "define A\nfoo\nendef\t# c\n",
        "define A\nfoo\nendef  \n",
        "define A\nfoo\nendef \\\n\n",
        "define A\nfoo\nendef \\\n# c\n",
        "define A\nfoo\nendef",
    ] {
        assert_eq!(
            parse_single_define(code, None),
            (vec![], None, Some("foo\n".to_string())),
            "{code:?}"
        );
    }
}

#[test]
fn test_nested_endef_extraneous_text() {
    // make also checks the `endef` of a define nested in the body, which
    // stays part of the value.
    let code = "define A\ndefine B\nfoo\nendef junk\nendef\n";
    assert_eq!(
        parse_single_define(code, None),
        (
            vec![(ParseErrorKind::ExtraneousText, 4)],
            None,
            Some("define B\nfoo\nendef junk\n".to_string())
        )
    );
}

#[test]
fn test_define_body_keyword_needs_separator() {
    // In a define body make only recognises `define` and `endef` when
    // followed by whitespace or the end of the line.
    for (code, value) in [
        ("define A\nfoo\nendef#c\nendef\n", "foo\nendef#c\n"),
        ("define A\nfoo\nendef=x\nendef\n", "foo\nendef=x\n"),
        ("define A\nfoo\nendef$(X)\nendef\n", "foo\nendef$(X)\n"),
        ("define A\nfoo\n endef#c\nendef\n", "foo\n endef#c\n"),
        ("define A\ndefine#c\nfoo\nendef\n", "define#c\nfoo\n"),
        ("define A\ndefine=x\nfoo\nendef\n", "define=x\nfoo\n"),
        ("define A\nfoo\nendef\t# c\n", "foo\n"),
    ] {
        assert_eq!(
            parse_single_define(code, None),
            (vec![], None, Some(value.to_string())),
            "{code:?}"
        );
    }
    let parsed = parse("define A\nfoo\nendef#c\n", None);
    assert_eq!(
        parsed.errors.iter().map(|e| e.kind()).collect::<Vec<_>>(),
        vec![ParseErrorKind::MissingEndef]
    );
    // A line continuation separates the keyword from what follows.
    assert_eq!(
        parse_single_define("define A\nfoo\nendef\\\nbar\n", None),
        (
            vec![(ParseErrorKind::ExtraneousText, 4)],
            None,
            Some("foo\n".to_string())
        )
    );
}

#[test]
fn test_define_body_line_continuation() {
    // make joins continued lines in a define body before looking for
    // `define` and `endef`, so a continued line swallows a following
    // `endef` line.
    for code in [
        "define A\nx \\\nendef\n",
        "define A\n\tx \\\nendef\n",
        "define A\nx \\\nendef # c\n",
        "define A\nx \\\\\\\nendef\n",
        "define A\ndefine B \\\nendef\nendef\n",
    ] {
        assert_eq!(
            parse_single_define(code, None),
            (
                vec![(ParseErrorKind::MissingEndef, 1)],
                None,
                Some(code["define A\n".len()..].to_string())
            ),
            "{code:?}"
        );
    }
    for (code, value) in [
        ("define A\nx \\\nendef\nendef\n", "x \\\nendef\n"),
        ("define A\nx \\\\\nendef\n", "x \\\\\n"),
        ("define A\nx \\\ny\nendef\n", "x \\\ny\n"),
    ] {
        assert_eq!(
            parse_single_define(code, None),
            (vec![], None, Some(value.to_string())),
            "{code:?}"
        );
    }
}

#[test]
fn test_directive_followed_by_comment() {
    // Outside a define body make strips comments first, so `endif#c` is
    // still `endif`.
    for code in [
        "ifdef X\nA = 1\nendif#c\n",
        "ifdef X\nA = 1\nelse#c\nA = 2\nendif\n",
    ] {
        let parsed = parse(code, None);
        assert_eq!(parsed.errors, vec![], "{code:?}");
        assert_eq!(code, parsed.root().to_string());
    }
    assert_eq!(
        error_kinds("define#c\nendef\n", None),
        vec![ParseErrorKind::ExpectedVariableName]
    );
    assert_eq!(
        error_kinds("endif#c\n", None),
        vec![ParseErrorKind::ExtraneousEndif]
    );
    assert_eq!(
        error_kinds("else#c\n", None),
        vec![ParseErrorKind::ElseWithoutIf]
    );
}

#[test]
fn test_define_extraneous_text_tree() {
    let code = "define A = x\nfoo\nendef y\n";
    let parsed = parse(code, None);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r##"ROOT@0..25
  VARIABLE@0..25
    IDENTIFIER@0..6 "define"
    WHITESPACE@6..7 " "
    IDENTIFIER@7..8 "A"
    WHITESPACE@8..9 " "
    OPERATOR@9..10 "="
    WHITESPACE@10..11 " "
    ERROR@11..12
      IDENTIFIER@11..12 "x"
    NEWLINE@12..13 "\n"
    EXPR@13..17
      IDENTIFIER@13..16 "foo"
      NEWLINE@16..17 "\n"
    IDENTIFIER@17..22 "endef"
    WHITESPACE@22..23 " "
    ERROR@23..24
      IDENTIFIER@23..24 "y"
    NEWLINE@24..25 "\n"
"##
    );
}

#[test]
fn test_define_with_modifiers() {
    let code = "override define FOO :=\nbody\nendef\nexport define BAR\nline\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(0, makefile.rules().count());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(2, vars.len());

    assert!(vars[0].is_define());
    assert!(vars[0].is_override());
    assert!(!vars[0].is_export());
    assert_eq!(Some("FOO".to_string()), vars[0].name());
    assert_eq!(Some(":=".to_string()), vars[0].assignment_operator());
    assert_eq!(Some("body\n".to_string()), vars[0].raw_value());

    assert!(vars[1].is_define());
    assert!(!vars[1].is_override());
    assert!(vars[1].is_export());
    assert_eq!(Some("BAR".to_string()), vars[1].name());
    assert_eq!(None, vars[1].assignment_operator());
    assert_eq!(Some("line\n".to_string()), vars[1].raw_value());
}

#[test]
fn test_define_with_combined_modifiers() {
    let code = "override export define OE =\nx\nendef\nprivate define P\ny\nendef\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(2, vars.len());

    assert!(vars[0].is_define());
    assert!(vars[0].is_override());
    assert!(vars[0].is_export());
    assert_eq!(Some("OE".to_string()), vars[0].name());
    assert_eq!(Some("=".to_string()), vars[0].assignment_operator());
    assert_eq!(Some("x\n".to_string()), vars[0].raw_value());

    assert!(vars[1].is_define());
    assert!(!vars[1].is_override());
    assert!(!vars[1].is_export());
    assert_eq!(Some("P".to_string()), vars[1].name());
    assert_eq!(Some("y\n".to_string()), vars[1].raw_value());
}

#[test]
fn test_modifier_keyword_as_variable_name() {
    let makefile: Makefile = "private = 1\n".parse().unwrap();
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(Some("private".to_string()), vars[0].name());
}

#[test]
fn test_define_with_modifier_in_conditional() {
    let code = "ifdef X\noverride define FOO\nbody\nendef\nendif\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    assert_eq!(0, makefile.rules().count());
    let cond = makefile.conditionals().next().unwrap();
    let if_items: Vec<_> = cond.if_items().collect();
    assert_eq!(1, if_items.len());
    let MakefileItem::Variable(var) = &if_items[0] else {
        panic!("expected a variable, got {:?}", if_items[0].syntax());
    };
    assert!(var.is_define());
    assert!(var.is_override());
    assert_eq!(Some("FOO".to_string()), var.name());
    assert_eq!(Some("body\n".to_string()), var.raw_value());
}

#[test]
fn test_private_define_and_private_assignment() {
    let code = "private define X\nbody\nendef\nprivate Y = 1\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(code, makefile.to_string());
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(2, vars.len());
    assert!(vars[0].is_define());
    assert_eq!(Some("X".to_string()), vars[0].name());
    assert!(!vars[1].is_define());
    assert_eq!(Some("Y".to_string()), vars[1].name());
    assert_eq!(Some("1".to_string()), vars[1].raw_value());
}

#[test]
fn test_undefine() {
    let text = "FOO = 1\nundefine FOO\nall:\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 2);
    assert!(!vars[0].is_undefine());
    assert!(vars[1].is_undefine());
    assert!(!vars[1].is_override());
    assert_eq!(vars[1].name(), Some("FOO".to_string()));
    assert_eq!(vars[1].assignment_operator(), None);
    assert_eq!(vars[1].raw_value(), None);
    assert_eq!(makefile.rules().count(), 1);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_override_undefine() {
    let text = "override undefine FOO\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert!(vars[0].is_undefine());
    assert!(vars[0].is_override());
    assert_eq!(vars[0].name(), Some("FOO".to_string()));
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_variable_reference() {
    let text = "undefine $(NAME)\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert!(vars[0].is_undefine());
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_computed_name() {
    let text = "override undefine CFLAGS.${PROG}\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_undefine());
    assert!(var.is_override());
    assert_eq!(var.name(), Some("CFLAGS.${PROG}".to_string()));
    assert_eq!(var.raw_value(), None);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_at_eof() {
    let text = "undefine FOO";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.variable_definitions().count(), 1);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_name_with_spaces() {
    // GNU make takes the rest of the line as a single name, keeping
    // internal whitespace.
    let text = "undefine A  B\noverride undefine B C # c\nundefine X \n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 3);
    assert!(vars[0].is_undefine());
    assert!(!vars[0].is_override());
    assert_eq!(vars[0].name(), Some("A  B".to_string()));
    assert_eq!(vars[0].names().collect::<Vec<_>>(), vec!["A  B"]);
    assert!(vars[1].is_undefine());
    assert!(vars[1].is_override());
    assert_eq!(vars[1].name(), Some("B C".to_string()));
    assert_eq!(vars[1].names().collect::<Vec<_>>(), vec!["B C"]);
    assert_eq!(vars[2].name(), Some("X".to_string()));
    assert_eq!(vars[2].names().collect::<Vec<_>>(), vec!["X"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_name_with_continuation() {
    // The continuation and surrounding whitespace become a single space.
    let text = "undefine A \\\n  $(B)\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_undefine());
    assert_eq!(var.name(), Some("A $(B)".to_string()));
    assert_eq!(var.names().collect::<Vec<_>>(), vec!["A $(B)"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_name_starting_with_keyword() {
    // Words after `undefine` are part of the name, not modifiers.
    let text = "undefine override X\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_undefine());
    assert!(!var.is_override());
    assert_eq!(var.name(), Some("override X".to_string()));
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_as_rule_target() {
    let text = "undefine:\n\techo hi\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.variable_definitions().count(), 0);
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["undefine"]);
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_as_variable_name() {
    let text = "undefine = 1\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert!(!vars[0].is_undefine());
    assert_eq!(vars[0].name(), Some("undefine".to_string()));
    assert_eq!(vars[0].raw_value(), Some("1".to_string()));
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_with_comment() {
    let text = "undefine FOO # gone\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert!(var.is_undefine());
    assert_eq!(var.name(), Some("FOO".to_string()));
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_undefine_empty_name() {
    for text in [
        "undefine\n",
        "undefine",
        "undefine # c\n",
        "override undefine\n",
        "override undefine \\\n\n",
    ] {
        let parsed = parse(text, None);
        assert_eq!(
            parsed
                .errors
                .iter()
                .map(|e| e.message.as_str())
                .collect::<Vec<_>>(),
            vec!["empty variable name"],
            "{text:?}"
        );
        assert_eq!(
            parsed.errors.iter().map(|e| e.kind()).collect::<Vec<_>>(),
            vec![ParseErrorKind::ExpectedVariableName],
            "{text:?}"
        );
        let makefile = parsed.root();
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1, "{text:?}");
        assert!(vars[0].is_undefine(), "{text:?}");
        assert_eq!(vars[0].name(), None, "{text:?}");
        assert_eq!(vars[0].names().collect::<Vec<_>>(), Vec::<String>::new());
        assert_eq!(makefile.code(), text);
    }
}

#[test]
fn test_undefine_name_with_operator() {
    // GNU make accepts these silently, undefining "A = b" and so on.
    let text = "undefine A = b\nundefine A: b\noverride undefine X := $(Y)\n";
    let parsed = parse(text, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.rules().count(), 0);
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 3);
    for (var, name) in vars.iter().zip(["A = b", "A: b", "X := $(Y)"]) {
        assert!(var.is_undefine());
        assert_eq!(var.name(), Some(name.to_string()));
        assert_eq!(var.names().collect::<Vec<_>>(), vec![name]);
        assert_eq!(var.assignment_operator(), None);
        assert_eq!(var.raw_value(), None);
    }
    assert!(vars[2].is_override());
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_define_undefine_gnu_only() {
    for variant in [
        MakefileVariant::POSIXMake,
        MakefileVariant::NMake,
        MakefileVariant::BSDMake,
    ] {
        for text in ["undefine A B\n", "undefine A\n", "define FOO\nbar\nendef\n"] {
            let parsed = parse(text, Some(variant));
            assert_eq!(
                parsed
                    .errors
                    .iter()
                    .map(|e| e.message.as_str())
                    .collect::<Vec<_>>(),
                vec!["expected ':'"; text.lines().count()],
                "{variant:?} {text:?}"
            );
            let makefile = parsed.root();
            assert_eq!(makefile.variable_definitions().count(), 0);
            assert_eq!(makefile.code(), text);
        }
    }
    // GNU make and the default
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let text = "undefine A B\ndefine FOO\nbar\nendef\n";
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 2);
        assert!(vars[0].is_undefine());
        assert!(vars[1].is_define());
    }
}

#[test]
fn test_assignment_modifiers_gnu_only() {
    let text = "override X = 1\nunexport X\nprivate X = 1\nexport X\nexport\n";
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
            vec!["expected ':'"; 5],
            "{variant:?}"
        );
        assert_eq!(parsed.root().variable_definitions().count(), 0);
        assert_eq!(parsed.root().code(), text);
    }
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        assert_eq!(parsed.root().variable_definitions().count(), 5);
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_modifier_keyword_as_variable_name_any_variant() {
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ] {
        let text = "override = 1\nexport = 2\n";
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        assert_eq!(
            parsed
                .root()
                .variable_definitions()
                .map(|v| v.name())
                .collect::<Vec<_>>(),
            vec![Some("override".to_string()), Some("export".to_string())],
            "{variant:?}"
        );
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_bsd_undef_unaffected() {
    let text = ".undef A B\n";
    let parsed = parse(text, Some(MakefileVariant::BSDMake));
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(parsed.root().code(), text);
}

#[test]
fn test_define_as_variable_name() {
    for variant in [
        None,
        Some(MakefileVariant::GNUMake),
        Some(MakefileVariant::BSDMake),
        Some(MakefileVariant::POSIXMake),
        Some(MakefileVariant::NMake),
    ] {
        let text = "define = 1\n";
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1, "{variant:?}");
        assert!(!vars[0].is_define(), "{variant:?}");
        assert_eq!(vars[0].name(), Some("define".to_string()), "{variant:?}");
        assert_eq!(vars[0].raw_value(), Some("1".to_string()), "{variant:?}");
        assert_eq!(parsed.root().code(), text);
    }
    for variant in [None, Some(MakefileVariant::GNUMake)] {
        let text = "override define := 1\nexport define = 2\n";
        let parsed = parse(text, variant);
        assert_eq!(parsed.errors, vec![], "{variant:?}");
        let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 2, "{variant:?}");
        assert!(vars[0].is_override());
        assert!(vars[1].is_export());
        for var in &vars {
            assert!(!var.is_define(), "{variant:?}");
            assert_eq!(var.name(), Some("define".to_string()), "{variant:?}");
        }
        assert_eq!(parsed.root().code(), text);
    }
}

#[test]
fn test_define_names() {
    let parsed = parse("define FOO\nbar baz\nendef\n", None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.names().collect::<Vec<_>>(), vec!["FOO"]);
}

#[test]
fn test_undefine_names() {
    let parsed = parse("undefine FOO\noverride undefine BAR\n", None);
    assert_eq!(parsed.errors, vec![]);
    let vars = parsed.root().variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars[0].names().collect::<Vec<_>>(), vec!["FOO"]);
    assert_eq!(vars[1].names().collect::<Vec<_>>(), vec!["BAR"]);
}
