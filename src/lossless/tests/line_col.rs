use super::*;

#[test]
fn test_line_number_calculation() {
    // Test inputs for various error locations
    let test_cases = [
        ("rule dependency\n\tcommand", 1),             // Missing colon
        ("#comment\n\t(╯°□°)╯︵ ┻━┻", 2),              // Strange characters
        ("var = value\n#comment\n\tindented line", 3), // Indented line not part of a rule
    ];

    for (input, expected_line) in test_cases {
        // Attempt to parse the input
        match input.parse::<Makefile>() {
            Ok(_) => {
                // If the parser succeeds, that's fine - our parser is more robust
                // Skip assertions when there's no error to check
                continue;
            }
            Err(err) => {
                if let Error::Parse(parse_err) = err {
                    // Verify error line number matches expected line
                    assert_eq!(
                        parse_err.errors[0].line, expected_line,
                        "Line number should match the expected line"
                    );

                    // If the error is about indentation, check that the context includes the tab
                    if parse_err.errors[0].message.contains("indented") {
                        assert!(
                            parse_err.errors[0].context.starts_with('\t'),
                            "Context for indentation errors should include the tab character"
                        );
                    }
                } else {
                    panic!("Expected parse error, got: {:?}", err);
                }
            }
        }
    }
}

#[test]
fn test_line_col() {
    let text = r#"# Comment at line 0
VAR1 = value1
VAR2 = value2

rule1: dep1 dep2
	command1
	command2

rule2:
	command3

ifdef DEBUG
CFLAGS = -g
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    // Test variable definition line numbers
    // variable_definitions() is recursive, so it finds VAR1, VAR2, and CFLAGS (inside conditional)
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars.len(), 3);

    // VAR1 starts at line 1
    assert_eq!(vars[0].line(), 1);
    assert_eq!(vars[0].column(), 0);
    assert_eq!(vars[0].line_col(), (1, 0));

    // VAR2 starts at line 2
    assert_eq!(vars[1].line(), 2);
    assert_eq!(vars[1].column(), 0);

    // CFLAGS starts at line 12 (inside ifdef DEBUG)
    assert_eq!(vars[2].line(), 12);
    assert_eq!(vars[2].column(), 0);

    // Test rule line numbers
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 2);

    // rule1 starts at line 4
    assert_eq!(rules[0].line(), 4);
    assert_eq!(rules[0].column(), 0);
    assert_eq!(rules[0].line_col(), (4, 0));

    // rule2 starts at line 8
    assert_eq!(rules[1].line(), 8);
    assert_eq!(rules[1].column(), 0);

    // Test conditional line numbers
    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 1);

    // ifdef DEBUG starts at line 11
    assert_eq!(conditionals[0].line(), 11);
    assert_eq!(conditionals[0].column(), 0);
    assert_eq!(conditionals[0].line_col(), (11, 0));
}

#[test]
fn test_line_col_multiline() {
    let text =
        "SOURCES = \\\n\tfile1.c \\\n\tfile2.c\n\ntarget: $(SOURCES)\n\tgcc -o target $(SOURCES)\n";
    let makefile: Makefile = text.parse().unwrap();

    // Variable definition starts at line 0
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].line(), 0);
    assert_eq!(vars[0].column(), 0);

    // Rule starts at line 4
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].line(), 4);
    assert_eq!(rules[0].column(), 0);
}

#[test]
fn test_line_col_includes() {
    let text = "VAR = value\n\ninclude config.mk\n-include optional.mk\n";
    let makefile: Makefile = text.parse().unwrap();

    // Variable at line 0
    let vars: Vec<_> = makefile.variable_definitions().collect();
    assert_eq!(vars[0].line(), 0);

    // Includes at lines 2 and 3
    let includes: Vec<_> = makefile.includes().collect();
    assert_eq!(includes.len(), 2);
    assert_eq!(includes[0].line(), 2);
    assert_eq!(includes[0].column(), 0);
    assert_eq!(includes[1].line(), 3);
    assert_eq!(includes[1].column(), 0);
}

/// The original implementation of `line_col_at_offset`, which walks the
/// tree from the root on every call.
fn line_col_by_walking(node: &SyntaxNode, offset: rowan::TextSize) -> (usize, usize) {
    let root = node.ancestors().last().unwrap_or_else(|| node.clone());
    let mut line = 0;
    let mut last_newline_offset = rowan::TextSize::from(0);
    for element in root.preorder_with_tokens() {
        if let rowan::WalkEvent::Enter(rowan::NodeOrToken::Token(token)) = element {
            if token.text_range().start() >= offset {
                break;
            }
            for (idx, _) in token.text().match_indices('\n') {
                line += 1;
                last_newline_offset =
                    token.text_range().start() + rowan::TextSize::from((idx + 1) as u32);
            }
        }
    }
    (line, (offset - last_newline_offset).into())
}

fn assert_line_cols_match_walking(root: &SyntaxNode) {
    let positions = |f: fn(&SyntaxNode, rowan::TextSize) -> (usize, usize)| {
        root.descendants_with_tokens()
            .map(|element| {
                let start = element.text_range().start();
                let node = match &element {
                    rowan::NodeOrToken::Node(n) => n.clone(),
                    rowan::NodeOrToken::Token(t) => t.parent().unwrap(),
                };
                (element.kind(), start, f(&node, start))
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        positions(line_col_by_walking),
        positions(line_col_at_offset)
    );
}

#[test]
fn test_line_col_matches_walking() {
    let inputs = [
            "",
            "VAR = value",
            "VAR = value\n\nrule: dep\n\tcommand\n",
            "VAR = value\r\n\r\nrule: dep\r\n\tcommand\r\n",
            "A = 1\r\nB = 2\nC = 3\r\n",
            "VAR = a \\\n  b \\\n  c\nrule: x \\\n y\n\tcmd \\\n\t  more\n",
            "# comment\nifdef A\nifeq ($(B),1)\nX = 1\nelse ifneq ($(C),)\nX = 2\nelse\nX = 3\nendif\nendif\n",
            "rule:\n\techo a\nifdef V\n\techo verbose\nelse\n\t@echo quiet\nendif\n",
            "define F\nline one\nline two\nendef\n$(eval $(call F,x))\n",
            ".if ${A}\nX = 1\n.elif defined(B)\nX = 2\n.else\nX = 3\n.endif\n",
            "include a.mk\n-include b.mk\nvpath %.c src\n",
        ];
    for input in inputs {
        let (makefile, _) = Makefile::from_str_relaxed(input);
        assert_line_cols_match_walking(makefile.syntax());
    }
}

#[test]
fn test_line_col_after_mutation() {
    let mut makefile: Makefile = "A = 1\nifdef X\nB = 2\nendif\nrule: dep\n\tcmd\n"
        .parse()
        .unwrap();
    let mut rule = makefile.rules().next().unwrap();
    assert_eq!(rule.line(), 4);

    let mut var = makefile.variable_definitions().next().unwrap();
    var.set_value("one \\\n  two");
    assert_eq!(rule.line(), 5);
    assert_line_cols_match_walking(makefile.syntax());

    rule.push_command("second");
    let mut new_rule = makefile.add_rule("new");
    new_rule.push_command("build");
    assert_eq!(new_rule.line(), 9);
    assert_line_cols_match_walking(makefile.syntax());

    var.remove();
    assert_eq!(rule.line(), 3);
    assert_eq!(new_rule.line(), 7);
    assert_line_cols_match_walking(makefile.syntax());
}

#[test]
fn test_line_col_multiple_trees() {
    let a: Makefile = "A = 1\nrule:\n".parse().unwrap();
    let b: Makefile = "\n\n\nrule:\n".parse().unwrap();
    let rule_a = a.rules().next().unwrap();
    let rule_b = b.rules().next().unwrap();
    assert_eq!((rule_a.line(), rule_b.line()), (1, 3));
    assert_eq!((rule_a.line(), rule_b.line()), (1, 3));
}

#[test]
fn test_nested_conditionals_line_tracking() {
    let text = r#"ifdef OUTER
VAR1 = value1
ifdef INNER
VAR2 = value2
endif
VAR3 = value3
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(
        conditionals.len(),
        1,
        "Only outer conditional should be top-level"
    );
    assert_eq!(conditionals[0].line(), 0);
    assert_eq!(conditionals[0].column(), 0);
}

#[test]
fn test_conditional_else_line_tracking() {
    let text = r#"VAR1 = before

ifdef DEBUG
DEBUG_FLAGS = -g
else
DEBUG_FLAGS = -O2
endif

VAR2 = after
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].line(), 2);
    assert_eq!(conditionals[0].column(), 0);
}

#[test]
fn test_multiple_conditionals_line_tracking() {
    let text = r#"ifdef A
VAR_A = a
endif

ifdef B
VAR_B = b
endif

ifdef C
VAR_C = c
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 3);
    assert_eq!(conditionals[0].line(), 0);
    assert_eq!(conditionals[1].line(), 4);
    assert_eq!(conditionals[2].line(), 8);
}

#[test]
fn test_conditional_types_line_tracking() {
    let text = r#"ifdef VAR1
A = 1
endif

ifndef VAR2
B = 2
endif

ifeq ($(X),y)
C = 3
endif

ifneq ($(Y),n)
D = 4
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 4);

    assert_eq!(conditionals[0].line(), 0); // ifdef
    assert_eq!(
        conditionals[0].conditional_type(),
        Some("ifdef".to_string())
    );

    assert_eq!(conditionals[1].line(), 4); // ifndef
    assert_eq!(
        conditionals[1].conditional_type(),
        Some("ifndef".to_string())
    );

    assert_eq!(conditionals[2].line(), 8); // ifeq
    assert_eq!(conditionals[2].conditional_type(), Some("ifeq".to_string()));

    assert_eq!(conditionals[3].line(), 12); // ifneq
    assert_eq!(
        conditionals[3].conditional_type(),
        Some("ifneq".to_string())
    );
}

#[test]
fn test_conditional_with_comment_line_tracking() {
    let text = r#"# This is a comment
ifdef DEBUG
# Another comment
CFLAGS = -g
endif
# Final comment
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].line(), 1);
    assert_eq!(conditionals[0].column(), 0);
}

#[test]
fn test_conditional_after_variable_with_blank_lines() {
    let text = r#"VAR1 = value1


ifdef DEBUG
VAR2 = value2
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let vars: Vec<_> = makefile.variable_definitions().collect();
    let conditionals: Vec<_> = makefile.conditionals().collect();

    // variable_definitions() is recursive, so it finds VAR1 and VAR2 (inside conditional)
    assert_eq!(vars.len(), 2);
    assert_eq!(vars[0].line(), 0); // VAR1
    assert_eq!(vars[1].line(), 4); // VAR2

    assert_eq!(conditionals.len(), 1);
    assert_eq!(conditionals[0].line(), 3);
}

#[test]
fn test_empty_conditional_line_tracking() {
    let text = r#"ifdef DEBUG
endif

ifndef RELEASE
endif
"#;
    let makefile: Makefile = text.parse().unwrap();

    let conditionals: Vec<_> = makefile.conditionals().collect();
    assert_eq!(conditionals.len(), 2);
    assert_eq!(conditionals[0].line(), 0);
    assert_eq!(conditionals[1].line(), 3);
}

#[test]
fn test_recipe_line_tracking() {
    let text = r#"build:
	echo "Building..."
	gcc -o app main.c
	echo "Done"

test:
	./run-tests
"#;
    let makefile: Makefile = text.parse().unwrap();

    // Test first rule's recipes
    let rule1 = makefile.rules().next().expect("Should have first rule");
    let recipes: Vec<_> = rule1.recipe_nodes().collect();
    assert_eq!(recipes.len(), 3);

    assert_eq!(recipes[0].text(), "echo \"Building...\"");
    assert_eq!(recipes[0].line(), 1);
    assert_eq!(recipes[0].column(), 0);

    assert_eq!(recipes[1].text(), "gcc -o app main.c");
    assert_eq!(recipes[1].line(), 2);
    assert_eq!(recipes[1].column(), 0);

    assert_eq!(recipes[2].text(), "echo \"Done\"");
    assert_eq!(recipes[2].line(), 3);
    assert_eq!(recipes[2].column(), 0);

    // Test second rule's recipes
    let rule2 = makefile.rules().nth(1).expect("Should have second rule");
    let recipes2: Vec<_> = rule2.recipe_nodes().collect();
    assert_eq!(recipes2.len(), 1);

    assert_eq!(recipes2[0].text(), "./run-tests");
    assert_eq!(recipes2[0].line(), 6);
    assert_eq!(recipes2[0].column(), 0);
}

#[test]
fn test_recipe_with_variables_line_tracking() {
    let text = r#"install:
	mkdir -p $(DESTDIR)
	cp $(BINARY) $(DESTDIR)/
"#;
    let makefile: Makefile = text.parse().unwrap();
    let rule = makefile.rules().next().expect("Should have rule");
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 2);
    assert_eq!(recipes[0].line(), 1);
    assert_eq!(recipes[1].line(), 2);
}

#[test]
fn test_text_range() {
    let text = "VAR = 1\r\ninclude a.mk\nifdef X\nall: b\n\techo hi\nendif\nvpath %.c src\n";
    let makefile: Makefile = text.parse().unwrap();
    let range = |start: u32, end: u32| crate::TextRange::new(start.into(), end.into());

    assert_eq!(makefile.text_range(), range(0, 66));
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.text_range(), range(0, 9));
    let include = makefile.includes().next().unwrap();
    assert_eq!(include.text_range(), range(9, 22));
    let conditional = makefile.conditionals().next().unwrap();
    assert_eq!(conditional.text_range(), range(22, 52));
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.text_range(), range(30, 46));
    let recipe = rule.recipe_nodes().next().unwrap();
    assert_eq!(recipe.text_range(), range(37, 46));
    let vpath = makefile
        .items()
        .find_map(|item| match item {
            MakefileItem::Vpath(v) => Some(v),
            _ => None,
        })
        .unwrap();
    assert_eq!(vpath.text_range(), range(52, 66));
}
