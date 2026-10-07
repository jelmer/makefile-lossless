use super::*;

#[test]
fn test_parse_simple() {
    const SIMPLE: &str = r#"VARIABLE = value

rule: dependency
	command
"#;
    let parsed = parse(SIMPLE, None);
    assert!(parsed.errors.is_empty());
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r#"ROOT@0..44
  VARIABLE@0..17
    IDENTIFIER@0..8 "VARIABLE"
    WHITESPACE@8..9 " "
    OPERATOR@9..10 "="
    WHITESPACE@10..11 " "
    EXPR@11..16
      IDENTIFIER@11..16 "value"
    NEWLINE@16..17 "\n"
  BLANK_LINE@17..18
    NEWLINE@17..18 "\n"
  RULE@18..44
    TARGETS@18..22
      IDENTIFIER@18..22 "rule"
    OPERATOR@22..23 ":"
    WHITESPACE@23..24 " "
    PREREQUISITES@24..34
      PREREQUISITE@24..34
        IDENTIFIER@24..34 "dependency"
    NEWLINE@34..35 "\n"
    RECIPE@35..44
      INDENT@35..36 "\t"
      TEXT@36..43 "command"
      NEWLINE@43..44 "\n"
"#
    );

    let root = parsed.root();

    let mut rules = root.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    let rule = rules.pop().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);

    let mut variables = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(variables.len(), 1);
    let variable = variables.pop().unwrap();
    assert_eq!(variable.name(), Some("VARIABLE".to_string()));
    assert_eq!(variable.raw_value(), Some("value".to_string()));
}

#[test]
fn test_parse_makefile_without_newline() {
    let makefile = "rule: dependency\n\tcommand".parse::<Makefile>().unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_from_reader() {
    let makefile = Makefile::from_reader("rule: dependency\n\tcommand".as_bytes()).unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_parse_with_tab_after_last_newline() {
    let makefile = Makefile::from_reader("rule: dependency\n\tcommand\n\t".as_bytes()).unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_parse_with_space_after_last_newline() {
    let makefile = Makefile::from_reader("rule: dependency\n\tcommand\n ".as_bytes()).unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_parse_with_comment_after_last_newline() {
    let makefile =
        Makefile::from_reader("rule: dependency\n\tcommand\n#comment".as_bytes()).unwrap();
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_whitespace_and_eof_handling() {
    // Test 1: File ending with blank lines
    let blank_lines = "VAR = value\n\n\n";

    let parsed_blank = parse(blank_lines, None);

    // We should be able to extract the variable definition
    let root = parsed_blank.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(
        vars.len(),
        1,
        "Should find one variable in blank lines test"
    );

    // Test 2: File ending with space
    let trailing_space = "VAR = value \n";

    let parsed_space = parse(trailing_space, None);

    // We should be able to extract the variable definition
    let root = parsed_space.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(
        vars.len(),
        1,
        "Should find one variable in trailing space test"
    );

    // Test 3: No final newline
    let no_newline = "VAR = value";

    let parsed_no_newline = parse(no_newline, None);

    // Regardless of parsing errors, we should be able to extract the variable
    let root = parsed_no_newline.root();
    let vars = root.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1, "Should find one variable in no newline test");
    assert_eq!(
        vars[0].name(),
        Some("VAR".to_string()),
        "Variable name should be VAR"
    );
}

#[test]
fn test_special_directives() {
    let content = r#"
# Special makefile directives
.PHONY: all clean
.SUFFIXES: .c .o
.DEFAULT: all

# Variable definition and export directive
export PATH := /usr/bin:/bin
"#;
    // Use relaxed parsing to allow for special directives
    let mut buf = content.as_bytes();
    let makefile = Makefile::read_relaxed(&mut buf).expect("Failed to parse special directives");

    // Check that we can extract rules even with errors
    let rules = makefile.rules().collect::<Vec<_>>();

    // Find phony rule
    let phony_rule = rules
        .iter()
        .find(|r| r.targets().any(|t| t.contains(".PHONY")));
    assert!(phony_rule.is_some(), "Expected to find .PHONY rule");

    // Check that variables can be extracted
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert!(!vars.is_empty(), "Expected to find at least one variable");
}

// Comprehensive Test combining multiple issues

#[test]
fn test_comprehensive_real_world_makefile() {
    // Simple makefile with basic elements
    let content = r#"
# Basic variable assignment
VERSION = 1.0.0

# Phony target
.PHONY: all clean

# Simple rule
all:
	echo "Building version $(VERSION)"

# Another rule with dependencies
clean:
	rm -f *.o
"#;

    // Parse the content
    let parsed = parse(content, None);

    // Check that parsing succeeded
    assert!(parsed.errors.is_empty(), "Expected no parsing errors");

    // Check that we found variables
    let variables = parsed.root().variable_definitions().collect::<Vec<_>>();
    assert!(!variables.is_empty(), "Expected at least one variable");
    assert_eq!(
        variables[0].name(),
        Some("VERSION".to_string()),
        "Expected VERSION variable"
    );

    // Check that we found rules
    let rules = parsed.root().rules().collect::<Vec<_>>();
    assert!(!rules.is_empty(), "Expected at least one rule");

    // Check for specific rules
    let rule_targets: Vec<String> = rules
        .iter()
        .flat_map(|r| r.targets().collect::<Vec<_>>())
        .collect();
    assert!(
        rule_targets.contains(&".PHONY".to_string()),
        "Expected .PHONY rule"
    );
    assert!(
        rule_targets.contains(&"all".to_string()),
        "Expected 'all' rule"
    );
    assert!(
        rule_targets.contains(&"clean".to_string()),
        "Expected 'clean' rule"
    );
}

#[test]
fn test_balanced_parens_counting() {
    // Test balanced parentheses parsing to cover the += vs -= mutant
    let input = r#"
VAR = $(call func,$(nested,arg),extra)
COMPLEX = $(if $(condition),$(then_val),$(else_val))
"#;
    let parsed = parse(input, None);
    assert!(parsed.errors.is_empty());

    let makefile = parsed.root();
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 2);
}

#[test]
fn test_documentation_lookahead() {
    // Test the documentation lookahead logic to cover the - vs + mutant at line 895
    let input = r#"
# Documentation comment
help:
	@echo "Usage instructions"
	@echo "More help text"
"#;
    let parsed = parse(input, None);
    assert!(parsed.errors.is_empty());

    let makefile = parsed.root();
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().next().unwrap(), "help");
}

#[test]
fn test_edge_case_empty_input() {
    // Test with empty input
    let parsed = parse("", None);
    assert!(parsed.errors.is_empty());

    // Test with only whitespace
    let parsed2 = parse("   \n  \n", None);
    // Some parsers might report warnings/errors for whitespace-only input
    // Just ensure it doesn't crash
    let _makefile = parsed2.root();
}

#[test]
fn test_large_makefile_performance() {
    // Create a makefile with many rules to test performance doesn't degrade
    let mut makefile = Makefile::new();

    // Add 100 rules
    for i in 0..100 {
        let rule_name = format!("rule{}", i);
        makefile
            .add_rule(&rule_name)
            .push_command(&format!("command{}", i));
    }

    assert_eq!(makefile.rules().count(), 100);

    // Replace rule in the middle - should be efficient
    let new_rule: Rule = "middle_rule:\n\tmiddle_command\n".parse().unwrap();
    makefile.replace_rule(50, new_rule).unwrap();

    // Verify the change
    let rule_50_targets: Vec<_> = makefile.rules().nth(50).unwrap().targets().collect();
    assert_eq!(rule_50_targets, vec!["middle_rule"]);

    assert_eq!(makefile.rules().count(), 100); // Count unchanged
}

#[test]
fn test_debug() {
    let makefile: Makefile = "X = $(Y)\nall: a\n\techo hi\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    assert_eq!(
        format!("{rule:?}"),
        "Rule { range: 9..25, text: \"all: a\\n\\techo hi\\n\" }"
    );
    assert_eq!(
        format!("{:?}", makefile.items().next().unwrap()),
        "Variable(VariableDefinition { range: 0..9, text: \"X = $(Y)\\n\" })"
    );
    assert_eq!(
        format!("{:?}", rule.items().next().unwrap()),
        "Recipe(\"echo hi\")"
    );
    let reference = makefile.variable_references().next().unwrap();
    assert_eq!(
        format!("{reference:?}"),
        "VariableReference { range: 4..8, text: \"$(Y)\" }"
    );
}
