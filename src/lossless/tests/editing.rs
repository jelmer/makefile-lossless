use super::*;
use crate::test_util::{assert_matches_reparse, item_without_newline};

#[test]
fn test_rule_remove_with_comment() {
    let makefile: Makefile = r#"rule1:
	command1

# Comment about rule2
rule2:
	command2
rule3:
	command3
"#
    .parse()
    .unwrap();

    // Remove rule2
    let rule2 = makefile.rules().nth(1).expect("Should have second rule");
    rule2.remove().unwrap();

    // Verify the comment is removed
    // Note: The empty line after rule1 is part of rule1's text, not a sibling, so it's preserved
    assert_eq!(
        makefile.code(),
        "rule1:\n\tcommand1\n\nrule3:\n\tcommand3\n"
    );
}

#[test]
fn test_rule_clone() {
    // Test that Rule can be cloned and produces an identical copy
    let rule_text = "rule:\n\tcommand\n\n";
    let rule: Rule = rule_text.parse().unwrap();
    let cloned = rule.clone();

    // Both should produce the same string representation
    assert_eq!(rule.to_string(), cloned.to_string());
    assert_eq!(rule.to_string(), rule_text);
    assert_eq!(cloned.to_string(), rule_text);

    // Verify targets and recipes are the same
    assert_eq!(
        rule.targets().collect::<Vec<_>>(),
        cloned.targets().collect::<Vec<_>>()
    );
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        cloned.recipes().collect::<Vec<_>>()
    );
}

#[test]
fn test_makefile_clone() {
    // Test that Makefile and other AST nodes can be cloned
    let input = "VAR = value\n\nrule:\n\tcommand\n";
    let makefile: Makefile = input.parse().unwrap();
    let cloned = makefile.clone();

    // Both should produce the same string representation
    assert_eq!(makefile.to_string(), cloned.to_string());
    assert_eq!(makefile.to_string(), input);

    // Verify rule count is the same
    assert_eq!(makefile.rules().count(), cloned.rules().count());

    // Verify variable definitions are the same
    assert_eq!(
        makefile.variable_definitions().count(),
        cloned.variable_definitions().count()
    );
}

#[test]
fn test_item_insert_after_unterminated() {
    let makefile: Makefile = "X = 1".parse().unwrap();
    let new_item = "Y = 1\n"
        .parse::<Makefile>()
        .unwrap()
        .items()
        .next()
        .unwrap();
    makefile
        .items()
        .next()
        .unwrap()
        .insert_after(new_item)
        .unwrap();
    assert_eq!(makefile.to_string(), "X = 1\nY = 1\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_conditional_remove() {
    let makefile: Makefile = r#"ifdef DEBUG
VAR = debug
endif

VAR2 = value2
"#
    .parse()
    .unwrap();

    let mut conditional = makefile.conditionals().next().unwrap();
    let result = conditional.remove();
    assert!(result.is_ok());

    let code = makefile.to_string();
    assert!(!code.contains("ifdef DEBUG"));
    assert!(!code.contains("VAR = debug"));
    assert!(code.contains("VAR2 = value2"));
}

#[test]
fn test_item_insert_before_without_newline() {
    let makefile: Makefile = "X = 1\n".parse().unwrap();
    let mut first = makefile.items().next().unwrap();
    first.insert_before(item_without_newline("Z = 1")).unwrap();
    assert_eq!(makefile.to_string(), "Z = 1\nX = 1\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_item_insert_after_without_newline() {
    let makefile: Makefile = "X = 1\nY = 1\n".parse().unwrap();
    let mut first = makefile.items().next().unwrap();
    first.insert_after(item_without_newline("Z = 1")).unwrap();
    assert_eq!(makefile.to_string(), "X = 1\nZ = 1\nY = 1\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_rule_parent() {
    let makefile: Makefile = r#"all:
	echo "test"
"#
    .parse()
    .unwrap();

    let rule = makefile.rules().next().unwrap();
    let parent = rule.parent();
    // Parent is ROOT node which doesn't cast to MakefileItem
    assert!(parent.is_none());
}
