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

/// Lines that can not be written as a single recipe line, comment or
/// variable value.
const LINE_BREAKING: [&str; 4] = ["a\nb", "a\r\nb", "a \\", "a \\\\\\"];

#[test]
fn test_recipe_commands_reject_line_breaks() {
    let text = "a:\n\techo\nb:\n";
    let makefile: Makefile = text.parse().unwrap();
    let mut rule = makefile.rules().next().unwrap();
    let mut recipe = rule.recipe_nodes().next().unwrap();
    for line in LINE_BREAKING {
        assert!(rule.try_push_command(line).is_err(), "{line:?}");
        assert!(rule.try_insert_command(0, line).is_err(), "{line:?}");
        assert!(rule.try_replace_command(0, line).is_err(), "{line:?}");
        assert!(recipe.try_replace_text(line).is_err(), "{line:?}");
        assert!(recipe.try_insert_before(line).is_err(), "{line:?}");
        assert!(recipe.try_insert_after(line).is_err(), "{line:?}");
        assert_eq!(makefile.code(), text, "{line:?}");
    }
}

#[test]
#[should_panic(expected = "invalid recipe line")]
fn test_push_command_panics_on_newline() {
    let mut rule: Rule = "a:\n".parse().unwrap();
    rule.push_command("echo a\necho b");
}

#[test]
fn test_recipe_commands_with_continuation() {
    let makefile: Makefile = "a:\n\techo\nb:\n".parse().unwrap();
    let mut rule = makefile.rules().next().unwrap();
    rule.try_push_command("echo x \\\n\ty").unwrap();
    assert_eq!(makefile.code(), "a:\n\techo\n\techo x \\\n\ty\nb:\n");
    assert_matches_reparse(&makefile);
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo", "echo x \\\ny"]
    );

    assert!(rule.try_replace_command(0, "c \\\n  d # e").unwrap());
    assert!(rule.try_insert_command(2, "f \\\\").unwrap());
    assert_eq!(
        makefile.code(),
        "a:\n\tc \\\n  d # e\n\techo x \\\n\ty\n\tf \\\\\nb:\n"
    );
    assert_matches_reparse(&makefile);
    assert!(!rule.try_insert_command(4, "g").unwrap());
    assert!(!rule.try_replace_command(3, "g").unwrap());
}

#[test]
fn test_inline_recipe_replace_with_continuation() {
    let makefile: Makefile = "a: ; echo\n".parse().unwrap();
    let mut rule = makefile.rules().next().unwrap();
    assert!(rule.try_replace_command(0, "x \\\n\ty").unwrap());
    assert_eq!(makefile.code(), "a: ; x \\\n\ty\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_set_value_rejects_line_breaks() {
    let text = "X = 1\nY = 2\n";
    let makefile: Makefile = text.parse().unwrap();
    let mut var = makefile.variable_definitions().next().unwrap();
    for value in LINE_BREAKING {
        assert!(var.try_set_value(value).is_err(), "{value:?}");
        assert_eq!(makefile.code(), text, "{value:?}");
    }
    assert!(var.try_set_name("A\nB").is_err());
    assert_eq!(makefile.code(), text);
}

#[test]
fn test_set_value_tree_matches_reparse() {
    let makefile: Makefile = "X = 1\nY = 2\n".parse().unwrap();
    let mut var = makefile.variable_definitions().next().unwrap();
    for value in ["a b", "a $(B) \\\n  c", "a\\\\"] {
        var.try_set_value(value).unwrap();
        assert_eq!(makefile.code(), format!("X = {value}\nY = 2\n"));
        assert_eq!(var.raw_value(), Some(value.to_string()));
        assert_matches_reparse(&makefile);
    }
}

#[test]
fn test_set_value_define() {
    let makefile: Makefile = "define X\nold\nendef\n".parse().unwrap();
    let mut var = makefile.variable_definitions().next().unwrap();
    var.try_set_value("a b\nc").unwrap();
    assert_eq!(makefile.code(), "define X\na b\nc\nendef\n");
    assert_eq!(var.raw_value(), Some("a b\nc\n".to_string()));
    assert_matches_reparse(&makefile);

    assert!(var.try_set_value("a\nendef\nb").is_err());
    assert_eq!(makefile.code(), "define X\na b\nc\nendef\n");
}

#[test]
fn test_comments_reject_line_breaks() {
    let text = "# c\nX = 1\n";
    let makefile: Makefile = text.parse().unwrap();
    let mut item = makefile.items().next().unwrap();
    for comment in LINE_BREAKING {
        assert!(item.add_comment(comment).is_err(), "{comment:?}");
        assert!(item.modify_comment(comment).is_err(), "{comment:?}");
        assert_eq!(makefile.code(), text, "{comment:?}");
    }
    item.add_comment("d \\\\").unwrap();
    assert_eq!(makefile.code(), "# c\n# d \\\\\nX = 1\n");
    assert_matches_reparse(&makefile);
}
