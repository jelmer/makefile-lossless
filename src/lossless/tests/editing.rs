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
        makefile.to_string(),
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

#[test]
fn test_rule_remove_doc_comment() {
    let cases = [
        ("a:\n\techo\n# doc\nc:\n", "a:\n\techo\n"),
        ("a:\n# doc\n# more\nc:\n", "a:\n"),
        ("a:\n\techo\n# doc\nc:\nd:\n", "a:\n\techo\nd:\n"),
        (
            "a:\r\n\techo\r\n# doc\r\nc:\r\nd:\r\n",
            "a:\r\n\techo\r\nd:\r\n",
        ),
        ("x = 1\n\n# doc\nc:\n", "x = 1\n"),
        ("x = 1\n\n# doc\nc:\n\nd:\n", "x = 1\n\nd:\n"),
        ("x = 1\n\n# doc\nc:\nd:\n", "x = 1\n\nd:\n"),
        ("x = 1\n# x\n\n# doc\nc:\nd:\n", "x = 1\n# x\n\nd:\n"),
        ("# header\n\nc:\nd:\n", "# header\n\nd:\n"),
        ("#!/bin/make\n# doc\nc:\n", "#!/bin/make\n"),
        ("X = 1 # x\nc:\n", "X = 1 # x\n"),
        ("FOO = a \\\n# continued\nc:\n", "FOO = a \\\n# continued\n"),
        ("ifdef X\n  # doc\n  c:\nendif\n", "ifdef X\nendif\n"),
    ];
    for (text, expected) in cases {
        let makefile: Makefile = text.parse().unwrap();
        let rule = makefile
            .rules()
            .find(|r| r.targets().collect::<Vec<_>>() == ["c"])
            .unwrap();
        rule.remove().unwrap();
        assert_eq!(makefile.to_string(), expected, "{text:?}");
        assert_matches_reparse(&makefile);
    }
}

#[test]
fn test_include_and_conditional_remove_doc_comment() {
    let makefile: Makefile = "a:\n\techo\n# doc\ninclude x.mk\n# far\n\n# doc\nifdef X\nendif\n"
        .parse()
        .unwrap();
    makefile.includes().next().unwrap().remove().unwrap();
    assert_eq!(
        makefile.to_string(),
        "a:\n\techo\n# far\n\n# doc\nifdef X\nendif\n"
    );
    makefile.conditionals().next().unwrap().remove().unwrap();
    assert_eq!(makefile.to_string(), "a:\n\techo\n# far\n");
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
        assert_eq!(makefile.to_string(), text, "{line:?}");
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
    assert_eq!(makefile.to_string(), "a:\n\techo\n\techo x \\\n\ty\nb:\n");
    assert_matches_reparse(&makefile);
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo", "echo x \\\ny"]
    );

    assert!(rule.try_replace_command(0, "c \\\n  d # e").unwrap());
    assert!(rule.try_insert_command(2, "f \\\\").unwrap());
    assert_eq!(
        makefile.to_string(),
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
    assert_eq!(makefile.to_string(), "a: ; x \\\n\ty\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_set_value_rejects_line_breaks() {
    let text = "X = 1\nY = 2\n";
    let makefile: Makefile = text.parse().unwrap();
    let mut var = makefile.variable_definitions().next().unwrap();
    for value in LINE_BREAKING {
        assert!(var.try_set_value(value).is_err(), "{value:?}");
        assert_eq!(makefile.to_string(), text, "{value:?}");
    }
    assert!(var.try_set_name("A\nB").is_err());
    assert_eq!(makefile.to_string(), text);
}

#[test]
fn test_set_value_tree_matches_reparse() {
    let makefile: Makefile = "X = 1\nY = 2\n".parse().unwrap();
    let mut var = makefile.variable_definitions().next().unwrap();
    for value in ["a b", "a $(B) \\\n  c", "a\\\\"] {
        var.try_set_value(value).unwrap();
        assert_eq!(makefile.to_string(), format!("X = {value}\nY = 2\n"));
        assert_eq!(var.raw_value(), Some(value.to_string()));
        assert_matches_reparse(&makefile);
    }
}

#[test]
fn test_set_value_continuation_at_end() {
    // The line break of a line continuation ending the file is kept, but
    // the continuation is replaced with the value.
    for (text, value, expected) in [
        ("X := a \\\n", "new", "X := new\n"),
        ("X := a \\\r\n", "new", "X := new\r\n"),
        ("X := a \\\n  ", "new", "X := new\n"),
        ("export X := $(A) \\\n", "new", "export X := new\n"),
        ("t: X := a \\\n", "new", "t: X := new\n"),
        ("X := a \\\n", "b \\\n  c", "X := b \\\n  c\n"),
        ("X := a \\", "new", "X := new"),
        ("X := a \\\n\n", "new", "X := new\n"),
    ] {
        let makefile: Makefile = text.parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.try_set_value(value).unwrap();
        assert_eq!(makefile.to_string(), expected, "{text:?}");
        assert_eq!(var.raw_value(), Some(value.to_string()), "{text:?}");
        assert_matches_reparse(&makefile);
    }
}

#[test]
fn test_set_value_define() {
    let makefile: Makefile = "define X\nold\nendef\n".parse().unwrap();
    let mut var = makefile.variable_definitions().next().unwrap();
    var.try_set_value("a b\nc").unwrap();
    assert_eq!(makefile.to_string(), "define X\na b\nc\nendef\n");
    assert_eq!(var.raw_value(), Some("a b\nc\n".to_string()));
    assert_matches_reparse(&makefile);

    assert!(var.try_set_value("a\nendef\nb").is_err());
    assert_eq!(makefile.to_string(), "define X\na b\nc\nendef\n");
}

#[test]
fn test_comments_reject_line_breaks() {
    let text = "# c\nX = 1\n";
    let makefile: Makefile = text.parse().unwrap();
    let mut item = makefile.items().next().unwrap();
    for comment in LINE_BREAKING {
        assert!(item.add_comment(comment).is_err(), "{comment:?}");
        assert!(item.modify_comment(comment).is_err(), "{comment:?}");
        assert_eq!(makefile.to_string(), text, "{comment:?}");
    }
    item.add_comment("d \\\\").unwrap();
    assert_eq!(makefile.to_string(), "# c\n# d \\\\\nX = 1\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_recipe_prefix_push_command() {
    let mut makefile: Makefile = ".RECIPEPREFIX = >\nall:\n>echo a\n".parse().unwrap();
    let mut rule = makefile.rules().next().unwrap();
    rule.push_command("echo b");
    rule.insert_command(0, "echo c");
    rule.replace_command(1, "echo d");
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\nall:\n>echo c\n>echo d\n>echo b\n"
    );
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo c", "echo d", "echo b"]
    );
    assert_matches_reparse(&makefile);

    // An empty rule, as add_rule creates.
    let mut rule = makefile.add_rule("b");
    rule.push_command("echo e");
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\nall:\n>echo c\n>echo d\n>echo b\n\nb:\n>echo e\n"
    );
    assert_matches_reparse(&makefile);
}

#[test]
fn test_recipe_prefix_continuation() {
    // make strips the recipe prefix from the start of continuation lines.
    let makefile: Makefile = ".RECIPEPREFIX = >\nall:\n>echo a\n".parse().unwrap();
    let mut rule = makefile.rules().next().unwrap();
    rule.push_command("echo x \\\n\ty");
    rule.push_command("echo y \\\n\t\tz");
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\nall:\n>echo a\n>echo x \\\n>y\n>echo y \\\n>\tz\n"
    );
    assert_matches_reparse(&makefile);
}

#[test]
fn test_recipe_prefix_recipe_editing() {
    let makefile: Makefile = ".RECIPEPREFIX = >\nall: ; echo a\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();
    recipe.insert_after("echo b");
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\nall: ; echo a\n>echo b\n"
    );
    assert_matches_reparse(&makefile);
    recipe.insert_before("echo c");
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\nall:\n>echo c\n>echo a\n>echo b\n"
    );
    assert_matches_reparse(&makefile);
    let mut recipe = rule.recipe_nodes().nth(2).unwrap();
    recipe.replace_text("echo x \\\n\ty");
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\nall:\n>echo c\n>echo a\n>echo x \\\n>y\n"
    );
    assert_matches_reparse(&makefile);
}

#[test]
fn test_recipe_prefix_changes_mid_file() {
    let makefile: Makefile = ".RECIPEPREFIX = >\na:\n>echo a\n.RECIPEPREFIX =\nb:\n\techo c\n"
        .parse()
        .unwrap();
    let mut rules: Vec<_> = makefile.rules().collect();
    rules[0].push_command("echo b");
    rules[1].push_command("echo d");
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\na:\n>echo a\n>echo b\n.RECIPEPREFIX =\nb:\n\techo c\n\techo d\n"
    );
    assert_matches_reparse(&makefile);
}

#[test]
fn test_recipe_prefix_inserted_rule() {
    let mut makefile: Makefile = ".RECIPEPREFIX = >\na:\n>echo a\n".parse().unwrap();
    makefile
        .insert_rule(1, Rule::new(&["b"], &[], &["echo b"]))
        .unwrap();
    let rule: Rule = "c:\n\techo x \\\n\ty\n\techo z\n".parse().unwrap();
    makefile.insert_rule(2, rule).unwrap();
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\na:\n>echo a\n\nb:\n>echo b\n\nc:\n>echo x \\\n>y\n>echo z\n"
    );
    assert_matches_reparse(&makefile);

    // Recipes from a makefile with a different prefix are converted.
    let mut other: Makefile = "b:\n\techo b\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    other.insert_rule(0, rule).unwrap();
    assert_eq!(other.to_string(), "a:\n\techo a\n\nb:\n\techo b\n");
    assert_matches_reparse(&other);
}

#[test]
fn test_recipe_prefix_add_conditional() {
    let mut makefile: Makefile = ".RECIPEPREFIX = >\na:\n>echo a\n".parse().unwrap();
    makefile
        .add_conditional("ifdef", "X", "b:\n\techo b\n", Some("c:\n\techo c\n"))
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\na:\n>echo a\n\nifdef X\nb:\n>echo b\nelse\nc:\n>echo c\nendif\n"
    );
    assert_matches_reparse(&makefile);

    let mut cond = makefile.conditionals().next().unwrap();
    cond.add_if_item(MakefileItem::Rule(Rule::new(&["d"], &[], &["echo d"])));
    // Directly after the assignment that sets the prefix.
    let mut item = makefile.items().next().unwrap();
    item.insert_after(MakefileItem::Rule(Rule::new(&["e"], &[], &["echo e"])))
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        ".RECIPEPREFIX = >\ne:\n>echo e\na:\n>echo a\n\nifdef X\nd:\n>echo d\nb:\n>echo b\nelse\nc:\n>echo c\nendif\n"
    );
    assert_matches_reparse(&makefile);
}

#[test]
fn test_recipe_prefix_set_by_inserted_item() {
    // The prefix set in the inserted conditional depends on the text before it.
    let other: Makefile = "ifdef X\n.RECIPEPREFIX := $(P)\nb:\n\techo b\nendif\n"
        .parse()
        .unwrap();
    let cond = other.items().next().unwrap();
    let makefile: Makefile = "P := >\na:\n\techo a\n".parse().unwrap();
    let mut item = makefile.items().last().unwrap();
    item.insert_after(cond).unwrap();
    assert_eq!(
        makefile.to_string(),
        "P := >\na:\n\techo a\nifdef X\n.RECIPEPREFIX := $(P)\nb:\n>echo b\nendif\n"
    );
    assert_matches_reparse(&makefile);
}

#[test]
fn test_recipe_prefix_add_conditional_with_items() {
    // Items from a makefile with a different prefix.
    let other: Makefile = ".RECIPEPREFIX = >\nb:\n>echo b\n".parse().unwrap();
    let rule = other.rules().next().unwrap();
    let mut makefile: Makefile = "a:\n\techo a\n".parse().unwrap();
    makefile
        .add_conditional_with_items("ifdef", "X", [MakefileItem::Rule(rule)], None::<Vec<_>>)
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        "a:\n\techo a\n\nifdef X\nb:\n\techo b\nendif\n"
    );
    assert_matches_reparse(&makefile);
}
