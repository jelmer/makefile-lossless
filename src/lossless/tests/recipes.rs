use super::*;
use crate::test_util::assert_matches_reparse;

#[test]
fn test_nmake_space_indented_commands() {
    // In nmake a command line begins with one or more spaces or tabs.
    let code = "all: foo.obj\n    link foo.obj\n  echo a \\\n b\n\techo c\n";
    let parsed = parse(code, Some(MakefileVariant::NMake));
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), code);
    assert_eq!(
        node_kinds(&parsed.syntax()),
        "RULE\n  TARGETS\n  PREREQUISITES\n    PREREQUISITE\n  RECIPE\n  RECIPE\n  RECIPE\n"
    );
    let rule = root.rules().next().unwrap();
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["link foo.obj", "echo a \\\n b", "echo c"]
    );
}

#[test]
fn test_nmake_space_indented_command_after_inline_command() {
    let code = "foo.obj: foo.c ; cl /c foo.c\n  echo done\nbar:\n";
    let parsed = parse(code, Some(MakefileVariant::NMake));
    assert_eq!(parsed.errors, vec![]);
    let root = parsed.root();
    assert_eq!(root.to_string(), code);
    let rules = root.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 2);
    assert_eq!(
        rules[0].recipes().collect::<Vec<_>>(),
        vec!["cl /c foo.c", "echo done"]
    );
    assert_eq!(rules[1].targets().collect::<Vec<_>>(), vec!["bar"]);
}

#[test]
fn test_parse_inline_recipe() {
    let parsed = parse("all: dep ; echo hi # x\n\tcmd\n", None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax()),
        r#"ROOT@0..28
  RULE@0..28
    TARGETS@0..3
      IDENTIFIER@0..3 "all"
    OPERATOR@3..4 ":"
    WHITESPACE@4..5 " "
    PREREQUISITES@5..9
      PREREQUISITE@5..8
        IDENTIFIER@5..8 "dep"
      WHITESPACE@8..9 " "
    RECIPE@9..23
      OPERATOR@9..10 ";"
      WHITESPACE@10..11 " "
      TEXT@11..22 "echo hi # x"
      NEWLINE@22..23 "\n"
    RECIPE@23..28
      INDENT@23..24 "\t"
      TEXT@24..27 "cmd"
      NEWLINE@27..28 "\n"
"#
    );
}

#[test]
fn test_parse_with_variable_command() {
    let makefile =
        Makefile::from_reader("COM := command\nrule: dependency\n\t$(COM)".as_bytes()).unwrap();

    // Check variable definition
    let vars = makefile.variable_definitions().collect::<Vec<_>>();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name(), Some("COM".to_string()));
    assert_eq!(vars[0].raw_value(), Some("command".to_string()));

    // Check rule
    let rules = makefile.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["rule"]);
    assert_eq!(
        rules[0].prerequisites().collect::<Vec<_>>(),
        vec!["dependency"]
    );
    assert_eq!(rules[0].recipes().collect::<Vec<_>>(), vec!["$(COM)"]);
}

#[test]
fn test_comment_handling_in_recipes() {
    // Create a recipe with a comment line
    let recipe_comment = "build:\n\t# This is a comment\n\tgcc -o app main.c\n";

    // Parse the recipe
    let parsed = parse(recipe_comment, None);

    // Verify no parsing errors
    assert!(
        parsed.errors.is_empty(),
        "Should parse recipe with comments without errors"
    );

    // Check rule structure
    let root = parsed.root();
    let rules = root.rules().collect::<Vec<_>>();
    assert_eq!(rules.len(), 1, "Should find exactly one rule");

    // Check the rule has the correct name
    let build_rule = &rules[0];
    assert_eq!(
        build_rule.targets().collect::<Vec<_>>(),
        vec!["build"],
        "Rule should have 'build' as target"
    );

    // Check recipes are parsed correctly
    // recipes() now returns all recipe nodes including comment-only lines
    let recipes = build_rule.recipe_nodes().collect::<Vec<_>>();
    assert_eq!(recipes.len(), 2, "Should find two recipe nodes");

    // First recipe should be comment-only
    assert_eq!(recipes[0].text(), "");
    assert_eq!(
        recipes[0].comment(),
        Some("# This is a comment".to_string())
    );

    // Second recipe should be the command
    assert_eq!(recipes[1].text(), "gcc -o app main.c");
    assert_eq!(recipes[1].comment(), None);
}

#[test]
fn test_indented_help_text() {
    let content = r#"
.PHONY: help
help:
	@echo "Available targets:"
	@echo "  build  - Build the project"
	@echo "  test   - Run tests"
	@echo "  clean  - Remove build artifacts"
"#;
    // Use relaxed parsing for now
    let mut buf = content.as_bytes();
    let makefile = Makefile::from_reader_relaxed(&mut buf)
        .expect("Failed to parse indented help text")
        .0;

    // Check that we can extract rules even with errors
    let rules = makefile.rules().collect::<Vec<_>>();
    assert!(!rules.is_empty(), "Expected at least one rule");

    // Find help rule
    let help_rule = rules.iter().find(|r| r.targets().any(|t| t == "help"));
    assert!(help_rule.is_some(), "Expected to find help rule");

    // Check recipes - they might not be perfectly parsed but should exist
    let recipes = help_rule.unwrap().recipes().collect::<Vec<_>>();
    assert!(
        !recipes.is_empty(),
        "Expected at least one recipe line in help rule"
    );
    assert!(
        recipes.iter().any(|r| r.contains("Available targets")),
        "Expected to find 'Available targets' in recipes"
    );
}

#[test]
fn test_recipe_with_colon() {
    let content = r#"
build:
	@echo "Building at: $(shell date)"
	gcc -o program main.c
"#;
    let parsed = parse(content, None);
    assert!(
        parsed.errors.is_empty(),
        "Failed to parse recipe with colon: {:?}",
        parsed.errors
    );
}

#[test]
fn test_space_indented_lines_are_not_recipes() {
    // Only a tab introduces a recipe line; GNU make rejects the
    // space-indented lines below with "missing separator".
    let content = r#"
# Targets with help text
help:
    @echo "Available targets:"
    @echo "  build      build the project"

# Another target
clean:
	rm -rf build/
"#;

    let parsed = parse(content, None);
    assert!(!parsed.errors.is_empty());

    let makefile = parsed.root();
    assert_eq!(makefile.to_string(), content);
    let help_rule = makefile.find_rule_by_target("help").unwrap();
    assert_eq!(
        help_rule.recipes().collect::<Vec<_>>(),
        Vec::<String>::new()
    );
    let clean_rule = makefile.find_rule_by_target("clean").unwrap();
    assert_eq!(
        clean_rule.recipes().collect::<Vec<_>>(),
        vec!["rm -rf build/".to_string()]
    );
}

#[test]
fn test_recipe_with_leading_comments_and_blank_lines() {
    // Regression test for bug where recipes with leading comments and blank lines
    // were not parsed correctly. The parser would stop parsing recipes when it
    // encountered a newline, missing subsequent recipe lines.
    let makefile_text = r#"#!/usr/bin/make

%:
	dh $@

override_dh_build:
	# The next line is empty

	dh_python3
"#;
    let makefile = Makefile::from_reader_relaxed(makefile_text.as_bytes())
        .unwrap()
        .0;

    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 2, "Expected 2 rules");

    // First rule: %
    let rule0 = &rules[0];
    assert_eq!(rule0.targets().collect::<Vec<_>>(), vec!["%"]);
    assert_eq!(rule0.recipes().collect::<Vec<_>>(), vec!["dh $@"]);

    // Second rule: override_dh_build
    let rule1 = &rules[1];
    assert_eq!(
        rule1.targets().collect::<Vec<_>>(),
        vec!["override_dh_build"]
    );

    // The key assertion: we should have at least the actual command recipe
    let recipes: Vec<_> = rule1.recipes().collect();
    assert!(
        !recipes.is_empty(),
        "Expected at least one recipe for override_dh_build, got none"
    );
    assert!(
        recipes.contains(&"dh_python3".to_string()),
        "Expected 'dh_python3' in recipes, got: {:?}",
        recipes
    );
}

#[test]
fn test_recipe_insert_after_unterminated() {
    let makefile: Makefile = "a:\n\tcmd".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().next().unwrap().insert_after("x");
    assert_eq!(makefile.to_string(), "a:\n\tcmd\n\tx\n");
    assert_matches_reparse(&makefile);
}

#[test]
fn test_recipe_text_no_leading_tab() {
    // Test that Recipe::text() does not include the leading tab
    let text = "test:\n\techo hello\n\t\techo nested\n\t  echo with spaces\n";
    let makefile: Makefile = text.parse().unwrap();
    let rule = makefile.rules().next().expect("Should have rule");
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    assert_eq!(recipes.len(), 3);

    // Debug: print syntax tree for the first recipe
    eprintln!("Recipe 0 syntax tree:\n{:#?}", recipes[0].syntax());

    // First recipe: single tab
    assert_eq!(recipes[0].text(), "echo hello");

    // Second recipe: double tab (nested)
    eprintln!("Recipe 1 syntax tree:\n{:#?}", recipes[1].syntax());
    assert_eq!(recipes[1].text(), "\techo nested");

    // Third recipe: tab followed by spaces
    eprintln!("Recipe 2 syntax tree:\n{:#?}", recipes[2].syntax());
    assert_eq!(recipes[2].text(), "  echo with spaces");
}

#[test]
fn test_recipe_parent() {
    let makefile: Makefile = "all: dep\n\techo hello\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();

    let parent = recipe.parent().expect("Recipe should have parent");
    assert_eq!(parent.targets().collect::<Vec<_>>(), vec!["all"]);
    assert_eq!(parent.prerequisites().collect::<Vec<_>>(), vec!["dep"]);
}

fn shell_texts(text: &str) -> Vec<String> {
    let makefile: Makefile = text.parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().map(|r| r.shell_text()).collect()
}

#[test]
fn test_recipe_shell_text_plain() {
    assert_eq!(shell_texts("all:\n\techo hello\n"), vec!["echo hello"]);
}

#[test]
fn test_recipe_shell_text_no_trailing_newline() {
    assert_eq!(shell_texts("all:\n\techo hello"), vec!["echo hello"]);
}

#[test]
fn test_recipe_shell_text_extra_indent() {
    assert_eq!(
        shell_texts("all:\n\t\techo a\n\t  echo b\n"),
        vec!["\techo a", "  echo b"]
    );
}

#[test]
fn test_recipe_shell_text_inline_hash() {
    assert_eq!(shell_texts("all:\n\techo a # b\n"), vec!["echo a # b"]);
}

#[test]
fn test_recipe_shell_text_comment_only() {
    assert_eq!(
        shell_texts("all:\n\t# just a comment\n\techo hello\n"),
        vec!["# just a comment", "echo hello"]
    );
}

#[test]
fn test_recipe_shell_text_quoted_hash() {
    assert_eq!(shell_texts("all:\n\techo \"x#y\"\n"), vec!["echo \"x#y\""]);
}

#[test]
fn test_recipe_shell_text_continuation_with_tab() {
    assert_eq!(
        shell_texts("all:\n\techo a \\\n\tb \\\n\t\tc\n\techo d\n"),
        vec!["echo a \\\nb \\\n\tc", "echo d"]
    );
}

#[test]
fn test_recipe_shell_text_continuation_without_tab() {
    assert_eq!(
        shell_texts("all:\n\techo a \\\n  b\n"),
        vec!["echo a \\\n  b"]
    );
}

#[test]
fn test_recipe_shell_text_continuation_with_hash() {
    assert_eq!(
        shell_texts("all:\n\techo a # b \\\n\tc\n"),
        vec!["echo a # b \\\nc"]
    );
}

#[test]
fn test_recipe_shell_text_continuation_comment_line() {
    assert_eq!(
        shell_texts("all:\n\techo a \\\n\t# x\n"),
        vec!["echo a \\\n# x"]
    );
}

#[test]
fn test_recipe_shell_text_keeps_prefixes() {
    assert_eq!(
        shell_texts("all:\n\t@echo a\n\t-echo b\n\t+echo c\n\t@-+echo d\n\t@# e\n"),
        vec!["@echo a", "-echo b", "+echo c", "@-+echo d", "@# e"]
    );
}

#[test]
fn test_recipe_shell_text_inline_recipe() {
    assert_eq!(
        shell_texts("all: dep ; echo hi # x\n\techo b\n"),
        vec!["echo hi # x", "echo b"]
    );
    assert_eq!(shell_texts("all: dep ;\t# x\n"), vec!["# x"]);
    assert_eq!(
        shell_texts("all: ; # a \\\n\t  b \\\n\tc\n"),
        vec!["# a \\\n  b \\\nc"]
    );
    assert_eq!(
        shell_texts("all: dep ;echo a \\\n\tb\n"),
        vec!["echo a \\\nb"]
    );
}

#[test]
fn test_recipe_insert_before_single() {
    let makefile: Makefile = "all:\n\techo world\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();

    recipe.insert_before("echo hello");

    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(recipes, vec!["echo hello", "echo world"]);
}

#[test]
fn test_recipe_insert_before_multiple() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    // Insert before the second recipe
    recipes[1].insert_before("echo middle");

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(
        new_recipes,
        vec!["echo one", "echo middle", "echo two", "echo three"]
    );
}

#[test]
fn test_recipe_insert_before_first() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[0].insert_before("echo zero");

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo zero", "echo one", "echo two"]);
}

#[test]
fn test_recipe_insert_after_single() {
    let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();

    recipe.insert_after("echo world");

    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(recipes, vec!["echo hello", "echo world"]);
}

#[test]
fn test_recipe_insert_after_multiple() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    // Insert after the second recipe
    recipes[1].insert_after("echo middle");

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(
        new_recipes,
        vec!["echo one", "echo two", "echo middle", "echo three"]
    );
}

#[test]
fn test_recipe_insert_after_last() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[1].insert_after("echo three");

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo one", "echo two", "echo three"]);
}

#[test]
fn test_recipe_remove_single() {
    let makefile: Makefile = "all:\n\techo hello\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipe = rule.recipe_nodes().next().unwrap();

    recipe.remove();

    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.recipes().count(), 0);
}

#[test]
fn test_recipe_remove_first() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[0].remove();

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo two", "echo three"]);
}

#[test]
fn test_recipe_remove_middle() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[1].remove();

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo one", "echo three"]);
}

#[test]
fn test_recipe_remove_last() {
    let makefile: Makefile = "all:\n\techo one\n\techo two\n\techo three\n"
        .parse()
        .unwrap();
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();

    recipes[2].remove();

    let rule = makefile.rules().next().unwrap();
    let new_recipes: Vec<_> = rule.recipes().collect();
    assert_eq!(new_recipes, vec!["echo one", "echo two"]);
}
