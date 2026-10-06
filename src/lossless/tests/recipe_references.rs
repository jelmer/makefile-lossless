use super::*;

/// The text and name of each reference in `text`, checking that the tree
/// still holds the whole text.
fn references(text: &str, variant: Option<MakefileVariant>) -> Vec<(String, Option<String>)> {
    let parsed = parse(text, variant);
    let makefile = parsed.root();
    assert_eq!(makefile.to_string(), text);
    makefile
        .variable_references()
        .map(|r| (r.to_string(), r.name()))
        .collect()
}

fn r(text: &str, name: &str) -> (String, Option<String>) {
    (text.to_string(), Some(name.to_string()))
}

fn recipe(text: &str, variant: Option<MakefileVariant>) -> Recipe {
    let makefile = parse(text, variant).root();
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().next().unwrap()
}

#[test]
fn test_recipe_reference_tree() {
    let code = "all:\n\t@$(CC) -o $@ $(addprefix -I,$(DIRS)) $$HOME\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(
        format!("{:#?}", parsed.syntax().children().next().unwrap()),
        r##"RULE@0..50
  TARGETS@0..3
    IDENTIFIER@0..3 "all"
  OPERATOR@3..4 ":"
  PREREQUISITES@4..4
  NEWLINE@4..5 "\n"
  RECIPE@5..50
    INDENT@5..6 "\t"
    TEXT@6..7 "@"
    EXPR@7..12
      DOLLAR@7..8 "$"
      LPAREN@8..9 "("
      IDENTIFIER@9..11 "CC"
      RPAREN@11..12 ")"
    TEXT@12..16 " -o "
    EXPR@16..18
      DOLLAR@16..17 "$"
      TEXT@17..18 "@"
    TEXT@18..19 " "
    EXPR@19..42
      DOLLAR@19..20 "$"
      LPAREN@20..21 "("
      IDENTIFIER@21..30 "addprefix"
      WHITESPACE@30..31 " "
      IDENTIFIER@31..33 "-I"
      COMMA@33..34 ","
      EXPR@34..41
        DOLLAR@34..35 "$"
        LPAREN@35..36 "("
        IDENTIFIER@36..40 "DIRS"
        RPAREN@40..41 ")"
      RPAREN@41..42 ")"
    TEXT@42..43 " "
    EXPR@43..45
      DOLLAR@43..44 "$"
      DOLLAR@44..45 "$"
    TEXT@45..49 "HOME"
    NEWLINE@49..50 "\n"
"##
    );
}

#[test]
fn test_recipe_references() {
    assert_eq!(
        references(
            "all:\n\techo $@ $< $^ $* $% $? $+ $| $(@D) ${^F} $1 $(1) $(X) ${Y}\n",
            None
        ),
        vec![
            r("$@", "@"),
            r("$<", "<"),
            r("$^", "^"),
            r("$*", "*"),
            r("$%", "%"),
            r("$?", "?"),
            r("$+", "+"),
            r("$|", "|"),
            r("$(@D)", "@D"),
            r("${^F}", "^F"),
            r("$1", "1"),
            r("$(1)", "1"),
            r("$(X)", "X"),
            r("${Y}", "Y"),
        ]
    );
}

#[test]
fn test_recipe_function_calls() {
    let makefile = parse(
        "all:\n\t$(foreach f,$(FILES),$(call cmd,$(f))) $(shell ls)\n",
        None,
    )
    .root();
    let refs: Vec<_> = makefile.variable_references().collect();
    assert_eq!(
        refs.iter()
            .map(|r| (r.to_string(), r.is_function_call(), r.argument_count()))
            .collect::<Vec<_>>(),
        vec![
            (
                "$(foreach f,$(FILES),$(call cmd,$(f)))".to_string(),
                true,
                3
            ),
            ("$(FILES)".to_string(), false, 0),
            ("$(call cmd,$(f))".to_string(), true, 2),
            ("$(f)".to_string(), false, 0),
            ("$(shell ls)".to_string(), true, 1),
        ]
    );
}

#[test]
fn test_recipe_escaped_dollar() {
    // `$$` is a dollar for the shell, so the parentheses after it are
    // shell syntax.
    assert_eq!(
        references("all:\n\techo $$(date) $${HOME} $$$(X) $$$$\n", None),
        vec![r("$(X)", "X")]
    );
}

#[test]
fn test_recipe_shell_parentheses() {
    let code =
        "all:\n\tcase $(X) in a) echo a;; (b) echo ${B};; esac\n\techo '$(' $(Y)\n\techo $(Z)\n";
    assert_eq!(
        references(code, None),
        vec![
            r("$(X)", "X"),
            r("${B}", "B"),
            r("$(Y)", "Y"),
            r("$(Z)", "Z")
        ]
    );
}

#[test]
fn test_recipe_unterminated_reference() {
    // GNU make only reports this when expanding the recipe. The reference
    // does not take in the following lines.
    let code = "all:\n\techo $(X\n\techo $(Y)\nZ = 1\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    let makefile = parsed.root();
    assert_eq!(makefile.to_string(), code);
    let rule = makefile.rules().next().unwrap();
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo $(X", "echo $(Y)"]
    );
    assert_eq!(references(code, None), vec![r("$(Y)", "Y")]);
    // References inside the unterminated one are found.
    assert_eq!(
        references("all:\n\techo $(X $(Y)\n", None),
        vec![r("$(Y)", "Y")]
    );
    // Only the opening kind of delimiter is counted.
    assert_eq!(
        references("all:\n\techo ${X)} $(Y})\n", None),
        vec![r("${X)}", "X"), r("$(Y})", "Y")]
    );
}

#[test]
fn test_recipe_lone_dollar() {
    assert_eq!(
        references("all:\n\techo $\n\techo $) \\\n\t$\\\n\tx\n", None),
        vec![]
    );
}

#[test]
fn test_recipe_reference_spanning_continuation() {
    let code = "all:\n\t$(foreach f,$(FILES), \\\n\t\tinstall $(f);) \\\n\t$(X)\n";
    let recipe = recipe(code, None);
    assert_eq!(
        recipe.text(),
        "$(foreach f,$(FILES), \\\n\tinstall $(f);) \\\n$(X)"
    );
    assert_eq!(
        recipe
            .references()
            .map(|r| r.to_string())
            .collect::<Vec<_>>(),
        vec![
            "$(foreach f,$(FILES), \\\n\t\tinstall $(f);)",
            "$(FILES)",
            "$(f)",
            "$(X)",
        ]
    );
    let foreach = recipe.references().next().unwrap();
    assert_eq!(foreach.name(), Some("foreach".to_string()));
    assert_eq!(foreach.argument_count(), 3);
}

#[test]
fn test_recipe_reference_not_continued() {
    // An even number of backslashes does not continue the line.
    let code = "all:\n\techo $(X \\\\\n\t)\n";
    assert_eq!(references(code, None), vec![]);
    let rule = parse(code, None).root().rules().next().unwrap();
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo $(X \\\\", ")"]
    );
}

#[test]
fn test_recipe_hash_in_reference() {
    // make passes `#` in a recipe to the shell.
    let code = "all:\n\techo $(subst #,x,$(X)) # $(Y)\n";
    assert_eq!(
        references(code, None),
        vec![
            r("$(subst #,x,$(X))", "subst"),
            r("$(X)", "X"),
            r("$(Y)", "Y")
        ]
    );
    assert_eq!(recipe(code, None).text(), "echo $(subst #,x,$(X)) # $(Y)");
}

#[test]
fn test_recipe_comment_line() {
    // GNU make expands a line starting with `#` before passing it to the
    // shell; BSD make and nmake skip it.
    let code = "all:\n\t# $(X)\n\techo\n";
    assert_eq!(references(code, None), vec![r("$(X)", "X")]);
    assert_eq!(
        references(code, Some(MakefileVariant::POSIXMake)),
        vec![r("$(X)", "X")]
    );
    assert_eq!(references(code, Some(MakefileVariant::BSDMake)), vec![]);
    assert_eq!(references(code, Some(MakefileVariant::NMake)), vec![]);
    assert_eq!(recipe(code, None).shell_text(), "# $(X)");
}

#[test]
fn test_recipe_on_rule_line() {
    let code = "all: a ; @echo $(X) # $(Y)\n";
    assert_eq!(references(code, None), vec![r("$(X)", "X"), r("$(Y)", "Y")]);
    let recipe = recipe(code, None);
    assert_eq!(recipe.text(), "@echo $(X) # $(Y)");
    assert!(recipe.is_silent());
}

#[test]
fn test_recipe_prefix_references() {
    let code = ".RECIPEPREFIX = >\nall:\n>echo $(X)\n";
    assert_eq!(references(code, None), vec![r("$(X)", "X")]);
    assert_eq!(recipe(code, None).text(), "echo $(X)");
}

#[test]
fn test_recipe_bsd_modifiers() {
    let bsd = Some(MakefileVariant::BSDMake);
    // BSD make finds the end of an expression from its modifiers, so the
    // parenthesis in the `:S` modifier does not count.
    assert_eq!(
        references("all:\n\techo ${SRCS:M*.c} ${X:S/(/[/} ${:U$(Y)}\n", bsd),
        vec![
            r("${SRCS:M*.c}", "SRCS"),
            r("${X:S/(/[/}", "X"),
            ("${:U$(Y)}".to_string(), None),
            r("$(Y)", "Y"),
        ]
    );
    let refs: Vec<_> = parse("all:\n\techo ${SRCS:M*.c:S/a/b/}\n", bsd)
        .root()
        .variable_references()
        .collect();
    let parsed = refs[0].parse(MakefileVariant::BSDMake).unwrap();
    assert_eq!(parsed.name, "SRCS");
    assert_eq!(parsed.modifiers.len(), 2);
}

#[test]
fn test_recipe_nmake_references() {
    let nmake = Some(MakefileVariant::NMake);
    // A substitution ends at the first `)`.
    assert_eq!(
        references("all:\n\techo $(SRCS:.c=(x)\n", nmake),
        vec![r("$(SRCS:.c=(x)", "SRCS")]
    );
    // Inline file lines are searched, but references do not span them.
    let code = "all:\n\tlink @<<\n$(OBJS) $(X\n<<\n";
    assert_eq!(references(code, nmake), vec![r("$(OBJS)", "OBJS")]);
}

#[test]
fn test_recipe_old_variable_references_unchanged() {
    // The text scanner only looks at single lines and skips automatic
    // variables and function calls.
    let recipe = recipe(
        "all:\n\t$(foreach f,$(F), \\\n\t$(f)) $@ $(shell $(X))\n",
        None,
    );
    #[allow(deprecated)]
    let names: Vec<(String, std::ops::Range<usize>)> = recipe
        .variable_references()
        .iter()
        .map(|r| (r.name().to_string(), r.text_range().into()))
        .collect();
    assert_eq!(
        names,
        vec![
            ("F".to_string(), 20..21),
            ("f".to_string(), 29..30),
            ("X".to_string(), 46..47)
        ]
    );
}

fn recipe_tree(rule: &Rule) -> Vec<String> {
    rule.recipe_nodes()
        .map(|r| {
            r.references()
                .map(|r| r.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        })
        .collect()
}

#[test]
fn test_recipe_editing_references() {
    let mut rule: Rule = "all:\n\techo a\n".parse().unwrap();
    rule.push_command("echo $(B)");
    rule.replace_command(0, "echo $(A) $@");
    let first = rule.recipe_nodes().next().unwrap();
    first.insert_before("echo $(C)");
    first.insert_after("echo $(D)");
    assert_eq!(recipe_tree(&rule), vec!["$(C)", "$(A) $@", "$(D)", "$(B)"]);
    let mut first = rule.recipe_nodes().next().unwrap();
    first.replace_text("echo ${E}");
    first.set_prefix("@");
    assert_eq!(first.text(), "@echo ${E}");
    assert_eq!(recipe_tree(&rule), vec!["${E}", "$(A) $@", "$(D)", "$(B)"]);
    assert_eq!(
        rule.to_string(),
        "all:\n\t@echo ${E}\n\techo $(A) $@\n\techo $(D)\n\techo $(B)\n"
    );

    let rule = Rule::new(&["all"], &[], &["echo $(X)"]);
    assert_eq!(recipe_tree(&rule), vec!["$(X)"]);
}

#[test]
fn test_recipe_on_rule_line_moved() {
    let makefile: Makefile = "all: ; echo $(X)\n".parse().unwrap();
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes()
        .next()
        .unwrap()
        .insert_before("echo $(Y)");
    assert_eq!(makefile.to_string(), "all:\n\techo $(Y)\n\techo $(X)\n");
    assert_eq!(recipe_tree(&rule), vec!["$(Y)", "$(X)"]);
}

#[test]
fn test_define_body_references() {
    let code = "define RULE\n$(1): $$($(1)_OBJS)\n\t$$(CC) -o $$@ $(LDFLAGS)\n$(foreach v,$(VARS),\n  $(info $(v)))\nendef\n";
    assert_eq!(
        references(code, None),
        vec![
            r("$(1)", "1"),
            r("$(1)", "1"),
            r("$(LDFLAGS)", "LDFLAGS"),
            r("$(foreach v,$(VARS),\n  $(info $(v)))", "foreach"),
            r("$(VARS)", "VARS"),
            r("$(info $(v))", "info"),
            r("$(v)", "v"),
        ]
    );
    let makefile = parse(code, None).root();
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(
        var.raw_value(),
        Some("$(1): $$($(1)_OBJS)\n\t$$(CC) -o $$@ $(LDFLAGS)\n$(foreach v,$(VARS),\n  $(info $(v)))\n".to_string())
    );
    assert_eq!(
        var.value(MakefileVariant::GNUMake),
        Some("$(1): $$($(1)_OBJS)\n\t$$(CC) -o $$@ $(LDFLAGS)\n$(foreach v,$(VARS),\n  $(info $(v)))".to_string())
    );
}

#[test]
fn test_define_body_hash_and_continuation() {
    // A define body has no comments, and its line continuations are kept.
    let code = "define X\na # $(A)\n$(B \\\n  c) \\\n$(D)\nendef\n";
    assert_eq!(
        references(code, None),
        vec![r("$(A)", "A"), r("$(B \\\n  c)", "B"), r("$(D)", "D")]
    );
    let var = parse(code, None)
        .root()
        .variable_definitions()
        .next()
        .unwrap();
    assert_eq!(
        var.value(MakefileVariant::GNUMake),
        Some("a # $(A)\n$(B c) $(D)".to_string())
    );
}

#[test]
fn test_define_body_unterminated_reference() {
    let code = "define X\n$(A\nendef\nY = $(B)\n";
    let parsed = parse(code, None);
    assert_eq!(parsed.errors, vec![]);
    assert_eq!(references(code, None), vec![r("$(B)", "B")]);
}

#[test]
fn test_nested_define_body_references() {
    let code = "define OUTER\ndefine $(1)_INNER\n$$(X) $(Y)\nendef\nendef\n";
    assert_eq!(references(code, None), vec![r("$(1)", "1"), r("$(Y)", "Y")]);
    let var = parse(code, None)
        .root()
        .variable_definitions()
        .next()
        .unwrap();
    assert_eq!(
        var.raw_value(),
        Some("define $(1)_INNER\n$$(X) $(Y)\nendef\n".to_string())
    );
}
