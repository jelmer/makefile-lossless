use super::*;
use crate::ast::makefile::MakefileItem;
use crate::test_util::assert_matches_reparse;

fn parse_crlf(src: &str) -> Makefile {
    let makefile: Makefile = src.parse().unwrap();
    assert_eq!(makefile.to_string(), src);
    makefile
}

fn variables(makefile: &Makefile) -> Vec<(String, String)> {
    makefile
        .variable_definitions()
        .map(|v| (v.name().unwrap(), v.raw_value().unwrap()))
        .collect()
}

#[test]
fn test_assignments() {
    let makefile = parse_crlf("X = 1\r\nY := 2 # c\r\nZ =\r\n");
    assert_eq!(
        variables(&makefile),
        vec![
            ("X".to_string(), "1".to_string()),
            ("Y".to_string(), "2 ".to_string()),
            ("Z".to_string(), "".to_string()),
        ]
    );
}

#[test]
fn test_value_continuation() {
    let makefile = parse_crlf("Y = a \\\r\n  b\r\nZ = c\r\n");
    assert_eq!(
        variables(&makefile),
        vec![
            ("Y".to_string(), "a \\\n  b".to_string()),
            ("Z".to_string(), "c".to_string()),
        ]
    );
}

#[test]
fn test_rule_with_continuation_and_recipes() {
    let makefile =
        parse_crlf("all: a \\\r\n\tb\r\n\techo hi\r\n\techo a \\\r\n\t  b\r\n\t# note\r\n");
    let rules: Vec<_> = makefile.rules().collect();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["all"]);
    assert_eq!(rules[0].prerequisites().collect::<Vec<_>>(), vec!["a", "b"]);
    assert_eq!(
        rules[0].recipes().collect::<Vec<_>>(),
        vec!["echo hi", "echo a \\\n  b", ""]
    );
    let comments: Vec<_> = rules[0].recipe_nodes().map(|r| r.comment()).collect();
    assert_eq!(comments, vec![None, None, Some("# note".to_string())]);
}

#[test]
fn test_order_only_prerequisites() {
    let makefile = parse_crlf("all: a \\\r\n  b | c $(wildcard d \\\r\n  e)\r\n\techo hi\r\n");
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["a", "b"]);
    assert_eq!(
        rule.order_only_prerequisites().collect::<Vec<_>>(),
        vec!["c", "$(wildcard d e)"]
    );
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["echo hi"]);
}

#[test]
fn test_static_pattern_rule() {
    let makefile = parse_crlf("a.o b.o: \\\r\n  %.o: %.c \\\r\n  %.h | dir\r\n\tcc -c $<\r\n");
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a.o", "b.o"]);
    assert_eq!(rule.static_pattern(), Some("%.o".to_string()));
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["%.c", "%.h"]);
    assert_eq!(
        rule.order_only_prerequisites().collect::<Vec<_>>(),
        vec!["dir"]
    );
    assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["cc -c $<"]);
}

#[test]
fn test_define() {
    let makefile = parse_crlf("define FOO\r\nline1\r\nline2\r\nendef\r\nX = 1\r\n");
    assert_eq!(
        variables(&makefile),
        vec![
            ("FOO".to_string(), "line1\nline2\n".to_string()),
            ("X".to_string(), "1".to_string()),
        ]
    );
}

#[test]
fn test_conditional() {
    let makefile = parse_crlf("ifdef X\r\nA = 1\r\nelse\r\nA = 2\r\nendif\r\n");
    let conditional = makefile.conditionals().next().unwrap();
    assert_eq!(conditional.conditional_type(), Some("ifdef".to_string()));
    assert_eq!(conditional.condition(), Some("X".to_string()));
    assert_eq!(conditional.if_body(), Some("A = 1\n".to_string()));
    assert_eq!(conditional.else_body(), Some("A = 2\n".to_string()));
}

#[test]
fn test_ifeq() {
    let makefile = parse_crlf("ifeq ($(X),y)\r\nA = 1\r\nendif\r\n");
    let conditional = makefile.conditionals().next().unwrap();
    assert_eq!(
        conditional.ifeq_args(),
        Some(("$(X)".to_string(), "y".to_string()))
    );
    assert_eq!(conditional.if_body(), Some("A = 1\n".to_string()));
}

#[test]
fn test_comments() {
    let makefile = parse_crlf("# first\r\n# second\r\nX = 1\r\n");
    let item = makefile.items().next().unwrap();
    assert_eq!(
        item.preceding_comments().collect::<Vec<_>>(),
        vec!["first", "second"]
    );
}

#[test]
fn test_include() {
    let makefile = parse_crlf("include foo.mk\r\n-include bar.mk\r\n");
    assert_eq!(
        makefile.included_files().collect::<Vec<_>>(),
        vec!["foo.mk", "bar.mk"]
    );
}

#[test]
fn test_condition_continuation() {
    let makefile = parse_crlf("ifeq ($(X),\\\r\n  y)\r\nA = 1\r\nendif\r\n");
    let conditional = makefile.conditionals().next().unwrap();
    assert_eq!(conditional.condition(), Some("($(X), y)".to_string()));
    assert_eq!(
        conditional.ifeq_args(),
        Some(("$(X)".to_string(), "y".to_string()))
    );
}

#[test]
fn test_ifdef_continuation() {
    let makefile = parse_crlf("ifdef \\\r\n  X\r\nA = 1\r\nendif\r\n");
    assert_eq!(makefile.rules().count(), 0);
    let conditional = makefile.conditionals().next().unwrap();
    assert_eq!(conditional.condition(), Some("X".to_string()));
    assert_eq!(conditional.if_body(), Some("A = 1\n".to_string()));
}

#[test]
fn test_include_continuation() {
    let makefile = parse_crlf("include a.mk \\\r\n  b.mk\r\nc.mk: d\r\n");
    assert_eq!(
        makefile.included_files().collect::<Vec<_>>(),
        vec!["a.mk b.mk"]
    );
    assert_eq!(makefile.rules().count(), 1);
}

#[test]
fn test_vpath_continuation() {
    let makefile = parse_crlf("vpath \\\r\n  %.c src \\\r\n  lib\r\n");
    let Some(MakefileItem::Vpath(vpath)) = makefile.items().next() else {
        panic!("expected a vpath directive");
    };
    assert_eq!(vpath.pattern(), Some("%.c".to_string()));
    assert_eq!(vpath.directories_text(), Some("src lib".to_string()));
}

#[test]
fn test_export_continuation() {
    let makefile = parse_crlf("export X \\\r\n  Y\r\n");
    assert_eq!(makefile.rules().count(), 0);
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.names().collect::<Vec<_>>(), vec!["X", "Y"]);
}

#[test]
fn test_expression_statement() {
    let makefile = parse_crlf("$(info a \\\r\n  b)\r\n");
    let Some(MakefileItem::ExpressionStatement(stmt)) = makefile.items().next() else {
        panic!("expected an expression statement");
    };
    assert_eq!(stmt.expression(), "$(info a b)");
}

#[test]
fn test_vpath() {
    let makefile = parse_crlf("vpath %.c src:lib\r\n");
    let Some(MakefileItem::Vpath(vpath)) = makefile.items().next() else {
        panic!("expected a vpath directive");
    };
    assert_eq!(vpath.pattern(), Some("%.c".to_string()));
    assert_eq!(vpath.directories_text(), Some("src:lib".to_string()));
}

#[test]
fn test_bsd_for_and_directive() {
    // BSD make does not continue a line ending in a backslash and CRLF,
    // so continue these with LF.
    let src = ".for i in a \\\n  b\r\nX+= ${i}\r\n.endfor\r\n.error bad \\\n  thing\r\n";
    let makefile = Makefile::parse_with_variant(src, crate::MakefileVariant::BSDMake).tree();
    assert_eq!(makefile.to_string(), src);
    let items: Vec<_> = makefile.items().collect();
    let MakefileItem::ForLoop(for_loop) = &items[0] else {
        panic!("expected a for loop");
    };
    assert_eq!(for_loop.list(), Some("a  b".to_string()));
    let MakefileItem::Directive(directive) = &items[1] else {
        panic!("expected a directive");
    };
    assert_eq!(directive.argument(), Some("bad  thing".to_string()));
}

#[test]
fn test_inline_recipe() {
    let makefile = parse_crlf("all: dep ; echo a \\\r\n\tb # x\r\n\techo c\r\n");
    let rule = makefile.rules().next().unwrap();
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dep"]);
    let recipes: Vec<_> = rule.recipe_nodes().collect();
    assert_eq!(
        recipes.iter().map(|r| r.text()).collect::<Vec<_>>(),
        vec!["echo a \\\nb # x", "echo c"]
    );
    assert_eq!(
        recipes.iter().map(|r| r.shell_text()).collect::<Vec<_>>(),
        vec!["echo a \\\nb # x", "echo c"]
    );
}

#[test]
fn test_inline_recipe_continuation_after_hash() {
    let makefile = parse_crlf("all: ; echo hi # x \\\r\n\techo more\r\n\techo next\r\n");
    let rule = makefile.rules().next().unwrap();
    let recipes: Vec<_> = rule.recipe_nodes().collect();
    assert_eq!(
        recipes.iter().map(|r| r.shell_text()).collect::<Vec<_>>(),
        vec!["echo hi # x \\\necho more", "echo next"]
    );
}

#[test]
fn test_insert_before_inline_recipe() {
    let makefile = parse_crlf("all: dep ; echo hi\r\n");
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes()
        .next()
        .unwrap()
        .insert_before("echo first");
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo first", "echo hi"]
    );
    assert_eq!(
        makefile.to_string(),
        "all: dep\r\n\techo first\r\n\techo hi\r\n"
    );
}

#[test]
fn test_insert_before_inline_recipe_without_newline() {
    let makefile = parse_crlf("X = 1\r\nall: ; echo hi");
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes()
        .next()
        .unwrap()
        .insert_before("echo first");
    assert_eq!(
        makefile.to_string(),
        "X = 1\r\nall:\r\n\techo first\r\n\techo hi"
    );
}

#[test]
fn test_recipe_insert_after() {
    let makefile = parse_crlf("all:\r\n\techo a\r\n");
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().next().unwrap().insert_after("echo b");
    assert_eq!(makefile.to_string(), "all:\r\n\techo a\r\n\techo b\r\n");
}

#[test]
fn test_recipe_replace_text_without_newline() {
    let makefile = parse_crlf("all:\r\n\techo a");
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().next().unwrap().replace_text("echo b");
    assert_eq!(makefile.to_string(), "all:\r\n\techo b\r\n");
}

#[test]
fn test_rule_commands() {
    let makefile = parse_crlf("all:\r\n\techo a\r\n");
    let mut rule = makefile.rules().next().unwrap();
    rule.push_command("echo c");
    assert!(rule.insert_command(2, "echo d"));
    assert!(rule.insert_command(0, "echo 0"));
    assert!(rule.replace_command(1, "echo b"));
    assert_eq!(
        makefile.to_string(),
        "all:\r\n\techo 0\r\n\techo b\r\n\techo c\r\n\techo d\r\n"
    );
}

#[test]
fn test_add_rule() {
    let mut makefile = parse_crlf("X = 1\r\nall:\r\n");
    makefile.add_rule("new");
    makefile.add_phony_target("all").unwrap();
    assert_eq!(
        makefile.to_string(),
        "X = 1\r\nall:\r\n\r\nnew:\r\n\r\n.PHONY: all\r\n"
    );
}

#[test]
fn test_insert_rule() {
    let mut makefile = parse_crlf("a:\r\nb:\r\n");
    makefile
        .insert_rule(0, parse_crlf("first:\r\n").rules().next().unwrap())
        .unwrap();
    makefile
        .insert_rule(2, parse_crlf("middle:\r\n").rules().next().unwrap())
        .unwrap();
    makefile
        .insert_rule(4, parse_crlf("last:\r\n").rules().next().unwrap())
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        "first:\r\n\r\na:\r\n\r\nmiddle:\r\n\r\nb:\r\n\r\nlast:\r\n"
    );
}

#[test]
fn test_add_include() {
    let mut makefile = parse_crlf("X = 1\r\n");
    makefile.add_include("a.mk").unwrap();
    makefile.insert_include(2, "c.mk").unwrap();
    let first = makefile.items().next().unwrap();
    makefile.insert_include_after(&first, "b.mk").unwrap();
    assert_eq!(
        makefile.to_string(),
        "include a.mk\r\ninclude b.mk\r\nX = 1\r\ninclude c.mk\r\n"
    );
}

#[test]
fn test_add_conditional() {
    let mut makefile = parse_crlf("X = 1\r\n");
    makefile
        .add_conditional("ifdef", "DEBUG", "Y = 1\n\nZ = 1\n", Some("Y = 2\n"))
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        "X = 1\r\n\r\nifdef DEBUG\r\nY = 1\r\n\r\nZ = 1\r\nelse\r\nY = 2\r\nendif\r\n"
    );
}

#[test]
fn test_add_conditional_body_without_trailing_newline() {
    let mut makefile = parse_crlf("X = 1\r\n");
    makefile
        .add_conditional("ifdef", "DEBUG", "Y = 1\r\nZ = 1", Some("Y = 2"))
        .unwrap();
    let text = makefile.to_string();
    assert_eq!(
        text,
        "X = 1\r\n\r\nifdef DEBUG\r\nY = 1\r\nZ = 1\r\nelse\r\nY = 2\r\nendif\r\n"
    );
    assert_eq!(parse_crlf(&text).to_string(), text);
}

#[test]
fn test_add_conditional_with_items() {
    let mut makefile = parse_crlf("X = 1\r\n");
    let items = parse_crlf("Y = 1\r\nY = 2\r\n");
    let mut items = items.items();
    makefile
        .add_conditional_with_items("ifdef", "DEBUG", items.next(), Some(items.next()))
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        "X = 1\r\n\r\nifdef DEBUG\r\nY = 1\r\nelse\r\nY = 2\r\nendif\r\n"
    );
}

#[test]
fn test_conditional_add_else_item() {
    let makefile = parse_crlf("ifdef X\r\nY = 1\r\nendif\r\n");
    let item = parse_crlf("Y = 2\r\n").items().next().unwrap();
    makefile.conditionals().next().unwrap().add_else_item(item);
    assert_eq!(
        makefile.to_string(),
        "ifdef X\r\nY = 1\r\nelse\r\nY = 2\r\nendif\r\n"
    );
}

fn item_without_newline(src: &str) -> MakefileItem {
    let item = parse_crlf(src).items().next().unwrap();
    assert_eq!(item.syntax().to_string(), src);
    item
}

#[test]
fn test_conditional_add_if_item_without_newline() {
    let makefile = parse_crlf("ifdef X\r\nendif\r\n");
    let mut cond = makefile.conditionals().next().unwrap();
    cond.add_if_item(item_without_newline("a:\r\n\tcmd"));
    assert_eq!(makefile.to_string(), "ifdef X\r\na:\r\n\tcmd\r\nendif\r\n");
}

#[test]
fn test_conditional_add_else_item_without_newline() {
    let makefile = parse_crlf("ifdef X\r\nY = 1\r\nendif\r\n");
    let mut cond = makefile.conditionals().next().unwrap();
    cond.add_else_item(item_without_newline("Y = 2"));
    assert_eq!(
        makefile.to_string(),
        "ifdef X\r\nY = 1\r\nelse\r\nY = 2\r\nendif\r\n"
    );
}

#[test]
fn test_item_replace_and_insert_without_newline() {
    let makefile = parse_crlf("X = 1\r\nY = 1\r\n");
    let mut first = makefile.items().next().unwrap();
    first.insert_after(item_without_newline("B = 1")).unwrap();
    first.insert_before(item_without_newline("A = 1")).unwrap();
    first.replace(item_without_newline("Z = 1")).unwrap();
    assert_eq!(makefile.to_string(), "A = 1\r\nZ = 1\r\nB = 1\r\nY = 1\r\n");
}

#[test]
fn test_replace_and_insert_rule_without_newline() {
    let mut makefile = parse_crlf("a:\r\nb:\r\n");
    makefile
        .replace_rule(0, "c:\r\n\tcmd".parse().unwrap())
        .unwrap();
    makefile.insert_rule(2, "d:".parse().unwrap()).unwrap();
    assert_eq!(makefile.to_string(), "c:\r\n\tcmd\r\nb:\r\n\r\nd:\r\n");
}

#[test]
fn test_push_command_after_unterminated_recipe() {
    let makefile = parse_crlf("a:\r\n\tcmd");
    makefile.rules().next().unwrap().push_command("x");
    assert_eq!(makefile.to_string(), "a:\r\n\tcmd\r\n\tx\r\n");
}

#[test]
fn test_insert_command_after_unterminated_rule_line() {
    let makefile = parse_crlf("X = 1\r\na: b");
    assert!(makefile.rules().next().unwrap().insert_command(0, "x"));
    assert_eq!(makefile.to_string(), "X = 1\r\na: b\r\n\tx\r\n");
}

#[test]
fn test_recipe_insert_after_unterminated() {
    let makefile = parse_crlf("a:\r\n\tcmd");
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().next().unwrap().insert_after("x");
    assert_eq!(makefile.to_string(), "a:\r\n\tcmd\r\n\tx\r\n");
}

#[test]
fn test_add_after_unterminated_line() {
    let mut makefile = parse_crlf("X = 1\r\nY = 1");
    makefile.add_rule("b");
    assert_eq!(makefile.to_string(), "X = 1\r\nY = 1\r\n\r\nb:\r\n");

    let mut makefile = parse_crlf("X = 1\r\nY = 1");
    makefile
        .add_conditional("ifdef", "D", "Z = 1\n", None)
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        "X = 1\r\nY = 1\r\n\r\nifdef D\r\nZ = 1\r\nendif\r\n"
    );

    let mut makefile = parse_crlf("X = 1\r\na:");
    makefile.insert_rule(1, "b:\n".parse().unwrap()).unwrap();
    assert_eq!(makefile.to_string(), "X = 1\r\na:\r\n\r\nb:\r\n");

    let mut makefile = parse_crlf("X = 1\r\nY = 1");
    makefile.insert_include(2, "a.mk").unwrap();
    assert_eq!(makefile.to_string(), "X = 1\r\nY = 1\r\ninclude a.mk\r\n");
}

#[test]
fn test_item_insert_after_unterminated() {
    let makefile = parse_crlf("X = 1\r\nY = 1");
    let new_item = parse_crlf("Z = 1\r\n").items().next().unwrap();
    makefile
        .items()
        .nth(1)
        .unwrap()
        .insert_after(new_item)
        .unwrap();
    assert_eq!(makefile.to_string(), "X = 1\r\nY = 1\r\nZ = 1\r\n");
}

#[test]
fn test_add_else_item_to_unterminated_conditional() {
    let (makefile, _) = Makefile::from_str_relaxed("ifdef X\r\nY = 1");
    let item = parse_crlf("Y = 2\r\n").items().next().unwrap();
    makefile.conditionals().next().unwrap().add_else_item(item);
    assert_eq!(
        makefile.to_string(),
        "ifdef X\r\nY = 1\r\nelse\r\nY = 2\r\n"
    );
}

#[test]
fn test_conditional_add_endif() {
    let (makefile, _) = Makefile::from_str_relaxed("ifdef X\r\nY = 1");
    assert!(makefile.conditionals().next().unwrap().add_endif().unwrap());
    assert_eq!(makefile.to_string(), "ifdef X\r\nY = 1\r\nendif\r\n");
}

#[test]
fn test_add_comment() {
    let makefile = parse_crlf("X = 1\r\n");
    makefile.items().next().unwrap().add_comment("hi").unwrap();
    assert_eq!(makefile.to_string(), "# hi\r\nX = 1\r\n");
}

fn parse_lone_cr(src: &str, variant: Option<crate::MakefileVariant>) -> Makefile {
    let parsed = match variant {
        Some(variant) => Makefile::parse_with_variant(src, variant),
        None => crate::Parse::<Makefile>::parse_makefile(src),
    };
    assert_eq!(parsed.errors(), &[]);
    let makefile = parsed.tree();
    assert_eq!(makefile.to_string(), src);
    makefile
}

const VARIANTS: [Option<crate::MakefileVariant>; 5] = [
    None,
    Some(crate::MakefileVariant::GNUMake),
    Some(crate::MakefileVariant::BSDMake),
    Some(crate::MakefileVariant::POSIXMake),
    Some(crate::MakefileVariant::NMake),
];

#[test]
fn test_lone_cr_in_value() {
    for variant in VARIANTS {
        let makefile = parse_lone_cr("X = a\rb\nY = c\r\r\nZ = d\\\re\n", variant);
        assert_eq!(makefile.rules().count(), 0);
        assert_eq!(
            variables(&makefile),
            vec![
                ("X".to_string(), "a\rb".to_string()),
                ("Y".to_string(), "c\r".to_string()),
                ("Z".to_string(), "d\\\re".to_string()),
            ]
        );
    }
}

#[test]
fn test_lone_cr_in_comment() {
    for variant in VARIANTS {
        let makefile = parse_lone_cr("# a\rb: c\nX = 1\n", variant);
        assert_eq!(makefile.rules().count(), 0);
        assert_eq!(
            variables(&makefile),
            vec![("X".to_string(), "1".to_string())]
        );
    }
}

#[test]
fn test_lone_cr_in_recipe() {
    for variant in VARIANTS {
        let makefile = parse_lone_cr("all: a\rb\n\techo a\rb\n\techo c\r\n", variant);
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["all"]);
        // BSD make splits words on a lone CR, but not recipes.
        let prerequisites = if variant == Some(crate::MakefileVariant::BSDMake) {
            vec!["a", "b"]
        } else {
            vec!["a\rb"]
        };
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), prerequisites);
        assert_eq!(
            rule.recipes().collect::<Vec<_>>(),
            vec!["echo a\rb", "echo c"]
        );
    }
}

#[test]
fn test_lone_cr_in_quoted_value() {
    let makefile = parse_lone_cr("X = a \"b\rc\" \\\n  d\n", None);
    assert_eq!(
        variables(&makefile),
        vec![("X".to_string(), "a \"b\rc\" \\\n  d".to_string())]
    );
}

#[test]
fn test_lone_cr_in_inline_recipe_comment() {
    let makefile = parse_lone_cr("all: ; echo a # b\rc \\\n\td\n", None);
    let rule = makefile.rules().next().unwrap();
    assert_eq!(
        rule.recipe_nodes().map(|r| r.text()).collect::<Vec<_>>(),
        vec!["echo a # b\rc \\\nd"]
    );
}

#[test]
fn test_lone_cr_after_semicolon() {
    let makefile = parse_lone_cr("$(info a); echo b\r", None);
    let Some(MakefileItem::ExpressionStatement(stmt)) = makefile.items().next() else {
        panic!("expected an expression statement");
    };
    assert_eq!(stmt.after_semicolon(), Some("echo b\r".to_string()));
}

#[test]
fn test_lone_cr_line_ending() {
    let makefile = parse_lone_cr("X = a\rb\nall:\n\techo a\n", None);
    let rule = makefile.rules().next().unwrap();
    rule.recipe_nodes().next().unwrap().insert_after("echo b");
    assert_eq!(makefile.to_string(), "X = a\rb\nall:\n\techo a\n\techo b\n");
}

#[test]
fn test_bsd_backslash_before_crlf() {
    // BSD make takes the backslash as escaping the CR, so the line is
    // not continued.
    let bsd = Some(crate::MakefileVariant::BSDMake);
    let makefile = parse_lone_cr("X = a \\\r\nY = b\r\n", bsd);
    assert_eq!(
        variables(&makefile),
        vec![
            ("X".to_string(), "a \\\r".to_string()),
            ("Y".to_string(), "b".to_string()),
        ]
    );
    let makefile = parse_lone_cr("all: a \\\r\nb:\r\n", bsd);
    let targets: Vec<_> = makefile
        .rules()
        .flat_map(|r| r.targets().collect::<Vec<_>>())
        .collect();
    assert_eq!(targets, vec!["all", "b"]);
    let makefile = parse_lone_cr("# c \\\r\nX = 1\r\n", bsd);
    assert_eq!(
        variables(&makefile),
        vec![("X".to_string(), "1".to_string())]
    );
    let makefile = parse_lone_cr("all:\r\n\techo a \\\r\n\techo b\r\n", bsd);
    let rule = makefile.rules().next().unwrap();
    assert_eq!(
        rule.recipes().collect::<Vec<_>>(),
        vec!["echo a \\\r", "echo b"]
    );
}

#[test]
fn test_bsd_cr_separates_words() {
    // BSD make splits words on anything isspace() accepts.
    for space in ['\r', '\x0b', '\x0c'] {
        let src = format!("a{space}b c: d{space}e f\n");
        let makefile = parse_lone_cr(&src, Some(crate::MakefileVariant::BSDMake));
        let rule = makefile.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["a", "b", "c"]);
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["d", "e", "f"]
        );
        for variant in VARIANTS {
            if variant == Some(crate::MakefileVariant::BSDMake) {
                continue;
            }
            let makefile = parse_lone_cr(&src, variant);
            let rule = makefile.rules().next().unwrap();
            assert_eq!(
                rule.targets().collect::<Vec<_>>(),
                vec![format!("a{space}b"), "c".to_string()],
                "{variant:?}"
            );
            assert_eq!(
                rule.prerequisites().collect::<Vec<_>>(),
                vec![format!("d{space}e"), "f".to_string()],
                "{variant:?}"
            );
        }
    }
}

#[test]
fn test_bsd_cr_around_assignment() {
    let makefile = parse_lone_cr(
        "X\r=\ry\rz\r\x0b\r\n",
        Some(crate::MakefileVariant::BSDMake),
    );
    let var = makefile.variable_definitions().next().unwrap();
    assert_eq!(var.name(), Some("X".to_string()));
    assert_eq!(
        var.value_for(crate::MakefileVariant::BSDMake),
        Some("y\rz".to_string())
    );
}

#[test]
fn test_backslash_before_crlf_continues() {
    for variant in VARIANTS {
        if variant == Some(crate::MakefileVariant::BSDMake) {
            continue;
        }
        let makefile = parse_lone_cr("X = a \\\r\nY = b\r\n", variant);
        assert_eq!(
            variables(&makefile),
            vec![("X".to_string(), "a \\\nY = b".to_string())],
            "{variant:?}"
        );
        let makefile = parse_lone_cr("all:\r\n\techo a \\\r\n\techo b\r\n", variant);
        let rule = makefile.rules().next().unwrap();
        assert_eq!(
            rule.recipes().collect::<Vec<_>>(),
            vec!["echo a \\\necho b"],
            "{variant:?}"
        );
    }
}

fn lf_item(src: &str) -> MakefileItem {
    src.parse::<Makefile>().unwrap().items().next().unwrap()
}

#[test]
fn test_insert_rule_adopts_line_ending() {
    let mut makefile = parse_crlf("all:\r\n");
    makefile.insert_rule(1, "b:\n".parse().unwrap()).unwrap();
    assert_eq!(makefile.to_string(), "all:\r\n\r\nb:\r\n");
    makefile
        .insert_rule(0, "a:\n\techo\n".parse().unwrap())
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        "a:\r\n\techo\r\n\r\nall:\r\n\r\nb:\r\n"
    );
}

#[test]
fn test_replace_rule_adopts_line_ending() {
    let mut makefile = parse_crlf("all:\r\nb:\r\n");
    makefile
        .replace_rule(0, "a:\n\techo\n".parse().unwrap())
        .unwrap();
    assert_eq!(makefile.to_string(), "a:\r\n\techo\r\nb:\r\n");
    assert_matches_reparse(&makefile);

    // The only line ending of the file is replaced, so the file's line
    // ending is that of the old rule.
    let mut makefile = parse_crlf("all:\r\n");
    makefile.replace_rule(0, "a:\n".parse().unwrap()).unwrap();
    assert_eq!(makefile.to_string(), "a:\r\n");
}

#[test]
fn test_lf_file_adopts_line_ending() {
    let mut makefile: Makefile = "all:\n".parse().unwrap();
    makefile
        .insert_rule(1, "b:\r\n\techo\r\n".parse().unwrap())
        .unwrap();
    assert_eq!(makefile.to_string(), "all:\n\nb:\n\techo\n");
}

#[test]
fn test_item_replace_and_insert_adopt_line_ending() {
    let makefile = parse_crlf("X = 1\r\nY = 1\r\n");
    let mut first = makefile.items().next().unwrap();
    first.insert_after(lf_item("b:\n\tcmd\n")).unwrap();
    first.insert_before(lf_item("A = 1\n")).unwrap();
    first.replace(lf_item("Z = 1\n")).unwrap();
    assert_eq!(
        makefile.to_string(),
        "A = 1\r\nZ = 1\r\nb:\r\n\tcmd\r\nY = 1\r\n"
    );
    assert_matches_reparse(&makefile);
}

#[test]
fn test_add_if_and_else_item_adopt_line_ending() {
    let makefile = parse_crlf("ifdef X\r\nendif\r\n");
    let mut conditional = makefile.conditionals().next().unwrap();
    conditional.add_if_item(lf_item("a:\n\tcmd\n"));
    conditional.add_else_item(lf_item("B = 1\n"));
    assert_eq!(
        makefile.to_string(),
        "ifdef X\r\na:\r\n\tcmd\r\nelse\r\nB = 1\r\nendif\r\n"
    );
}

#[test]
fn test_add_conditional_with_items_adopts_line_ending() {
    let mut makefile = parse_crlf("all:\r\n");
    makefile
        .add_conditional_with_items(
            "ifdef",
            "X",
            vec![lf_item("a:\n\tcmd\n")],
            Some(vec![lf_item("B = 1\n")]),
        )
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        "all:\r\n\r\nifdef X\r\na:\r\n\tcmd\r\nelse\r\nB = 1\r\nendif\r\n"
    );
}

#[test]
fn test_inserted_continuation_line_endings_kept() {
    // Whether a backslash before a CRLF continues the line depends on the
    // make variant, so line continuations are left alone.
    let mut makefile = parse_crlf("all:\r\n");
    makefile
        .insert_rule(
            1,
            "b: x \\\n y\n\techo \\\n\tz # c \\\n d\n".parse().unwrap(),
        )
        .unwrap();
    assert_eq!(
        makefile.to_string(),
        "all:\r\n\r\nb: x \\\n y\r\n\techo \\\n\tz # c \\\n d\r\n"
    );
    let reparsed: Makefile = makefile.to_string().parse().unwrap();
    let rule = reparsed.rules().nth(1).unwrap();
    assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["x", "y"]);
    assert_eq!(rule.recipe_nodes().count(), 1);
}

#[test]
fn test_set_value_define() {
    for (text, value, expected) in [
        (
            "define X\r\nold\r\nendef\r\n",
            "a\nb",
            "define X\r\na\r\nb\r\nendef\r\n",
        ),
        (
            "define X\r\nold\r\nendef\r\n",
            "a\r\nb\r\n",
            "define X\r\na\r\nb\r\nendef\r\n",
        ),
        ("define X\r\nendef\r\n", "a", "define X\r\na\r\nendef\r\n"),
        ("define X\r\nold\r\nendef\r\n", "", "define X\r\nendef\r\n"),
        ("define X\r\nold\r\nendef", "a", "define X\r\na\r\nendef"),
    ] {
        let makefile: Makefile = text.parse().unwrap();
        let mut var = makefile.variable_definitions().next().unwrap();
        var.set_value(value);
        assert_eq!(makefile.to_string(), expected, "{text:?}");
        assert_matches_reparse(&makefile);
        let value = value.replace("\r\n", "\n");
        let value = if value.is_empty() || value.ends_with('\n') {
            value
        } else {
            format!("{value}\n")
        };
        assert_eq!(var.raw_value(), Some(value), "{text:?}");
    }
}
