use super::*;
use crate::ast::makefile::MakefileItem;
use crate::MakefileVariant;

mod conditionals;
mod define;
mod editing;
mod errors;
mod export;
mod expression_statement;
mod general;
mod include;
mod line_col;
mod recipe_references;
mod recipes;
mod references;
mod rule_context;
mod rules;
mod variables;

fn top_level_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children().map(|c| c.kind()).collect()
}

fn error_kinds(input: &str, variant: Option<MakefileVariant>) -> Vec<ParseErrorKind> {
    let parsed = parse(input, variant);
    let kinds: Vec<_> = parsed.errors.iter().map(ErrorInfo::kind).collect();
    assert_eq!(
        parsed
            .positioned_errors
            .iter()
            .map(PositionedParseError::kind)
            .collect::<Vec<_>>(),
        kinds
    );
    kinds
}

/// Render the node structure (without tokens) of a parse tree, one node
/// per line, indented by depth.
fn node_kinds(node: &SyntaxNode) -> String {
    fn walk(node: &SyntaxNode, depth: usize, out: &mut String) {
        for child in node.children() {
            out.push_str(&format!("{}{:?}\n", "  ".repeat(depth), child.kind()));
            walk(&child, depth + 1, out);
        }
    }
    let mut out = String::new();
    walk(node, 0, &mut out);
    out
}
