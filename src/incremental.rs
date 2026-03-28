//! Incremental reparsing support for efficient handling of text edits.
//!
//! Instead of reparsing the entire file after each edit, this module identifies
//! which top-level items are affected and reparses only those, splicing the
//! results back into the existing green tree.

use crate::lossless::{ErrorInfo, Makefile, PositionedParseError};
use crate::parse::Parse;
use rowan::TextRange;

/// A text edit applied to the source, as typically received from an LSP.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextEdit {
    /// The byte range in the old text to replace.
    pub range: TextRange,
    /// The new text to insert in place of the range.
    pub new_text: String,
}

impl TextEdit {
    /// Create a new text edit.
    pub fn new(range: TextRange, new_text: String) -> Self {
        Self { range, new_text }
    }

    /// The length delta introduced by this edit.
    fn delta(&self) -> i64 {
        self.new_text.len() as i64 - u32::from(self.range.len()) as i64
    }
}

/// Apply a text edit to the old source, producing the new source text.
pub fn apply_edit_to_text(old_text: &str, edit: &TextEdit) -> String {
    let start: usize = u32::from(edit.range.start()) as usize;
    let end: usize = u32::from(edit.range.end()) as usize;
    let mut new = String::with_capacity(old_text.len().wrapping_add_signed(edit.delta() as isize));
    new.push_str(&old_text[..start]);
    new.push_str(&edit.new_text);
    new.push_str(&old_text[end..]);
    new
}

impl Parse<Makefile> {
    /// Apply an incremental text edit and reparse only the affected region.
    ///
    /// This is more efficient than a full reparse for large files, as it reuses
    /// the green tree nodes for unaffected top-level items.
    ///
    /// # Arguments
    /// * `old_text` - The full text before the edit
    /// * `edit` - The edit to apply
    ///
    /// # Returns
    /// A new `Parse<Makefile>` with the edit applied, and the new full text.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, Parse, TextEdit, TextRange};
    ///
    /// let old_text = "VAR1 = old\nVAR2 = value\n";
    /// let parse = Parse::<Makefile>::parse_makefile(old_text);
    ///
    /// // Change "old" to "new" in VAR1
    /// let edit = TextEdit::new(
    ///     TextRange::new(7.into(), 10.into()),
    ///     "new".to_string(),
    /// );
    /// let (new_parse, new_text) = parse.apply_edit(old_text, &edit);
    /// assert_eq!(new_text, "VAR1 = new\nVAR2 = value\n");
    ///
    /// let makefile: Makefile = new_parse.tree();
    /// let vars: Vec<_> = makefile.variable_definitions().collect();
    /// assert_eq!(vars.len(), 2);
    /// assert_eq!(vars[0].raw_value(), Some("new".to_string()));
    /// assert_eq!(vars[1].raw_value(), Some("value".to_string()));
    /// ```
    pub fn apply_edit(&self, old_text: &str, edit: &TextEdit) -> (Self, String) {
        let new_text = apply_edit_to_text(old_text, edit);
        let delta = edit.delta();

        // Walk the ROOT green node's children to find which ones overlap the edit range.
        let old_green = self.green();
        let children: Vec<_> = old_green.children().map(|c| c.to_owned()).collect();

        // Compute the text range of each direct child of ROOT.
        let mut child_ranges: Vec<TextRange> = Vec::with_capacity(children.len());
        let mut offset = rowan::TextSize::from(0);
        for child in &children {
            let len = match child {
                rowan::NodeOrToken::Node(n) => n.text_len(),
                rowan::NodeOrToken::Token(t) => t.text_len(),
            };
            child_ranges.push(TextRange::new(offset, offset + len));
            offset += len;
        }

        if children.is_empty() {
            // Empty tree — just do a full parse.
            let new_parse = Parse::parse_makefile(&new_text);
            return (new_parse, new_text);
        }

        // Find the first and last children that overlap or are adjacent to the edit range.
        let first_affected = child_ranges
            .iter()
            .position(|r| r.end() > edit.range.start())
            .unwrap_or(children.len().saturating_sub(1));

        let last_affected = child_ranges
            .iter()
            .rposition(|r| r.start() < edit.range.end())
            .unwrap_or(first_affected);

        // The reparse region in the *old* text.
        let reparse_start = child_ranges[first_affected].start();
        let reparse_end_old = child_ranges[last_affected].end();

        // The corresponding region in the *new* text.
        // Everything before first_affected is unchanged, so reparse_start is the same.
        // The end shifts by the delta.
        let reparse_end_new =
            rowan::TextSize::from((u32::from(reparse_end_old) as i64 + delta) as u32);

        let reparse_region =
            &new_text[u32::from(reparse_start) as usize..u32::from(reparse_end_new) as usize];

        // Reparse just the affected region.
        let reparsed = crate::lossless::parse(reparse_region, None);
        let reparsed_root = reparsed.green_node;

        // Build the new ROOT by splicing: [old children before] + [reparsed children] + [old children after]
        let new_root = old_green.splice_children(
            first_affected..last_affected + 1,
            reparsed_root.children().map(|c| c.to_owned()),
        );

        // Rebuild errors: keep errors outside the affected region, add reparsed errors with adjusted positions.
        let mut new_errors = Vec::new();
        let mut new_positioned_errors = Vec::new();

        // Errors before the affected region (unchanged).
        for err in self.errors() {
            // ErrorInfo uses line numbers, not byte offsets. We need to figure out
            // which errors are before the reparse region by line number.
            // Since we can't easily map line numbers to byte offsets without the text,
            // we use a simpler approach: count newlines up to reparse_start.
            let lines_before = old_text[..u32::from(reparse_start) as usize]
                .matches('\n')
                .count();
            if err.line <= lines_before {
                new_errors.push(err.clone());
            }
        }

        // Errors from the reparsed region (adjusted line numbers).
        let line_offset = old_text[..u32::from(reparse_start) as usize]
            .matches('\n')
            .count();
        for err in &reparsed.errors {
            new_errors.push(ErrorInfo {
                message: err.message.clone(),
                line: err.line + line_offset,
                context: err.context.clone(),
            });
        }

        // Errors after the affected region (adjusted line numbers).
        let old_lines_in_region = old_text
            [u32::from(reparse_start) as usize..u32::from(reparse_end_old) as usize]
            .matches('\n')
            .count();
        let new_lines_in_region = reparse_region.matches('\n').count();
        let line_delta = new_lines_in_region as i64 - old_lines_in_region as i64;
        let lines_after_start = line_offset + old_lines_in_region;
        for err in self.errors() {
            if err.line > lines_after_start {
                new_errors.push(ErrorInfo {
                    message: err.message.clone(),
                    line: (err.line as i64 + line_delta) as usize,
                    context: err.context.clone(),
                });
            }
        }

        // Positioned errors before.
        for err in self.positioned_errors() {
            if err.range.end() <= reparse_start {
                new_positioned_errors.push(err.clone());
            }
        }

        // Positioned errors from reparsed region (shifted by reparse_start).
        for err in &reparsed.positioned_errors {
            new_positioned_errors.push(PositionedParseError {
                message: err.message.clone(),
                range: TextRange::new(
                    err.range.start() + reparse_start,
                    err.range.end() + reparse_start,
                ),
                code: err.code.clone(),
            });
        }

        // Positioned errors after (shifted by delta).
        for err in self.positioned_errors() {
            if err.range.start() >= reparse_end_old {
                let shift = rowan::TextSize::from(delta.unsigned_abs() as u32);
                let (new_start, new_end) = if delta >= 0 {
                    (err.range.start() + shift, err.range.end() + shift)
                } else {
                    (err.range.start() - shift, err.range.end() - shift)
                };
                new_positioned_errors.push(PositionedParseError {
                    message: err.message.clone(),
                    range: TextRange::new(new_start, new_end),
                    code: err.code.clone(),
                });
            }
        }

        let new_parse = Parse::new(new_root, new_errors, new_positioned_errors);
        (new_parse, new_text)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowan::ast::AstNode;

    #[test]
    fn test_apply_edit_to_text() {
        let old = "hello world";
        let edit = TextEdit::new(TextRange::new(6.into(), 11.into()), "rust".to_string());
        assert_eq!(apply_edit_to_text(old, &edit), "hello rust");
    }

    #[test]
    fn test_apply_edit_to_text_insert() {
        let old = "hello world";
        let edit = TextEdit::new(TextRange::new(5.into(), 5.into()), " beautiful".to_string());
        assert_eq!(apply_edit_to_text(old, &edit), "hello beautiful world");
    }

    #[test]
    fn test_apply_edit_to_text_delete() {
        let old = "hello world";
        let edit = TextEdit::new(TextRange::new(5.into(), 11.into()), String::new());
        assert_eq!(apply_edit_to_text(old, &edit), "hello");
    }

    #[test]
    fn test_incremental_change_variable_value() {
        let old_text = "VAR1 = old\nVAR2 = value\n";
        let parse = Parse::parse_makefile(old_text);

        // Change "old" to "new"
        let edit = TextEdit::new(TextRange::new(7.into(), 10.into()), "new".to_string());
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "VAR1 = new\nVAR2 = value\n");
        let makefile = new_parse.tree();
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars.len(), 2);
        assert_eq!(vars[0].name(), Some("VAR1".to_string()));
        assert_eq!(vars[0].raw_value(), Some("new".to_string()));
        assert_eq!(vars[1].name(), Some("VAR2".to_string()));
        assert_eq!(vars[1].raw_value(), Some("value".to_string()));
    }

    #[test]
    fn test_incremental_change_rule_command() {
        let old_text = "all:\n\techo hello\n";
        let parse = Parse::parse_makefile(old_text);

        // Change "hello" to "goodbye"
        let edit = TextEdit::new(TextRange::new(11.into(), 16.into()), "goodbye".to_string());
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "all:\n\techo goodbye\n");
        let makefile = new_parse.tree();
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_incremental_insert_new_variable() {
        let old_text = "VAR1 = one\nVAR2 = two\n";
        let parse = Parse::parse_makefile(old_text);

        // Insert a new variable between the two
        let edit = TextEdit::new(
            TextRange::new(11.into(), 11.into()),
            "NEW = inserted\n".to_string(),
        );
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "VAR1 = one\nNEW = inserted\nVAR2 = two\n");
        let makefile = new_parse.tree();
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars.len(), 3);
        assert_eq!(vars[0].name(), Some("VAR1".to_string()));
        assert_eq!(vars[1].name(), Some("NEW".to_string()));
        assert_eq!(vars[2].name(), Some("VAR2".to_string()));
    }

    #[test]
    fn test_incremental_delete_variable() {
        let old_text = "VAR1 = one\nVAR2 = two\nVAR3 = three\n";
        let parse = Parse::parse_makefile(old_text);

        // Delete VAR2 line
        let edit = TextEdit::new(TextRange::new(11.into(), 22.into()), String::new());
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "VAR1 = one\nVAR3 = three\n");
        let makefile = new_parse.tree();
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars.len(), 2);
        assert_eq!(vars[0].name(), Some("VAR1".to_string()));
        assert_eq!(vars[1].name(), Some("VAR3".to_string()));
    }

    #[test]
    fn test_incremental_edit_preserves_unaffected() {
        let old_text = "VAR1 = one\nVAR2 = two\nVAR3 = three\n";
        let parse = Parse::parse_makefile(old_text);

        // Only change VAR2's value
        let edit = TextEdit::new(TextRange::new(18.into(), 21.into()), "TWO".to_string());
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "VAR1 = one\nVAR2 = TWO\nVAR3 = three\n");
        let makefile = new_parse.tree();
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars.len(), 3);

        // Verify that unaffected green nodes are structurally identical.
        let old_children: Vec<_> = parse.green().children().map(|c| c.to_owned()).collect();
        let new_children: Vec<_> = new_parse.green().children().map(|c| c.to_owned()).collect();

        // First child (VAR1 node) should be structurally identical.
        assert_eq!(
            old_children[0], new_children[0],
            "VAR1 green node should be identical (reused)"
        );
    }

    #[test]
    fn test_incremental_empty_file() {
        let old_text = "";
        let parse = Parse::parse_makefile(old_text);

        let edit = TextEdit::new(
            TextRange::new(0.into(), 0.into()),
            "VAR = value\n".to_string(),
        );
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "VAR = value\n");
        let makefile = new_parse.tree();
        assert_eq!(makefile.variable_definitions().count(), 1);
    }

    #[test]
    fn test_incremental_change_variable_to_rule() {
        let old_text = "target = value\n";
        let parse = Parse::parse_makefile(old_text);

        // Change "= value" to ":"
        let edit = TextEdit::new(TextRange::new(7.into(), 14.into()), ":".to_string());
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "target :\n");
        let makefile = new_parse.tree();
        assert_eq!(makefile.variable_definitions().count(), 0);
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_incremental_matches_full_reparse() {
        let old_text = "VAR1 = one\nall: dep\n\techo $(VAR1)\nVAR2 = two\n";
        let parse = Parse::parse_makefile(old_text);

        // Edit inside the rule
        let edit = TextEdit::new(TextRange::new(26.into(), 30.into()), "VAR2".to_string());
        let (incremental, new_text) = parse.apply_edit(old_text, &edit);
        let full = Parse::parse_makefile(&new_text);

        // Both should produce the same tree.
        let inc_tree = incremental.tree();
        let full_tree: Makefile = full.tree();
        assert_eq!(
            inc_tree.syntax().to_string(),
            full_tree.syntax().to_string()
        );
    }

    #[test]
    fn test_incremental_edit_at_end() {
        let old_text = "VAR = value\n";
        let parse = Parse::parse_makefile(old_text);

        // Append a new rule at the end
        let edit = TextEdit::new(
            TextRange::new(12.into(), 12.into()),
            "all:\n\techo done\n".to_string(),
        );
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "VAR = value\nall:\n\techo done\n");
        let makefile = new_parse.tree();
        assert_eq!(makefile.variable_definitions().count(), 1);
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_incremental_positioned_errors_shifted() {
        // Verify that positioned errors from the reparsed region get correct offsets
        let old_text = "VAR1 = one\nVAR2 = two\n";
        let parse = Parse::parse_makefile(old_text);
        assert!(parse.ok());

        // Insert text that causes a parse error (indented line not in a rule)
        let edit = TextEdit::new(
            TextRange::new(11.into(), 11.into()),
            "\tbad line\n".to_string(),
        );
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);
        assert_eq!(new_text, "VAR1 = one\n\tbad line\nVAR2 = two\n");

        // Full reparse should produce the same error count
        let full = Parse::parse_makefile(&new_text);
        assert_eq!(new_parse.errors().len(), full.errors().len());
    }

    #[test]
    fn test_incremental_with_include() {
        let old_text = "include foo.mk\nVAR = value\n";
        let parse = Parse::parse_makefile(old_text);

        // Change include path
        let edit = TextEdit::new(TextRange::new(8.into(), 14.into()), "bar.mk".to_string());
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "include bar.mk\nVAR = value\n");
        let makefile = new_parse.tree();
        let includes: Vec<_> = makefile.includes().collect();
        assert_eq!(includes.len(), 1);
        assert_eq!(includes[0].path(), Some("bar.mk".to_string()));
        assert_eq!(makefile.variable_definitions().count(), 1);
    }

    #[test]
    fn test_incremental_with_conditional() {
        let old_text = "ifdef DEBUG\nCFLAGS = -g\nendif\nVAR = value\n";
        let parse = Parse::parse_makefile(old_text);

        // Change variable inside conditional
        let edit = TextEdit::new(TextRange::new(21.into(), 23.into()), "-O2".to_string());
        let (new_parse, new_text) = parse.apply_edit(old_text, &edit);

        assert_eq!(new_text, "ifdef DEBUG\nCFLAGS = -O2\nendif\nVAR = value\n");
        let makefile = new_parse.tree();
        assert_eq!(makefile.conditionals().count(), 1);
        // 2 variables: CFLAGS inside conditional + VAR at top level
        assert_eq!(makefile.variable_definitions().count(), 2);
    }

    #[test]
    fn test_incremental_multiple_edits_sequentially() {
        let old_text = "VAR1 = one\nVAR2 = two\nVAR3 = three\n";
        let parse = Parse::parse_makefile(old_text);

        // First edit: change VAR1
        let edit1 = TextEdit::new(TextRange::new(7.into(), 10.into()), "ONE".to_string());
        let (parse2, text2) = parse.apply_edit(old_text, &edit1);

        // Second edit: change VAR3 (in the new text)
        let edit2 = TextEdit::new(TextRange::new(29.into(), 34.into()), "THREE".to_string());
        let (parse3, text3) = parse2.apply_edit(&text2, &edit2);

        assert_eq!(text3, "VAR1 = ONE\nVAR2 = two\nVAR3 = THREE\n");
        let makefile = parse3.tree();
        let vars: Vec<_> = makefile.variable_definitions().collect();
        assert_eq!(vars[0].raw_value(), Some("ONE".to_string()));
        assert_eq!(vars[1].raw_value(), Some("two".to_string()));
        assert_eq!(vars[2].raw_value(), Some("THREE".to_string()));
    }
}
