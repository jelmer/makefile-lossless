//! Incremental reparsing support for efficient handling of text edits.
//!
//! Instead of reparsing the entire file after each edit, this module reparses
//! only the top-level items between the nearest points around the edit where
//! the parser state is known, splicing the results back into the existing
//! green tree.

use crate::lossless::{ErrorInfo, Makefile, PositionedParseError};
use crate::parse::Parse;
use rowan::{NodeOrToken, TextRange, TextSize};

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
        let new_parse = self.reparse(old_text, &new_text, edit).unwrap_or_else(|| {
            let parsed = crate::lossless::parse(&new_text, self.variant());
            Parse::new(parsed.green_node, parsed.errors, parsed.positioned_errors)
                .with_variant(self.variant())
        });
        (new_parse, new_text)
    }

    /// Reparse the part of `new_text` affected by `edit`, or return `None`
    /// if only a full parse is known to give the right result.
    ///
    /// The reparsed region starts and ends at sync points: top-level
    /// children after which the parser and lexer are in their initial state,
    /// so that parsing the region on its own gives the same result as
    /// parsing it as part of the whole text.
    fn reparse(&self, old_text: &str, new_text: &str, edit: &TextEdit) -> Option<Self> {
        // A .RECIPEPREFIX assignment changes how all later lines are lexed.
        if old_text.contains(".RECIPEPREFIX") || new_text.contains(".RECIPEPREFIX") {
            return None;
        }

        let old_green = self.green();
        let children: Vec<_> = old_green.children().map(|c| c.to_owned()).collect();
        let mut child_ranges: Vec<TextRange> = Vec::with_capacity(children.len());
        let mut offset = TextSize::from(0);
        for child in &children {
            let len = match child {
                NodeOrToken::Node(n) => n.text_len(),
                NodeOrToken::Token(t) => t.text_len(),
            };
            child_ranges.push(TextRange::at(offset, len));
            offset += len;
        }
        let is_sync = |i: usize| is_sync_point(&children[i], &old_text[child_ranges[i]]);

        // Start after the last sync point that the edit leaves untouched.
        let first = (0..children.len())
            .rev()
            .find(|&i| child_ranges[i].end() <= edit.range.start() && is_sync(i))
            .map_or(0, |i| i + 1);
        let start = child_ranges
            .get(first)
            .map_or(TextSize::of(old_text), |r| r.start());

        // End at the first sync point after the edit, if it is parsed the same
        // way as before. Otherwise parse up to the end of the text.
        let sync_end = (first..children.len())
            .find(|&i| child_ranges[i].start() >= edit.range.end() && is_sync(i))
            .and_then(|last| {
                let end = shift(child_ranges[last].end(), edit.delta());
                let reparsed =
                    crate::lossless::parse(&new_text[TextRange::new(start, end)], self.variant());
                let same_end = reparsed.green_node.children().last().map(|c| c.to_owned())
                    == Some(children[last].clone());
                same_end.then_some((last + 1, reparsed))
            });
        let to_eof = sync_end.is_none();
        let (end_index, reparsed) = sync_end.unwrap_or_else(|| {
            (
                children.len(),
                crate::lossless::parse(&new_text[usize::from(start)..], self.variant()),
            )
        });
        let old_end = if to_eof {
            TextSize::of(old_text)
        } else {
            child_ranges[end_index - 1].end()
        };
        let new_end = shift(old_end, edit.delta());

        let new_root = old_green.splice_children(
            first..end_index,
            reparsed.green_node.children().map(|c| c.to_owned()),
        );

        // ErrorInfo uses line numbers, so count the lines before the region
        // and the change in the number of lines in it.
        let line_offset = old_text[..usize::from(start)].matches('\n').count();
        let line_delta = new_text[TextRange::new(start, new_end)]
            .matches('\n')
            .count() as i64
            - old_text[TextRange::new(start, old_end)]
                .matches('\n')
                .count() as i64;

        let old_errors = self.errors().iter().zip(self.positioned_errors());
        let mut errors = Vec::new();
        let mut positioned_errors = Vec::new();
        for (err, positioned) in old_errors.clone() {
            if positioned.range.start() < start {
                errors.push(err.clone());
                positioned_errors.push(positioned.clone());
            }
        }
        for (err, positioned) in reparsed.errors.iter().zip(&reparsed.positioned_errors) {
            errors.push(ErrorInfo {
                line: err.line + line_offset,
                ..err.clone()
            });
            positioned_errors.push(PositionedParseError {
                range: positioned.range + start,
                ..positioned.clone()
            });
        }
        for (err, positioned) in old_errors {
            if !to_eof && positioned.range.start() >= old_end {
                errors.push(ErrorInfo {
                    line: (err.line as i64 + line_delta) as usize,
                    ..err.clone()
                });
                positioned_errors.push(PositionedParseError {
                    range: TextRange::new(
                        shift(positioned.range.start(), edit.delta()),
                        shift(positioned.range.end(), edit.delta()),
                    ),
                    ..positioned.clone()
                });
            }
        }

        // Lines may have shifted, so find the lines in the new tree.
        crate::lossless::locate_error_lines(
            &rowan::SyntaxNode::new_root(new_root.clone()),
            new_text,
            &mut positioned_errors,
        );
        Some(Parse::new(new_root, errors, positioned_errors).with_variant(self.variant()))
    }
}

/// Whether the parser and lexer are back in their initial state after the
/// top-level child `child` with text `text`. That is the case after a
/// variable assignment that ends in a newline that does not continue it.
fn is_sync_point(child: &NodeOrToken<rowan::GreenNode, rowan::GreenToken>, text: &str) -> bool {
    child
        .as_node()
        .is_some_and(|n| n.kind() == crate::SyntaxKind::VARIABLE.into())
        && text
            .strip_suffix('\n')
            .is_some_and(|line| !line.trim_end_matches('\r').ends_with('\\'))
}

fn shift(offset: TextSize, delta: i64) -> TextSize {
    TextSize::from((u32::from(offset) as i64 + delta) as u32)
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
    fn test_incremental_reuses_nodes_after_edit() {
        let old_text = "VAR1 = one\nVAR2 = two\nVAR3 = three\nVAR4 = four\n";
        let parse = Parse::parse_makefile(old_text);
        let edit = TextEdit::new(TextRange::new(18.into(), 21.into()), "TWO".to_string());
        let (new_parse, _) = parse.apply_edit(old_text, &edit);

        let node = |parse: &Parse<Makefile>, i: usize| {
            parse
                .green()
                .children()
                .nth(i)
                .unwrap()
                .into_node()
                .unwrap() as *const _
        };
        assert!(std::ptr::eq(node(&parse, 0), node(&new_parse, 0)));
        assert!(!std::ptr::eq(node(&parse, 1), node(&new_parse, 1)));
        assert!(std::ptr::eq(node(&parse, 3), node(&new_parse, 3)));
    }

    #[test]
    fn test_incremental_keeps_variant() {
        use crate::MakefileVariant;
        for old_text in ["!IF 1\nA = a\n!ENDIF\n", ""] {
            let parse = Parse::parse_makefile_with_variant(old_text, MakefileVariant::NMake);
            let edit = TextEdit::new(TextRange::empty(0.into()), "!IF 2\n!ENDIF\n".to_string());
            let (new_parse, new_text) = parse.apply_edit(old_text, &edit);
            let full = Parse::parse_makefile_with_variant(&new_text, MakefileVariant::NMake);
            assert_eq!(
                format!("{:#?}", new_parse.syntax_node()),
                format!("{:#?}", full.syntax_node())
            );
            assert_eq!(new_parse.errors(), full.errors());
        }
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

    #[test]
    fn test_apply_edit_shifts_error_line_ranges() {
        let old_text = "A = 1\n\n  foo bar\n\nB = 2\n\n  baz \\\n  qux\n";
        let parse = Parse::<Makefile>::parse_makefile(old_text);
        let ranges = |parse: &Parse<Makefile>| {
            parse
                .positioned_errors()
                .iter()
                .map(|e| (e.range, e.line_range(), e.space_indent_range()))
                .collect::<Vec<_>>()
        };
        for edit in [
            TextEdit::new(TextRange::new(4.into(), 5.into()), "123".to_string()),
            TextEdit::new(TextRange::new(4.into(), 5.into()), "".to_string()),
            TextEdit::new(TextRange::new(9.into(), 12.into()), "x".to_string()),
        ] {
            let (new_parse, new_text) = parse.apply_edit(old_text, &edit);
            let full = Parse::<Makefile>::parse_makefile(&new_text);
            assert_eq!(ranges(&new_parse), ranges(&full));
            assert_eq!(ranges(&full).len(), 2);
        }
    }

    #[test]
    fn test_apply_edit_keeps_error_kinds() {
        use crate::ParseErrorKind;
        let old_text = "A = 1\n\nfoo bar\n\nendif\n";
        let parse = Parse::<Makefile>::parse_makefile(old_text);
        // Edit the middle error, leaving the last one after the edit.
        let edit = TextEdit::new(TextRange::new(7.into(), 10.into()), "baz".to_string());
        let (new_parse, _) = parse.apply_edit(old_text, &edit);
        assert_eq!(
            new_parse
                .errors()
                .iter()
                .map(|e| (e.line, e.kind()))
                .collect::<Vec<_>>(),
            vec![
                (3, ParseErrorKind::MissingSeparator),
                (5, ParseErrorKind::ExtraneousEndif)
            ]
        );
        assert_eq!(
            new_parse
                .positioned_errors()
                .iter()
                .map(|e| e.kind())
                .collect::<Vec<_>>(),
            vec![
                ParseErrorKind::MissingSeparator,
                ParseErrorKind::ExtraneousEndif
            ]
        );
    }

    const SAMPLES: &[&str] = &[
        "all:\n\techo\nA = a\n",
        "A = a\nB = b\n",
        "VAR1 = one\n# comment\nall: dep\n\techo $(VAR1) \\\n\t  more\n\nVAR2 = two\nclean:\n\trm -f x\n",
        "ifdef DEBUG\nCFLAGS = -g\nelse\nCFLAGS = -O2\nendif\nA = a\nall:\n\t@echo $(A)\n",
        "define FOO\necho a\nendef\nB := $(FOO)\ninclude x.mk\nC = c \\\n  d\n",
        "all: a b\n\n\techo\n# c\n\techo2\nx = 1\n-include y.mk\n$(info hi)\n",
        ".RECIPEPREFIX = >\nall:\n>echo a\nB = b\nc:\n>echo c\n",
        "A = 1\n\n  foo bar\n\nB = 2\n\n  baz \\\n  qux\nendif\nC = 3",
        "# c \\\nA = a\nall:\n B = b\n\techo\nexport C = c\r\nD = d\r\n",
        ".if 1\nA = a\n.for x in a b\nB = b\n.endfor\n.endif\nC = c\n!IF 1\nD = d\n!ENDIF\n",
        "override E = e\nundefine E\nall: F = f\nG = $(shell \\\n  ls)\nH = h\n",
    ];

    const INSERTIONS: &[&str] = &[
        "\n", "\t", " ", "\\", ":", "=", "#", "x", "$", "(", ")", ";", "\r",
    ];

    fn assert_matches_full_parse(old_text: &str, edit: &TextEdit) {
        let parse = Parse::<Makefile>::parse_makefile(old_text);
        let (incremental, new_text) = parse.apply_edit(old_text, edit);
        let full = Parse::<Makefile>::parse_makefile(&new_text);
        assert_eq!(
            format!("{:#?}", incremental.syntax_node()),
            format!("{:#?}", full.syntax_node()),
            "tree differs for {:?} with {:?}",
            old_text,
            edit
        );
        assert_eq!(
            incremental.errors(),
            full.errors(),
            "errors differ for {:?} with {:?}",
            old_text,
            edit
        );
        assert_eq!(
            incremental.positioned_errors(),
            full.positioned_errors(),
            "positioned errors differ for {:?} with {:?}",
            old_text,
            edit
        );
    }

    fn insert(offset: u32, text: &str) -> TextEdit {
        TextEdit::new(TextRange::empty(offset.into()), text.to_string())
    }

    #[test]
    fn test_recipe_line_after_rule() {
        assert_matches_full_parse("all:\n\techo\nA = a\n", &insert(11, "\techo2\n"));
    }

    #[test]
    fn test_continuation_joins_next_line() {
        assert_matches_full_parse("A = a\nB = b\n", &insert(5, " \\"));
    }

    #[test]
    fn test_conditional_inserted_at_start() {
        assert_matches_full_parse("A = a\nB = b\n", &insert(0, "ifdef X\n"));
    }

    #[test]
    fn test_endif_inserted() {
        assert_matches_full_parse("ifdef X\nA = a\nB = b\nendif\n", &insert(6, "\nendif\n"));
    }

    #[test]
    fn test_define_opened() {
        assert_matches_full_parse("A = a\nB = b\nC = c\n", &insert(6, "define B\n"));
    }

    #[test]
    fn test_recipe_prefix_changed() {
        assert_matches_full_parse(
            ".RECIPEPREFIX = >\nall:\n>echo a\nB = b\nc:\n>echo c\n",
            &TextEdit::new(TextRange::new(16.into(), 17.into()), "|".to_string()),
        );
    }

    #[test]
    fn test_append_at_end_without_newline() {
        assert_matches_full_parse("A = a\nB = b", &insert(11, " \\\nC = c\n"));
    }

    #[test]
    fn test_all_single_char_edits() {
        for sample in SAMPLES {
            for offset in 0..=sample.len() as u32 {
                for text in INSERTIONS {
                    assert_matches_full_parse(sample, &insert(offset, text));
                }
                if (offset as usize) < sample.len() {
                    let delete =
                        TextEdit::new(TextRange::at(offset.into(), 1.into()), String::new());
                    assert_matches_full_parse(sample, &delete);
                }
            }
        }
    }

    #[test]
    fn test_multi_line_edits() {
        let insertions = [
            "ifdef X\n",
            "endif\n",
            "else\n",
            "\techo\n",
            "all:\n",
            "define V\n",
            "endef\n",
            ".RECIPEPREFIX = >\n",
            "A = \\\n",
            "x: ; y\n",
        ];
        for sample in SAMPLES {
            for offset in 0..=sample.len() as u32 {
                for text in insertions {
                    assert_matches_full_parse(sample, &insert(offset, text));
                }
                for len in 2..12u32 {
                    if (offset + len) as usize <= sample.len() {
                        let delete =
                            TextEdit::new(TextRange::at(offset.into(), len.into()), String::new());
                        assert_matches_full_parse(sample, &delete);
                    }
                }
            }
        }
    }
}
