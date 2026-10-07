//! Text-based utilities for navigating Makefile source text.
//!
//! These functions work on raw source text (not the syntax tree) and are useful
//! for editor integrations that need to understand what is at a given cursor position.

use crate::reference::{split_references, ReferenceError, ReferenceSyntaxErrorKind, TextPart};
use crate::MakefileVariant;

/// Extract the name of the innermost `$(VAR)` or `${VAR}` reference
/// surrounding the given byte offset, from just after its opening brace up
/// to and including its closing brace.
///
/// References are found as GNU make finds them, on the line containing the
/// offset. Returns `None` if the offset is not inside a reference, if the
/// innermost reference is a function call such as `$(wildcard *.c)`, is not
/// closed or has a computed name such as `$(A_$(B))`, or if the offset is
/// past the end of `text` or not on a character boundary.
///
/// # Example
/// ```
/// use makefile_lossless::variable_at_offset;
/// assert_eq!(variable_at_offset("$(FOO)", 2), Some("FOO"));
/// assert_eq!(variable_at_offset("${BAR}", 3), Some("BAR"));
/// assert_eq!(variable_at_offset("plain text", 3), None);
/// assert_eq!(variable_at_offset("$(subst a,b,$(X))", 3), None);
/// assert_eq!(variable_at_offset("$(subst a,b,$(X))", 14), Some("X"));
/// ```
pub fn variable_at_offset(text: &str, offset: usize) -> Option<&str> {
    if !text.is_char_boundary(offset) {
        return None;
    }
    let line_start = text[..offset].rfind('\n').map_or(0, |i| i + 1);
    let line_end = text[offset..].find('\n').map_or(text.len(), |i| offset + i);
    let mut region = line_start..line_end;
    let mut name = None;
    loop {
        let Some((range, parsed)) =
            split_references(&text[region.clone()], MakefileVariant::GNUMake)
                .into_iter()
                .find_map(|part| match part {
                    TextPart::Reference { range, parsed } => {
                        let range = region.start + range.start..region.start + range.end;
                        let body_start = range.start + 2;
                        (body_start <= offset && offset < range.end).then_some((range, parsed))
                    }
                    _ => None,
                })
        else {
            return name;
        };
        let body_start = range.start + 2;
        let unclosed = parsed.as_ref().err().and_then(ReferenceError::syntax_kind)
            == Some(ReferenceSyntaxErrorKind::UnclosedExpression);
        name = match parsed {
            Ok(reference) if !reference.name.contains('$') => {
                Some(&text[body_start..body_start + reference.name.len()])
            }
            _ => None,
        };
        region = if unclosed {
            body_start..range.end
        } else {
            body_start..range.end - 1
        };
    }
}

/// Extract the word (identifier) at the given byte offset.
///
/// A word consists of ASCII alphanumeric characters, underscores, dots, and hyphens.
/// Returns `None` if the offset is not on a word character.
///
/// # Example
/// ```
/// use makefile_lossless::word_at_offset;
/// assert_eq!(word_at_offset("hello world", 0), Some("hello"));
/// assert_eq!(word_at_offset("hello world", 5), None); // space
/// assert_eq!(word_at_offset("hello world", 6), Some("world"));
/// ```
pub fn word_at_offset(text: &str, offset: usize) -> Option<&str> {
    if offset > text.len() {
        return None;
    }
    let bytes = text.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_' || b == b'.' || b == b'-';
    if offset < text.len() && !is_ident(bytes[offset]) {
        return None;
    }
    let start = (0..offset)
        .rev()
        .take_while(|&i| is_ident(bytes[i]))
        .last()
        .unwrap_or(offset);
    let end = (offset..text.len())
        .take_while(|&i| is_ident(bytes[i]))
        .last()
        .map(|i| i + 1)
        .unwrap_or(offset);
    if start == end {
        return None;
    }
    Some(&text[start..end])
}

/// Determine if the given byte offset is in the prerequisites area of a rule line
/// (i.e. after the first `:` on a non-recipe line).
///
/// # Example
/// ```
/// use makefile_lossless::is_in_prerequisites;
/// let text = "all: build test\n\techo ok\n";
/// assert!(!is_in_prerequisites(text, 0));  // 'a' in target
/// assert!(is_in_prerequisites(text, 5));   // 'b' in prerequisites
/// assert!(!is_in_prerequisites(text, 17)); // 'e' in recipe
/// ```
pub fn is_in_prerequisites(text: &str, offset: usize) -> bool {
    let line_start = text[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line = &text[line_start..];
    // Recipe lines start with a tab
    if line.starts_with('\t') {
        return false;
    }
    let col = offset - line_start;
    // Check if there's a `:` before our position on this line
    line[..col].contains(':')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_variable_at_offset_parens() {
        assert_eq!(variable_at_offset("$(FOO)", 2), Some("FOO"));
        assert_eq!(variable_at_offset("$(FOO)", 4), Some("FOO"));
    }

    #[test]
    fn test_variable_at_offset_braces() {
        assert_eq!(variable_at_offset("${BAR}", 2), Some("BAR"));
    }

    #[test]
    fn test_variable_at_offset_none() {
        assert_eq!(variable_at_offset("plain text", 3), None);
    }

    #[test]
    fn test_variable_at_offset_nested_context() {
        let text = "\t$(CC) main.c";
        assert_eq!(variable_at_offset(text, 3), Some("CC"));
    }

    #[test]
    fn test_variable_at_offset_function_call() {
        let text = "$(subst a,b,$(X))";
        assert_eq!(variable_at_offset(text, 3), None);
        assert_eq!(variable_at_offset(text, 12), None);
        assert_eq!(variable_at_offset(text, 14), Some("X"));
        assert_eq!(variable_at_offset(text, 15), Some("X"));
        assert_eq!(variable_at_offset(text, 16), None);
    }

    #[test]
    fn test_variable_at_offset_nested() {
        let text = "$(A:.c=$(B))";
        assert_eq!(variable_at_offset(text, 2), Some("A"));
        assert_eq!(variable_at_offset(text, 5), Some("A"));
        assert_eq!(variable_at_offset(text, 9), Some("B"));
        assert_eq!(variable_at_offset(text, 11), Some("A"));
        // A computed variable name has no name to return.
        assert_eq!(variable_at_offset("$(A_$(B))", 3), None);
        assert_eq!(variable_at_offset("$(A_$(B))", 6), Some("B"));
    }

    #[test]
    fn test_variable_at_offset_mismatched_closer() {
        // As in make, only the kind of brace that opens a reference closes it.
        assert_eq!(variable_at_offset("$(A} x)", 2), Some("A} x"));
        assert_eq!(variable_at_offset("${A) x}", 2), Some("A) x"));
    }

    #[test]
    fn test_variable_at_offset_outside() {
        let text = "x $(FOO) y";
        assert_eq!(variable_at_offset(text, 0), None);
        assert_eq!(variable_at_offset(text, 2), None);
        assert_eq!(variable_at_offset(text, 3), None);
        assert_eq!(variable_at_offset(text, 4), Some("FOO"));
        assert_eq!(variable_at_offset(text, 7), Some("FOO"));
        assert_eq!(variable_at_offset(text, 8), None);
        assert_eq!(variable_at_offset("$X $@", 1), None);
    }

    #[test]
    fn test_variable_at_offset_unclosed() {
        assert_eq!(variable_at_offset("$(FOO", 3), None);
        assert_eq!(variable_at_offset("$(FOO\nBAR)", 3), None);
        assert_eq!(variable_at_offset("$(FOO $(BAR)", 9), Some("BAR"));
    }

    #[test]
    fn test_variable_at_offset_multiline() {
        let text = "A = $(B)\nC = $(D)\n";
        assert_eq!(variable_at_offset(text, 6), Some("B"));
        assert_eq!(variable_at_offset(text, 15), Some("D"));
    }

    #[test]
    fn test_word_at_offset_basic() {
        assert_eq!(word_at_offset("hello world", 0), Some("hello"));
        assert_eq!(word_at_offset("hello world", 3), Some("hello"));
        assert_eq!(word_at_offset("hello world", 5), None);
        assert_eq!(word_at_offset("hello world", 6), Some("world"));
    }

    #[test]
    fn test_word_at_offset_special_chars() {
        assert_eq!(word_at_offset("foo-bar.o", 0), Some("foo-bar.o"));
        assert_eq!(word_at_offset("FOO_BAR", 3), Some("FOO_BAR"));
    }

    #[test]
    fn test_is_in_prerequisites() {
        let text = "all: build test\n\techo ok\n";
        assert!(!is_in_prerequisites(text, 0)); // 'a' in target
        assert!(is_in_prerequisites(text, 5)); // 'b' in prerequisites
        assert!(!is_in_prerequisites(text, 17)); // 'e' in recipe
    }

    #[test]
    fn test_is_in_prerequisites_no_colon() {
        let text = "VAR = value\n";
        assert!(!is_in_prerequisites(text, 6));
    }
}
