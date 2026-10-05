//! Text-based utilities for navigating Makefile source text.
//!
//! These functions work on raw source text (not the syntax tree) and are useful
//! for editor integrations that need to understand what is at a given cursor position.

/// Extract a variable name from `$(VAR)` or `${VAR}` surrounding the given byte offset.
///
/// Returns `None` if the offset is not inside a variable reference.
///
/// # Example
/// ```
/// use makefile_lossless::variable_at_offset;
/// assert_eq!(variable_at_offset("$(FOO)", 2), Some("FOO"));
/// assert_eq!(variable_at_offset("${BAR}", 3), Some("BAR"));
/// assert_eq!(variable_at_offset("plain text", 3), None);
/// ```
pub fn variable_at_offset(text: &str, offset: usize) -> Option<&str> {
    let bytes = text.as_bytes();
    let mut start = None;
    let mut i = offset;
    while i >= 2 {
        i -= 1;
        if i > 0 && (bytes[i] == b'(' || bytes[i] == b'{') && bytes[i - 1] == b'$' {
            start = Some(i + 1);
            break;
        }
        if bytes[i] == b')' || bytes[i] == b'}' || bytes[i] == b'\n' {
            return None;
        }
    }
    let start = start?;
    let rest = &text[start..];
    let end = rest.find([')', '}'])?;
    let var_name = &rest[..end];
    if offset >= start && offset <= start + end {
        Some(var_name)
    } else {
        None
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
