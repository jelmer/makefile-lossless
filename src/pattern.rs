/// Match a target against a pattern using make-style wildcard matching.
///
/// Supports `%` as a wildcard that matches any sequence of characters.
/// For example, `%.o` matches `foo.o`, `bar.o`, etc.
///
/// # Arguments
/// * `pattern` - The pattern to match against (e.g., "%.o")
/// * `target` - The target name to check (e.g., "foo.o")
///
/// # Returns
/// `true` if the target matches the pattern, `false` otherwise
pub(crate) fn matches_pattern(pattern: &str, target: &str) -> bool {
    // No wildcard means exact match
    if !pattern.contains('%') {
        return pattern == target;
    }

    // GNU make supports exactly one '%' which matches any NON-EMPTY substring
    let parts: Vec<&str> = pattern.split('%').collect();

    // Only handle single % (GNU make doesn't support multiple %)
    if parts.len() != 2 {
        // Multiple % or malformed pattern - just do exact match as fallback
        return pattern == target;
    }

    let prefix = parts[0];
    let suffix = parts[1];

    // Target must be longer than prefix + suffix to have a non-empty stem
    if target.len() <= prefix.len() + suffix.len() {
        return false;
    }

    // Check that target starts with prefix and ends with suffix
    target.starts_with(prefix) && target.ends_with(suffix)
}

/// Split `pattern` at its first unquoted `%`, as GNU make reads a pattern
/// rule target, into the text before and after it.
///
/// A `%` after an odd number of backslashes is a literal `%`, and half of
/// the backslashes before each `%` up to the pattern one are removed. The
/// text after the pattern `%` is kept as is. A `%` inside a variable
/// reference does not count, since make only sees it after expansion.
pub(crate) fn split_pattern(pattern: &str) -> Option<(String, &str)> {
    let mut prefix = String::new();
    let mut backslashes = 0;
    let mut chars = pattern.char_indices();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' => {
                backslashes += 1;
                prefix.push(c);
                continue;
            }
            '%' => {
                prefix.truncate(prefix.len() - (backslashes - backslashes / 2));
                if backslashes % 2 == 0 {
                    return Some((prefix, &pattern[i + 1..]));
                }
                prefix.push(c);
            }
            '$' => {
                prefix.push(c);
                let Some((_, open)) = chars.next() else {
                    break;
                };
                prefix.push(open);
                let close = match open {
                    '(' => ')',
                    '{' => '}',
                    _ => {
                        backslashes = 0;
                        continue;
                    }
                };
                let mut depth = 1;
                for (_, c) in chars.by_ref() {
                    prefix.push(c);
                    if c == open {
                        depth += 1;
                    } else if c == close {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                }
            }
            _ => prefix.push(c),
        }
        backslashes = 0;
    }
    None
}

/// `text` with `$$` read as `$`, or `None` if it contains a variable
/// reference, whose value is not known.
fn literal_text(text: &str) -> Option<String> {
    let mut result = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c == '$' && chars.next()? != '$' {
            return None;
        }
        result.push(c);
    }
    Some(result)
}

/// The stem with which GNU make matches the pattern rule target `pattern`
/// against `target`, or `None` if it does not match.
///
/// If `pattern` has no `/`, the directory part of `target` is left out of
/// the comparison and put in front of the stem, so `lib%.a` matches
/// `dir/libfoo.a` with stem `dir/foo`. The stem may not be empty. Patterns
/// that contain variable references never match.
pub(crate) fn pattern_stem(pattern: &str, target: &str) -> Option<String> {
    let (prefix, suffix) = split_pattern(pattern)?;
    let prefix = literal_text(&prefix)?;
    let suffix = literal_text(suffix)?;
    let (dir, name) = match target.rfind('/') {
        Some(i) if !prefix.contains('/') && !suffix.contains('/') => target.split_at(i + 1),
        _ => ("", target),
    };
    let stem = name
        .strip_prefix(prefix.as_str())?
        .strip_suffix(suffix.as_str())?;
    if dir.is_empty() && stem.is_empty() {
        return None;
    }
    Some(format!("{dir}{stem}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matches_pattern_exact() {
        assert!(matches_pattern("foo.o", "foo.o"));
        assert!(!matches_pattern("foo.o", "bar.o"));
    }

    #[test]
    fn test_matches_pattern_wildcard_only() {
        assert!(matches_pattern("%", "a"));
        assert!(matches_pattern("%", "anything"));
        assert!(!matches_pattern("%", "")); // % requires non-empty stem
    }

    #[test]
    fn test_matches_pattern_suffix() {
        assert!(matches_pattern("%.o", "foo.o"));
        assert!(matches_pattern("%.o", "bar.o"));
        assert!(!matches_pattern("%.o", "foo.c"));
        assert!(!matches_pattern("%.o", ".o")); // % requires non-empty stem
    }

    #[test]
    fn test_matches_pattern_prefix() {
        assert!(matches_pattern("test_%", "test_foo"));
        assert!(matches_pattern("test_%", "test_bar"));
        assert!(!matches_pattern("test_%", "other_foo"));
        assert!(!matches_pattern("test_%", "test_")); // % requires non-empty stem
    }

    #[test]
    fn test_matches_pattern_middle() {
        assert!(matches_pattern("foo%bar", "fooBARbar"));
        assert!(matches_pattern("foo%bar", "foo123bar"));
        assert!(!matches_pattern("foo%bar", "foobar")); // % requires non-empty stem
    }

    #[test]
    fn test_matches_pattern_empty_stem() {
        // % must match at least one character (non-empty stem)
        assert!(!matches_pattern("%.o", ".o"));
        assert!(!matches_pattern("foo%", "foo"));
        assert!(!matches_pattern("%bar", "bar"));
    }

    #[test]
    fn test_matches_pattern_multiple_wildcards_not_supported() {
        // Multiple % not supported - fallback to exact match
        assert!(matches_pattern("%.%.o", "%.%.o"));
        assert!(!matches_pattern("%.%.o", "foo.bar.o"));
    }

    #[test]
    fn test_split_pattern() {
        assert_eq!(split_pattern("%.o"), Some((String::new(), ".o")));
        assert_eq!(split_pattern("lib%.a"), Some(("lib".to_string(), ".a")));
        assert_eq!(split_pattern("foo.o"), None);
        // Only the first `%` is the pattern character.
        assert_eq!(split_pattern("%.x%"), Some((String::new(), ".x%")));
    }

    #[test]
    fn test_split_pattern_backslashes() {
        assert_eq!(split_pattern("a\\%b"), None);
        assert_eq!(split_pattern("q\\%r%.y"), Some(("q%r".to_string(), ".y")));
        assert_eq!(split_pattern("a\\\\%b"), Some(("a\\".to_string(), "b")));
        assert_eq!(split_pattern("c\\\\\\%d"), None);
        assert_eq!(split_pattern("e\\f%g"), Some(("e\\f".to_string(), "g")));
        // Backslashes after the pattern `%` are kept.
        assert_eq!(split_pattern("%.x\\%"), Some((String::new(), ".x\\%")));
    }

    #[test]
    fn test_split_pattern_references() {
        assert_eq!(split_pattern("$(patsubst %.c,%.o,x.c)"), None);
        assert_eq!(split_pattern("${A%B}"), None);
        assert_eq!(split_pattern("$(f (%))"), None);
        assert_eq!(
            split_pattern("$(DIR)/%.o"),
            Some(("$(DIR)/".to_string(), ".o"))
        );
        // `$%` is the archive member automatic variable.
        assert_eq!(split_pattern("$%"), None);
        assert_eq!(split_pattern("$$%.o"), Some(("$$".to_string(), ".o")));
    }

    #[test]
    fn test_pattern_stem() {
        assert_eq!(pattern_stem("%.o", "foo.o"), Some("foo".to_string()));
        assert_eq!(pattern_stem("%.o", "foo.c"), None);
        assert_eq!(pattern_stem("%.o", ".o"), None);
        assert_eq!(pattern_stem("%.x%", "a.x%"), Some("a".to_string()));
        assert_eq!(pattern_stem("%.x%", "a.xq"), None);
        assert_eq!(
            pattern_stem("q\\%r%.y", "q%rfoo.y"),
            Some("foo".to_string())
        );
        assert_eq!(pattern_stem("foo.o", "foo.o"), None);
    }

    #[test]
    fn test_pattern_stem_directories() {
        assert_eq!(
            pattern_stem("%.o", "src/foo.o"),
            Some("src/foo".to_string())
        );
        assert_eq!(
            pattern_stem("lib%.a", "d1/d2/libbar.a"),
            Some("d1/d2/bar".to_string())
        );
        assert_eq!(
            pattern_stem("lib%.a", "dir/lib.a"),
            Some("dir/".to_string())
        );
        assert_eq!(pattern_stem("pre%", "pre/x"), None);
        assert_eq!(pattern_stem("pre%", "dir/prex"), Some("dir/x".to_string()));
        // A pattern with a `/` is matched against the whole name.
        assert_eq!(
            pattern_stem("src/%.c", "src/a/foo.c"),
            Some("a/foo".to_string())
        );
        assert_eq!(pattern_stem("src/%.c", "x/src/foo.c"), None);
        assert_eq!(pattern_stem("%/x.z", "a/b/x.z"), Some("a/b".to_string()));
    }

    #[test]
    fn test_pattern_stem_references() {
        assert_eq!(pattern_stem("$(DIR)/%.o", "build/foo.o"), None);
        assert_eq!(pattern_stem("$$%.o", "$foo.o"), Some("foo".to_string()));
    }
}
