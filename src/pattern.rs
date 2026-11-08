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
