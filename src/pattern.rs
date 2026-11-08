/// Split `pattern` at its first unquoted `%`, as GNU make reads a pattern
/// rule target, into the text before and after it.
///
/// A `%` after an odd number of backslashes is a literal `%`, and half of
/// the backslashes before each `%` up to the pattern one are removed. The
/// text after the pattern `%` is kept as is. A `%` inside a variable
/// reference does not count, since make only sees it after expansion.
pub(crate) fn split_pattern(pattern: &str) -> Option<(String, &str)> {
    let (prefix, rest) = scan_percent(pattern);
    Some((prefix, rest?))
}

/// `name` with each `\%` read as `%`, as GNU make reads an explicit target:
/// as [`split_pattern`] does up to the first unquoted `%`, which is kept
/// along with the text after it.
pub(crate) fn unescape_percent(name: &str) -> String {
    match scan_percent(name) {
        (prefix, Some(rest)) => format!("{prefix}%{rest}"),
        (prefix, None) => prefix,
    }
}

/// The text before the first unquoted `%` in `pattern`, unescaped as
/// described for [`split_pattern`], and the text after that `%` if there is
/// one.
fn scan_percent(pattern: &str) -> (String, Option<&str>) {
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
                    return (prefix, Some(&pattern[i + 1..]));
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
    (prefix, None)
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

/// How `target` matches a pattern rule target, as [`pattern_match`] finds.
pub(crate) struct PatternMatch<'a> {
    /// The directory of `target` that was left out of the comparison, with
    /// its trailing `/`, or empty.
    pub(crate) dir: &'a str,
    /// The part of `target` that `%` matched, without `dir`.
    pub(crate) stem: &'a str,
}

impl PatternMatch<'_> {
    /// The stem as make sets `$*`: [`Self::stem`] with [`Self::dir`] in
    /// front.
    pub(crate) fn full_stem(&self) -> String {
        format!("{}{}", self.dir, self.stem)
    }
}

/// How GNU make matches the pattern rule target `pattern` against `target`,
/// or `None` if it does not match.
///
/// If `pattern` has no `/`, the directory part of `target` is left out of
/// the comparison, so `lib%.a` matches `dir/libfoo.a` with directory `dir/`
/// and stem `foo`. A `/` at the very end of `target` does not end the
/// directory. The stem may only be empty if there is a directory. Patterns
/// that contain variable references never match.
pub(crate) fn pattern_match<'a>(pattern: &str, target: &'a str) -> Option<PatternMatch<'a>> {
    let (prefix, suffix) = literal_pattern(pattern)?;
    let (dir, name) = match target.strip_suffix('/').unwrap_or(target).rfind('/') {
        Some(i) if !prefix.contains('/') && !suffix.contains('/') => target.split_at(i + 1),
        _ => ("", target),
    };
    let stem = name
        .strip_prefix(prefix.as_str())?
        .strip_suffix(suffix.as_str())?;
    if dir.is_empty() && stem.is_empty() {
        return None;
    }
    Some(PatternMatch { dir, stem })
}

/// How GNU make matches a target of a static pattern rule against its
/// target pattern: unlike [`pattern_match`], the directory is part of the
/// comparison, and the stem may be empty.
pub(crate) fn static_pattern_match<'a>(pattern: &str, target: &'a str) -> Option<PatternMatch<'a>> {
    let (prefix, suffix) = literal_pattern(pattern)?;
    let stem = target
        .strip_prefix(prefix.as_str())?
        .strip_suffix(suffix.as_str())?;
    Some(PatternMatch { dir: "", stem })
}

/// The text before and after the pattern `%` of `pattern`, or `None` if it
/// has none or contains a variable reference.
fn literal_pattern(pattern: &str) -> Option<(String, String)> {
    let (prefix, suffix) = split_pattern(pattern)?;
    Some((literal_text(&prefix)?, literal_text(suffix)?))
}

/// The stem with which GNU make matches the pattern rule target `pattern`
/// against `target`, with the directory of [`pattern_match`] in front, or
/// `None` if it does not match.
pub(crate) fn pattern_stem(pattern: &str, target: &str) -> Option<String> {
    pattern_match(pattern, target).map(|m| m.full_stem())
}

/// `prerequisite` of a pattern rule with its first `%` replaced by the
/// stem of `m`, and the directory of `m` in front, as GNU make does. A
/// prerequisite without `%` is used as is. Returns `None` if it contains a
/// variable reference, whose value is not known.
pub(crate) fn substitute_stem(prerequisite: &str, m: &PatternMatch) -> Option<String> {
    match split_pattern(prerequisite) {
        Some((prefix, rest)) => Some(format!(
            "{}{}{}{}",
            m.dir,
            literal_text(&prefix)?,
            m.stem,
            literal_text(rest)?
        )),
        None => literal_text(prerequisite),
    }
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
    fn test_unescape_percent() {
        assert_eq!(unescape_percent("foo.o"), "foo.o");
        assert_eq!(unescape_percent("a\\%b"), "a%b");
        assert_eq!(unescape_percent("c\\%d\\%e"), "c%d%e");
        assert_eq!(unescape_percent("a\\\\\\%b"), "a\\%b");
        assert_eq!(unescape_percent("x\\y\\%z"), "x\\y%z");
        // Only up to the first unquoted `%`.
        assert_eq!(unescape_percent("x\\\\%y\\%z"), "x\\%y\\%z");
        assert_eq!(unescape_percent("$(f \\%)\\%"), "$(f \\%)%");
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
    fn test_pattern_stem_trailing_slash() {
        // make does not count a `/` at the end as the end of the directory.
        assert_eq!(pattern_stem("x%", "a/xb/"), Some("a/b/".to_string()));
        assert_eq!(pattern_stem("x%", "xb/"), Some("b/".to_string()));
    }

    #[test]
    fn test_static_pattern_match() {
        let stem = |p, t| static_pattern_match(p, t).map(|m| m.full_stem());
        assert_eq!(stem("%.o", "d/a.o"), Some("d/a".to_string()));
        assert_eq!(stem("x%.o", "d/xa.o"), None);
        assert_eq!(stem("%.o", ".o"), Some(String::new()));
        assert_eq!(stem("a%a", "a"), None);
    }

    #[test]
    fn test_substitute_stem() {
        let m = pattern_match("%.o", "d/foo.o").unwrap();
        assert_eq!(substitute_stem("%.c", &m), Some("d/foo.c".to_string()));
        assert_eq!(
            substitute_stem("common.h", &m),
            Some("common.h".to_string())
        );
        assert_eq!(substitute_stem("%.x%", &m), Some("d/foo.x%".to_string()));
        assert_eq!(substitute_stem("$(DIR)/%.c", &m), None);
        assert_eq!(substitute_stem("$$%.c", &m), Some("d/$foo.c".to_string()));
    }

    #[test]
    fn test_pattern_stem_references() {
        assert_eq!(pattern_stem("$(DIR)/%.o", "build/foo.o"), None);
        assert_eq!(pattern_stem("$$%.o", "$foo.o"), Some("foo".to_string()));
    }
}
