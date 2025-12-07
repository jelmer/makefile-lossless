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
}
