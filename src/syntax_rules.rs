//! Rules of make syntax shared by the lexer, the parser and the AST.

/// GNU make's assignment operators. BSD make also has `:sh=`, see
/// [`is_sunsh_operator`], but not `::=` and `:::=`, see
/// [`is_colons_before_subst`].
pub(crate) const ASSIGNMENT_OPERATORS: &[&str] = &["=", ":=", "::=", ":::=", "+=", "?=", "!="];

/// Whether `op` is `::=` or `:::=`, which BSD make does not have: it reads
/// the leading colons as part of the variable name, followed by `:=`.
pub(crate) fn is_colons_before_subst(op: &str) -> bool {
    matches!(op, "::=" | ":::=")
}

/// Whether `text` is BSD make's `:sh=` shell assignment operator, which may
/// contain whitespace and repeat the modifier, as in `:sh :sh =`.
pub(crate) fn is_sunsh_operator(text: &str) -> bool {
    let compact: String = text.split_whitespace().collect();
    compact
        .strip_suffix('=')
        .is_some_and(|modifiers| !modifiers.is_empty() && modifiers.split(":sh").all(str::is_empty))
}

/// Whether `word` is one of the modifiers that GNU make accepts before an
/// assignment or `define`, in any order and repeated. Of these, BSD make
/// only has `export`, for a GNU make style `export VAR = value`.
pub(crate) fn is_assignment_modifier(word: &str) -> bool {
    matches!(word, "override" | "export" | "unexport" | "private")
}

/// The GNU make keywords that start a conditional.
pub(crate) const GNU_CONDITIONAL_STARTS: &[&str] = &["ifdef", "ifndef", "ifeq", "ifneq"];

/// The GNU make conditional keywords: those starting a conditional, `else`
/// and `endif`.
pub(crate) const GNU_CONDITIONAL_KEYWORDS: &[&str] =
    &["ifdef", "ifndef", "ifeq", "ifneq", "else", "endif"];

/// Whether `word` starts a GNU make conditional. This requires an exact
/// match: a variable named e.g. `ifpkg` is not a conditional.
pub(crate) fn is_gnu_conditional_start(word: &str) -> bool {
    GNU_CONDITIONAL_STARTS.contains(&word)
}

/// Whether the BSD make directive `name`, without its leading dot, starts
/// a conditional.
pub(crate) fn is_bsd_if(name: &str) -> bool {
    matches!(name, "if" | "ifdef" | "ifndef" | "ifmake" | "ifnmake")
}

/// Whether the BSD make directive `name`, without its leading dot, starts
/// another branch of a conditional with a condition.
pub(crate) fn is_bsd_elif(name: &str) -> bool {
    matches!(
        name,
        "elif" | "elifdef" | "elifndef" | "elifmake" | "elifnmake"
    )
}

/// Whether the BSD make directive `name`, without its leading dot, is part
/// of a conditional.
pub(crate) fn is_bsd_conditional(name: &str) -> bool {
    is_bsd_if(name) || is_bsd_elif(name) || matches!(name, "else" | "endif")
}

/// The keywords of GNU make's `include` directive.
pub(crate) const GNU_INCLUDE_KEYWORDS: &[&str] = &["include", "-include", "sinclude"];

/// The keywords of POSIX make's `include` directive.
pub(crate) const POSIX_INCLUDE_KEYWORDS: &[&str] = &["include", "-include"];

/// Whether the last of a run of `count` backslashes is not itself escaped,
/// so that it escapes the character after it, or continues the line before
/// a newline. Each backslash escapes the next one, so this holds for an odd
/// count.
pub(crate) fn last_backslash_unescaped(count: usize) -> bool {
    count % 2 == 1
}

/// Whether the character or token after one that `is_backslash` is escaped,
/// given whether that one was `escaped` itself. This follows a run of
/// backslashes one at a time, as [`last_backslash_unescaped`] does at once.
pub(crate) fn escapes_next(is_backslash: bool, escaped: bool) -> bool {
    is_backslash && !escaped
}

/// Whether `text` ends in a backslash that is not escaped by the one before
/// it.
pub(crate) fn ends_with_unescaped_backslash(text: &str) -> bool {
    last_backslash_unescaped(text.chars().rev().take_while(|&c| c == '\\').count())
}
