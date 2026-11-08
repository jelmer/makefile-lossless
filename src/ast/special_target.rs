//! Special targets and suffix rules.

use crate::lossless::{Makefile, Rule};
use crate::MakefileVariant;

/// GNU make's special targets.
const GNU_SPECIAL_TARGETS: &[&str] = &[
    ".DEFAULT",
    ".DELETE_ON_ERROR",
    ".EXPORT_ALL_VARIABLES",
    ".IGNORE",
    ".INTERMEDIATE",
    ".LOW_RESOLUTION_TIME",
    ".NOTINTERMEDIATE",
    ".NOTPARALLEL",
    ".ONESHELL",
    ".PHONY",
    ".POSIX",
    ".PRECIOUS",
    ".SECONDARY",
    ".SECONDEXPANSION",
    ".SILENT",
    ".SUFFIXES",
];

/// Targets that BSD make treats specially in a dependency line; a line
/// starting with one never provides the default goal.
const BSD_SPECIAL_TARGETS: &[&str] = &[
    ".BEGIN",
    ".DEFAULT",
    ".DELETE_ON_ERROR",
    ".END",
    ".ERROR",
    ".EXEC",
    ".IGNORE",
    ".INCLUDES",
    ".INTERRUPT",
    ".INVISIBLE",
    ".JOIN",
    ".LIBS",
    ".MADE",
    ".MAIN",
    ".MAKE",
    ".MAKEFLAGS",
    ".META",
    ".MFLAGS",
    ".NOMETA",
    ".NOMETA_CMP",
    ".NOPATH",
    ".NOREADONLY",
    ".NOTMAIN",
    ".NOTPARALLEL",
    ".NO_PARALLEL",
    ".NULL",
    ".OBJDIR",
    ".OPTIONAL",
    ".ORDER",
    ".PARALLEL",
    ".PATH",
    ".PHONY",
    ".POSIX",
    ".PRECIOUS",
    ".READONLY",
    ".RECURSIVE",
    ".SHELL",
    ".SILENT",
    ".SINGLESHELL",
    ".STALE",
    ".SUFFIXES",
    ".USE",
    ".USEBEFORE",
];

/// The special targets of POSIX.1-2024 make.
const POSIX_SPECIAL_TARGETS: &[&str] = &[
    ".DEFAULT",
    ".IGNORE",
    ".NOTPARALLEL",
    ".PHONY",
    ".POSIX",
    ".PRECIOUS",
    ".SCCS_GET",
    ".SILENT",
    ".SUFFIXES",
];

// TODO: check the nmake lists against nmake itself.
const NMAKE_SPECIAL_TARGETS: &[&str] = &[".IGNORE", ".PRECIOUS", ".SILENT", ".SUFFIXES"];

/// Whether `name` is a special target of `variant`.
pub(crate) fn is_special_target(name: &str, variant: MakefileVariant) -> bool {
    match variant {
        MakefileVariant::GNUMake => GNU_SPECIAL_TARGETS.contains(&name),
        MakefileVariant::BSDMake => {
            BSD_SPECIAL_TARGETS.contains(&name) || name.starts_with(".PATH.")
        }
        MakefileVariant::POSIXMake => POSIX_SPECIAL_TARGETS.contains(&name),
        MakefileVariant::NMake => NMAKE_SPECIAL_TARGETS.contains(&name),
    }
}

impl Makefile {
    /// The prerequisites of `target` in all rules for it, in source order.
    ///
    /// This is meant for special targets such as `.PRECIOUS`,
    /// `.INTERMEDIATE` or `.SECONDARY`, which can be listed more than once.
    /// Names are not expanded. See [`Self::special_target_prerequisites_for`]
    /// for other variants.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".PRECIOUS: a.o\nall:\n.PRECIOUS: %.c\n".parse().unwrap();
    /// assert_eq!(
    ///     makefile.special_target_prerequisites(".PRECIOUS").collect::<Vec<_>>(),
    ///     vec!["a.o", "%.c"]
    /// );
    /// ```
    pub fn special_target_prerequisites<'a>(
        &'a self,
        target: &'a str,
    ) -> impl Iterator<Item = String> + 'a {
        self.special_target_prerequisites_for(target, MakefileVariant::GNUMake)
    }

    /// The prerequisites of `target` in all rules for it, read as
    /// `variant` does; see [`Self::special_target_prerequisites`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = ".SECONDARY: a.c b.c\n".parse().unwrap();
    /// assert_eq!(
    ///     makefile
    ///         .special_target_prerequisites_for(".SECONDARY", MakefileVariant::BSDMake)
    ///         .collect::<Vec<_>>(),
    ///     vec!["a.c", "b.c"]
    /// );
    /// ```
    pub fn special_target_prerequisites_for<'a>(
        &'a self,
        target: &'a str,
        variant: MakefileVariant,
    ) -> impl Iterator<Item = String> + 'a {
        self.rules()
            .filter(move |rule| rule.targets_for(variant).any(|t| t == target))
            .flat_map(move |rule| rule.prerequisites_for(variant).collect::<Vec<_>>())
    }
}

impl Rule {
    /// Whether a target of this rule is a GNU make special target, such as
    /// `.PHONY` or `.PRECIOUS`; see [`Self::is_special_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".PHONY: all\nall:\n".parse().unwrap();
    /// let rules: Vec<_> = makefile.rules().collect();
    /// assert!(rules[0].is_special());
    /// assert!(!rules[1].is_special());
    /// ```
    pub fn is_special(&self) -> bool {
        self.is_special_for(MakefileVariant::GNUMake)
    }

    /// Whether a target of this rule is a special target of `variant`.
    ///
    /// For BSD make this includes the special sources such as `.USE`, and
    /// `.PATH.suffix`. Suffix rules are not special targets; see
    /// [`Self::is_suffix_rule_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{MakefileVariant, Rule};
    /// let rule: Rule = ".BEGIN:\n\techo start\n".parse().unwrap();
    /// assert!(rule.is_special_for(MakefileVariant::BSDMake));
    /// assert!(!rule.is_special_for(MakefileVariant::GNUMake));
    /// ```
    pub fn is_special_for(&self, variant: MakefileVariant) -> bool {
        self.targets_for(variant)
            .any(|t| is_special_target(&t, variant))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_special() {
        let makefile: Makefile = ".PHONY: a\n.PATH.c: src\n.BEGIN:\n.SCCS_GET:\nall:\n"
            .parse()
            .unwrap();
        let special = |variant| {
            makefile
                .rules()
                .map(|r| r.is_special_for(variant))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            special(MakefileVariant::GNUMake),
            vec![true, false, false, false, false]
        );
        assert_eq!(
            special(MakefileVariant::BSDMake),
            vec![true, true, true, false, false]
        );
        assert_eq!(
            special(MakefileVariant::POSIXMake),
            vec![true, false, false, true, false]
        );
    }

    #[test]
    fn test_special_target_prerequisites() {
        let makefile: Makefile = ".INTERMEDIATE: a.c\nall: x\n.INTERMEDIATE: b.c c.c\n"
            .parse()
            .unwrap();
        assert_eq!(
            makefile
                .special_target_prerequisites(".INTERMEDIATE")
                .collect::<Vec<_>>(),
            vec!["a.c", "b.c", "c.c"]
        );
        assert_eq!(
            makefile
                .special_target_prerequisites(".PRECIOUS")
                .collect::<Vec<_>>(),
            Vec::<String>::new()
        );
    }
}
