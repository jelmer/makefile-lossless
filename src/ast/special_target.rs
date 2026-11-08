//! Special targets and suffix rules.

use crate::lossless::{invalid_edit, Error, InvalidEditKind, Makefile, Rule};
use crate::{MakefileVariant, SyntaxKind};
use rowan::ast::AstNode;

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

    /// Whether any rule has `target` as a target, such as a
    /// `.DELETE_ON_ERROR:` line.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".ONESHELL:\nall:\n".parse().unwrap();
    /// assert!(makefile.has_special_target(".ONESHELL"));
    /// assert!(!makefile.has_special_target(".POSIX"));
    /// ```
    pub fn has_special_target(&self, target: &str) -> bool {
        self.rules_by_target(target).next().is_some()
    }

    /// Add a rule for `target` with no prerequisites, such as
    /// `.DELETE_ON_ERROR:`, unless there already is a rule for it.
    ///
    /// For targets such as `.SILENT` and `.IGNORE`, such a rule applies to
    /// every target, and an existing rule with prerequisites limits them to
    /// those; this does not change it.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = "all:\n".parse().unwrap();
    /// makefile.add_special_target(".ONESHELL").unwrap();
    /// makefile.add_special_target(".ONESHELL").unwrap();
    /// assert_eq!(makefile.to_string(), "all:\n\n.ONESHELL:\n");
    /// ```
    pub fn add_special_target(&mut self, target: &str) -> Result<(), Error> {
        if !self.has_special_target(target) {
            self.try_add_rule(target)?;
        }
        Ok(())
    }

    /// Remove `target` from every rule, removing the rules that have no
    /// other target.
    ///
    /// Returns whether there was a rule for `target`.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = ".NOTPARALLEL:\nall:\n".parse().unwrap();
    /// assert!(makefile.remove_special_target(".NOTPARALLEL").unwrap());
    /// assert!(!makefile.remove_special_target(".NOTPARALLEL").unwrap());
    /// assert_eq!(makefile.to_string(), "all:\n");
    /// ```
    pub fn remove_special_target(&mut self, target: &str) -> Result<bool, Error> {
        let rules: Vec<Rule> = self.rules_by_target(target).collect();
        let found = !rules.is_empty();
        for mut rule in rules {
            if rule.targets().all(|t| t == target) {
                rule.remove()?;
            } else {
                rule.remove_target(target)?;
            }
        }
        Ok(found)
    }

    /// Add `prerequisite` to `target`, such as a file to `.PRECIOUS` or a
    /// suffix to `.SUFFIXES`, unless a rule for `target` already lists it.
    ///
    /// It is added to the first rule outside a conditional whose only
    /// target is `target`, or else to a new rule at the end.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = ".PRECIOUS .SECONDARY: a.o\n".parse().unwrap();
    /// makefile.add_special_target_prerequisite(".PRECIOUS", "b.o").unwrap();
    /// makefile.add_special_target_prerequisite(".PRECIOUS", "b.o").unwrap();
    /// assert_eq!(makefile.to_string(), ".PRECIOUS .SECONDARY: a.o\n\n.PRECIOUS: b.o\n");
    /// ```
    pub fn add_special_target_prerequisite(
        &mut self,
        target: &str,
        prerequisite: &str,
    ) -> Result<(), Error> {
        if self
            .special_target_prerequisites(target)
            .any(|p| p == prerequisite)
        {
            return Ok(());
        }
        let existing = self.rules_by_target(target).find(|rule| {
            rule.targets().all(|t| t == target)
                && rule.syntax().parent().map(|p| p.kind()) == Some(SyntaxKind::ROOT)
        });
        let mut rule = match existing {
            Some(rule) => rule,
            None => self.try_add_rule(target)?,
        };
        rule.add_prerequisite(prerequisite)
    }

    /// Remove `prerequisite` from every rule for `target`, removing the
    /// rules it was the last prerequisite of.
    ///
    /// Returns whether `prerequisite` was listed. Removing a rule rather
    /// than leaving it without prerequisites matters for targets such as
    /// `.SUFFIXES`, where a bare rule means something else.
    ///
    /// # Errors
    ///
    /// Returns an [`Error::InvalidEdit`] of kind
    /// [`InvalidEditKind::Unsupported`], leaving the makefile unchanged, if
    /// a rule listing `prerequisite` has other targets as well.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile: Makefile = ".SUFFIXES: .c\nall:\n.SUFFIXES: .o .c\n".parse().unwrap();
    /// assert!(makefile.remove_special_target_prerequisite(".SUFFIXES", ".c").unwrap());
    /// assert_eq!(makefile.to_string(), "all:\n.SUFFIXES: .o\n");
    /// ```
    pub fn remove_special_target_prerequisite(
        &mut self,
        target: &str,
        prerequisite: &str,
    ) -> Result<bool, Error> {
        let rules: Vec<Rule> = self
            .rules_by_target(target)
            .filter(|rule| rule.prerequisites().any(|p| p == prerequisite))
            .collect();
        if let Some(rule) = rules
            .iter()
            .find(|rule| rule.targets().any(|t| t != target))
        {
            return Err(invalid_edit(
                InvalidEditKind::Unsupported,
                "Makefile::remove_special_target_prerequisite",
                format!(
                    "{prerequisite:?} is also a prerequisite of the other targets of {:?}",
                    rule.targets().collect::<Vec<_>>().join(" ")
                ),
            ));
        }
        let found = !rules.is_empty();
        for mut rule in rules {
            rule.remove_prerequisite(prerequisite)?;
            if rule.prerequisites().next().is_none() {
                rule.remove()?;
            }
        }
        Ok(found)
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

    #[test]
    fn test_special_target_flags() {
        let mut makefile: Makefile = "all:\n.DELETE_ON_ERROR .ONESHELL:\n".parse().unwrap();
        assert!(makefile.has_special_target(".ONESHELL"));
        assert!(makefile.remove_special_target(".ONESHELL").unwrap());
        assert_eq!(makefile.to_string(), "all:\n.DELETE_ON_ERROR:\n");
        assert!(makefile.has_special_target(".DELETE_ON_ERROR"));
        makefile.add_special_target(".POSIX").unwrap();
        assert_eq!(makefile.to_string(), "all:\n.DELETE_ON_ERROR:\n\n.POSIX:\n");
    }

    #[test]
    fn test_add_special_target_prerequisite_outside_conditional() {
        let mut makefile: Makefile = "ifdef X\n.PRECIOUS: a\nendif\n.PRECIOUS: b\n"
            .parse()
            .unwrap();
        makefile
            .add_special_target_prerequisite(".PRECIOUS", "c")
            .unwrap();
        assert_eq!(
            makefile.to_string(),
            "ifdef X\n.PRECIOUS: a\nendif\n.PRECIOUS: b c\n"
        );
        // Already listed, even if only in a conditional.
        makefile
            .add_special_target_prerequisite(".PRECIOUS", "a")
            .unwrap();
        assert_eq!(
            makefile.to_string(),
            "ifdef X\n.PRECIOUS: a\nendif\n.PRECIOUS: b c\n"
        );
    }

    #[test]
    fn test_remove_special_target_prerequisite_keeps_bare_rule() {
        let mut makefile: Makefile = ".SUFFIXES:\n.SUFFIXES: .c\n".parse().unwrap();
        assert!(makefile
            .remove_special_target_prerequisite(".SUFFIXES", ".c")
            .unwrap());
        assert_eq!(makefile.to_string(), ".SUFFIXES:\n");
        assert!(!makefile
            .remove_special_target_prerequisite(".SUFFIXES", ".c")
            .unwrap());
    }
}
