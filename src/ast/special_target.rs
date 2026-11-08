//! Special targets and suffix rules.

use crate::lossless::{Makefile, Rule};
use crate::MakefileVariant;
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

/// The suffixes GNU make knows before reading a makefile, unless run
/// with `-r`.
const GNU_DEFAULT_SUFFIXES: &[&str] = &[
    ".out", ".a", ".ln", ".o", ".c", ".cc", ".C", ".cpp", ".p", ".f", ".F", ".m", ".r", ".y", ".l",
    ".ym", ".yl", ".s", ".S", ".mod", ".sym", ".def", ".h", ".info", ".dvi", ".tex", ".texinfo",
    ".texi", ".txinfo", ".w", ".ch", ".web", ".sh", ".elc", ".el",
];

/// The suffixes of the POSIX.1-2017 default rules.
const POSIX_DEFAULT_SUFFIXES: &[&str] = &[
    ".o", ".c", ".y", ".l", ".a", ".sh", ".f", ".c~", ".y~", ".l~", ".sh~", ".f~",
];

const NMAKE_DEFAULT_SUFFIXES: &[&str] = &[
    ".exe", ".obj", ".asm", ".c", ".cpp", ".cxx", ".bas", ".cbl", ".for", ".pas", ".res", ".rc",
    ".f", ".f90",
];

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

fn default_suffixes(variant: MakefileVariant) -> &'static [&'static str] {
    match variant {
        MakefileVariant::GNUMake => GNU_DEFAULT_SUFFIXES,
        // bmake has no built-in suffixes; they come from sys.mk.
        MakefileVariant::BSDMake => &[],
        MakefileVariant::POSIXMake => POSIX_DEFAULT_SUFFIXES,
        MakefileVariant::NMake => NMAKE_DEFAULT_SUFFIXES,
    }
}

/// The known suffixes after the `.SUFFIXES` rules of `makefile` that start
/// before `before`, or after all of them.
// TODO: follow conditionals the way default_goal_candidates does, rather
// than reading the rules in every branch.
fn known_suffixes(
    makefile: &Makefile,
    variant: MakefileVariant,
    before: Option<rowan::TextSize>,
) -> Vec<String> {
    let mut suffixes: Vec<String> = default_suffixes(variant)
        .iter()
        .map(|s| s.to_string())
        .collect();
    for rule in makefile.rules() {
        if before.is_some_and(|pos| rule.syntax().text_range().start() >= pos) {
            break;
        }
        if !rule.targets_for(variant).any(|t| t == ".SUFFIXES") {
            continue;
        }
        let prerequisites: Vec<String> = rule.prerequisites_for(variant).collect();
        if prerequisites.is_empty() {
            suffixes.clear();
        }
        for suffix in prerequisites {
            if !suffixes.contains(&suffix) {
                suffixes.push(suffix);
            }
        }
    }
    suffixes
}

/// Whether `target` is one known suffix, or two concatenated.
fn is_suffix_target(target: &str, known: &[String]) -> bool {
    known.iter().any(|first| {
        target
            .strip_prefix(first.as_str())
            .is_some_and(|rest| rest.is_empty() || known.iter().any(|second| second == rest))
    })
}

/// The makefile `rule` is part of, if any.
fn enclosing_makefile(rule: &Rule) -> Option<Makefile> {
    rule.syntax().ancestors().last().and_then(Makefile::cast)
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

    /// The suffixes GNU make knows after reading this makefile, in order.
    ///
    /// This starts from GNU make's built-in list, as when make is run
    /// without `-r`. Each `.SUFFIXES` rule adds its prerequisites, and one
    /// without prerequisites clears the list. Names are not expanded, and
    /// `.SUFFIXES` rules in every branch of a conditional are read. See
    /// [`Self::suffixes_for`] for other variants.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".SUFFIXES:\n.SUFFIXES: .c .o\n".parse().unwrap();
    /// assert_eq!(makefile.suffixes(), vec![".c", ".o"]);
    /// ```
    pub fn suffixes(&self) -> Vec<String> {
        self.suffixes_for(MakefileVariant::GNUMake)
    }

    /// The suffixes `variant` knows after reading this makefile, in order;
    /// see [`Self::suffixes`].
    ///
    /// For POSIX make the list starts with the suffixes of the default
    /// rules. For BSD make it starts empty, since bmake gets its suffixes
    /// from `sys.mk`, which is not read.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = ".SUFFIXES: .c .o\n".parse().unwrap();
    /// assert_eq!(makefile.suffixes_for(MakefileVariant::BSDMake), vec![".c", ".o"]);
    /// ```
    pub fn suffixes_for(&self, variant: MakefileVariant) -> Vec<String> {
        known_suffixes(self, variant, None)
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

    /// Whether this is a GNU make suffix rule, such as `.c.o:` or `.c:`;
    /// see [`Self::is_suffix_rule_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = ".SUFFIXES: .c .o\n.c.o:\n\tcc -c $<\n.x.y:\n".parse().unwrap();
    /// let rules: Vec<_> = makefile.rules().collect();
    /// assert!(rules[1].is_suffix_rule());
    /// assert!(!rules[2].is_suffix_rule());
    /// ```
    pub fn is_suffix_rule(&self) -> bool {
        self.is_suffix_rule_for(MakefileVariant::GNUMake)
    }

    /// Whether this is a suffix rule as `variant` reads it: a target is a
    /// known suffix (a single-suffix rule) or two known suffixes
    /// concatenated (a double-suffix rule).
    ///
    /// The known suffixes are those of [`Makefile::suffixes_for`] for the
    /// makefile the rule is in. GNU and POSIX make use the suffixes known
    /// after reading the whole makefile, while BSD make only reads a rule
    /// as a transformation if its suffixes are known where it appears and
    /// are still known at the end.
    ///
    /// GNU make ignores the prerequisites of a suffix rule, with a warning,
    /// but POSIX make and GNU make with `.POSIX` anywhere in the makefile
    /// read a rule with prerequisites as an ordinary rule.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = ".c.o:\n\tcc -c $<\n.SUFFIXES: .c .o\n".parse().unwrap();
    /// let rule = makefile.rules().next().unwrap();
    /// assert!(rule.is_suffix_rule_for(MakefileVariant::GNUMake));
    /// assert!(!rule.is_suffix_rule_for(MakefileVariant::BSDMake));
    /// ```
    // TODO: nmake inference rules with search paths, such as
    // `{src}.c{obj}.obj:`, are not recognised.
    pub fn is_suffix_rule_for(&self, variant: MakefileVariant) -> bool {
        let Some(makefile) = enclosing_makefile(self) else {
            return false;
        };
        if self.prerequisites_for(variant).next().is_some()
            && (variant == MakefileVariant::POSIXMake
                || (variant == MakefileVariant::GNUMake
                    && makefile.rules_by_target(".POSIX").next().is_some()))
        {
            return false;
        }
        let mut known = known_suffixes(&makefile, variant, None);
        if variant == MakefileVariant::BSDMake {
            let here = known_suffixes(&makefile, variant, Some(self.syntax().text_range().start()));
            known.retain(|s| here.contains(s));
        }
        self.targets_for(variant)
            .any(|t| is_suffix_target(&t, &known))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn suffix_rules(text: &str, variant: MakefileVariant) -> Vec<String> {
        let makefile: Makefile = text.parse().unwrap();
        makefile
            .rules()
            .filter(|r| r.is_suffix_rule_for(variant))
            .map(|r| r.targets().collect::<Vec<_>>().join(" "))
            .collect()
    }

    #[test]
    fn test_suffixes_default() {
        let makefile: Makefile = "all:\n".parse().unwrap();
        assert_eq!(makefile.suffixes(), GNU_DEFAULT_SUFFIXES);
        assert_eq!(
            makefile.suffixes_for(MakefileVariant::BSDMake),
            Vec::<String>::new()
        );
        assert_eq!(
            makefile.suffixes_for(MakefileVariant::POSIXMake),
            POSIX_DEFAULT_SUFFIXES
        );
    }

    #[test]
    fn test_suffixes_clear_and_add() {
        let makefile: Makefile =
            ".SUFFIXES: .q\n.SUFFIXES:\n.SUFFIXES: .c .o .c\n.SUFFIXES: .o .h\n"
                .parse()
                .unwrap();
        assert_eq!(makefile.suffixes(), vec![".c", ".o", ".h"]);
    }

    #[test]
    fn test_suffix_rule_gnu() {
        assert_eq!(
            suffix_rules(
                ".SUFFIXES:\n.SUFFIXES: .c .o .q\n.c.o:\n.q:\n.x.o:\nfoo.c:\n",
                MakefileVariant::GNUMake
            ),
            vec![".c.o", ".q"]
        );
    }

    #[test]
    fn test_suffix_rule_needs_known_suffixes() {
        // `.SUFFIXES:` is itself a single-suffix rule only if `.SUFFIXES` is
        // a known suffix, which it is not.
        assert_eq!(
            suffix_rules(".SUFFIXES:\n.c.o:\n", MakefileVariant::GNUMake),
            Vec::<String>::new()
        );
        assert_eq!(
            suffix_rules(".c.o:\n.SUFFIXES:\n", MakefileVariant::GNUMake),
            Vec::<String>::new()
        );
    }

    #[test]
    fn test_suffix_rule_order() {
        // GNU make uses the suffixes known at the end; BSD make the ones
        // known where the rule appears that are still known at the end.
        let text = ".SUFFIXES:\n.SUFFIXES: .c\n.c.o:\n.SUFFIXES: .o\n";
        assert_eq!(suffix_rules(text, MakefileVariant::GNUMake), vec![".c.o"]);
        assert_eq!(
            suffix_rules(text, MakefileVariant::BSDMake),
            Vec::<String>::new()
        );
        let text = ".SUFFIXES: .c .o\n.c.o:\n.SUFFIXES:\n.SUFFIXES: .c .o\n";
        assert_eq!(suffix_rules(text, MakefileVariant::BSDMake), vec![".c.o"]);
        let text = ".SUFFIXES: .c .o\n.c.o:\n.SUFFIXES:\n";
        assert_eq!(
            suffix_rules(text, MakefileVariant::BSDMake),
            Vec::<String>::new()
        );
    }

    #[test]
    fn test_suffix_rule_with_prerequisites() {
        let text = ".SUFFIXES:\n.SUFFIXES: .c .o\n.c.o: foo.h\n";
        assert_eq!(suffix_rules(text, MakefileVariant::GNUMake), vec![".c.o"]);
        assert_eq!(suffix_rules(text, MakefileVariant::BSDMake), vec![".c.o"]);
        assert_eq!(
            suffix_rules(text, MakefileVariant::POSIXMake),
            Vec::<String>::new()
        );
        let text = ".SUFFIXES:\n.SUFFIXES: .c .o\n.c.o: foo.h\n.POSIX:\n";
        assert_eq!(
            suffix_rules(text, MakefileVariant::GNUMake),
            Vec::<String>::new()
        );
    }

    #[test]
    fn test_suffix_rule_among_other_targets() {
        assert_eq!(
            suffix_rules(
                ".SUFFIXES:\n.SUFFIXES: .c .o\nbar .c.o:\n",
                MakefileVariant::GNUMake
            ),
            vec!["bar .c.o"]
        );
    }

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
