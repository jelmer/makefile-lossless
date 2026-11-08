//! Pattern rules, suffix rules and implicit rule search.

use crate::lossless::{Makefile, Rule};
use crate::pattern::{
    pattern_match, split_pattern, static_pattern_match, substitute_stem, PatternMatch,
};
use crate::MakefileVariant;
use rowan::ast::AstNode;
use std::collections::HashSet;

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

impl Rule {
    /// Check whether this is a pattern rule, such as `%.o: %.c`
    ///
    /// GNU make reads a rule as a pattern rule when its first target has a
    /// `%` that is not quoted with a backslash. A static pattern rule is
    /// not one, as its targets are explicit. Variable references are not
    /// expanded, so a `%` that only comes from one is not seen. See
    /// [`Self::is_pattern_for`] for other variants.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "%.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
    /// assert!(rule.is_pattern());
    ///
    /// let rule: Rule = "100\\%.txt:\n".parse().unwrap();
    /// assert!(!rule.is_pattern());
    ///
    /// let rule: Rule = "a.o b.o: %.o: %.c\n".parse().unwrap();
    /// assert!(!rule.is_pattern());
    /// ```
    pub fn is_pattern(&self) -> bool {
        self.is_pattern_for(MakefileVariant::GNUMake)
    }

    /// Check whether this is a pattern rule, as `variant` reads it
    ///
    /// BSD make and nmake have no pattern rules, so this is always false
    /// for them. POSIX make is read like GNU make.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{MakefileVariant, Rule};
    /// let rule: Rule = "%.o: %.c\n".parse().unwrap();
    /// assert!(rule.is_pattern_for(MakefileVariant::GNUMake));
    /// assert!(!rule.is_pattern_for(MakefileVariant::BSDMake));
    /// ```
    pub fn is_pattern_for(&self, variant: MakefileVariant) -> bool {
        matches!(
            variant,
            MakefileVariant::GNUMake | MakefileVariant::POSIXMake
        ) && self.static_pattern_for(variant).is_none()
            && self
                .targets_with(variant.into())
                .next()
                .is_some_and(|t| crate::pattern::split_pattern(&t).is_some())
    }

    /// Get the stem with which this pattern rule matches `target`
    ///
    /// The stem is what the `%` matches, and what `$*` expands to in the
    /// recipe. The first of the rule's targets that matches is used. As in
    /// GNU make, a pattern without a `/` is matched against the file name
    /// only, and the directory is put back in front of the stem. Returns
    /// `None` if this is not a pattern rule, or none of its targets match.
    /// Targets with variable references never match. See
    /// [`Self::stem_for`] for other variants.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "lib%.a: %.o\n".parse().unwrap();
    /// assert_eq!(rule.stem("libfoo.a"), Some("foo".to_string()));
    /// assert_eq!(rule.stem("src/libfoo.a"), Some("src/foo".to_string()));
    /// assert_eq!(rule.stem("foo.a"), None);
    /// ```
    pub fn stem(&self, target: &str) -> Option<String> {
        self.stem_for(target, MakefileVariant::GNUMake)
    }

    /// Get the stem with which this pattern rule matches `target`, as
    /// `variant` reads the rule; see [`Self::is_pattern_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{MakefileVariant, Rule};
    /// let rule: Rule = "%.o: %.c\n".parse().unwrap();
    /// assert_eq!(
    ///     rule.stem_for("foo.o", MakefileVariant::GNUMake),
    ///     Some("foo".to_string())
    /// );
    /// assert_eq!(rule.stem_for("foo.o", MakefileVariant::BSDMake), None);
    /// ```
    pub fn stem_for(&self, target: &str, variant: MakefileVariant) -> Option<String> {
        if !self.is_pattern_for(variant) {
            return None;
        }
        self.targets_with(variant.into())
            .find_map(|pattern| crate::pattern::pattern_stem(&pattern, target))
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

impl Makefile {
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

    /// Find the first rule whose target matches the given pattern
    ///
    /// Supports make-style pattern matching where `%` in a rule's target acts as a wildcard.
    /// For example, a rule with target `%.o` will match `foo.o`, `bar.o`, etc.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
    /// let rule = makefile.find_rule_by_target_pattern("foo.o");
    /// assert!(rule.is_some());
    /// ```
    pub fn find_rule_by_target_pattern(&self, target: &str) -> Option<Rule> {
        self.rules_by_target_pattern(target).next()
    }

    /// Find all rules whose targets match the given pattern
    ///
    /// Supports make-style pattern matching where `%` in a rule's target acts as a wildcard.
    /// For example, a rule with target `%.o` will match `foo.o`, `bar.o`, etc.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n%.o: %.s\n\t$(AS) -o $@ $<\n".parse().unwrap();
    /// let rules: Vec<_> = makefile.rules_by_target_pattern("foo.o").collect();
    /// assert_eq!(rules.len(), 2);
    /// ```
    pub fn rules_by_target_pattern<'a>(
        &'a self,
        target: &'a str,
    ) -> impl Iterator<Item = Rule> + 'a {
        self.rules()
            .filter(move |rule| rule.has_target(target) || rule.stem(target).is_some())
    }

    /// Find all rules whose targets match the given pattern
    #[deprecated(since = "0.4.2", note = "use `rules_by_target_pattern` instead")]
    pub fn find_rules_by_target_pattern<'a>(
        &'a self,
        target: &'a str,
    ) -> impl Iterator<Item = Rule> + 'a {
        self.rules_by_target_pattern(target)
    }

    /// The implicit rule GNU make would use to make `target`, if any; see
    /// [`Self::implicit_rule_for`].
    ///
    /// `exists` says whether a file exists. This follows GNU make's
    /// implicit rule search: rules are tried with the shortest stem first,
    /// and a rule is used if each prerequisite exists, ought to exist
    /// because it is a target in the makefile or a prerequisite of
    /// `target`, or can be made by an implicit rule in turn (see
    /// [`ImplicitMatch::chain`]).
    ///
    /// There is no implicit rule for a phony target, or one with a recipe
    /// in the makefile. If no rule applies to a file that does not exist
    /// and has no rule in the makefile, the `.DEFAULT` rule is returned,
    /// with no stem or prerequisites.
    ///
    /// Only the rules in this makefile are used, not make's built-in rules,
    /// as with `make -r`; but the known suffixes include make's default
    /// ones, as [`Self::suffixes`] says. Names are not expanded, so a
    /// pattern rule with a variable reference in a target or prerequisite
    /// is not used. Rules in every branch of a conditional are read, and
    /// `vpath` and `.SECONDEXPANSION` are not taken into account.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n%.c: %.y\n\tyacc $<\n"
    ///     .parse()
    ///     .unwrap();
    /// let m = makefile.implicit_rule("src/foo.o", |f| f == "src/foo.y").unwrap();
    /// assert_eq!(m.stem(), "src/foo");
    /// assert_eq!(m.prerequisites(), ["src/foo.c"]);
    /// assert_eq!(m.chain()[0].target(), "src/foo.c");
    /// assert_eq!(m.chain()[0].prerequisites(), ["src/foo.y"]);
    /// ```
    // TODO: follow conditionals, as default_goal_candidates does; pass the
    // directories `vpath` and `VPATH` give to `exists`; and support
    // `.SECONDEXPANSION`.
    pub fn implicit_rule(
        &self,
        target: &str,
        exists: impl Fn(&str) -> bool,
    ) -> Option<ImplicitMatch> {
        self.implicit_rule_for(target, exists, MakefileVariant::GNUMake)
    }

    /// The implicit rule `variant` would use to make `target`; see
    /// [`Self::implicit_rule`].
    ///
    /// POSIX make is treated as GNU make, with POSIX's default suffixes.
    /// This is always `None` for BSD make and nmake, whose pattern and
    /// inference rules are not supported.
    pub fn implicit_rule_for(
        &self,
        target: &str,
        exists: impl Fn(&str) -> bool,
        variant: MakefileVariant,
    ) -> Option<ImplicitMatch> {
        if !matches!(
            variant,
            MakefileVariant::GNUMake | MakefileVariant::POSIXMake
        ) {
            return None;
        }
        if self
            .special_target_prerequisites_for(".PHONY", variant)
            .any(|p| p == target)
        {
            return None;
        }
        let mut targets = HashSet::new();
        let mut mentioned = HashSet::new();
        let mut explicit = Vec::new();
        for rule in self.rules().filter(|r| !r.is_pattern_for(variant)) {
            let rule_targets: Vec<String> = rule.targets_for(variant).collect();
            let static_pattern = rule.static_pattern_for(variant);
            let prerequisites: Vec<String> = rule
                .prerequisites_for(variant)
                .chain(rule.order_only_prerequisites_for(variant))
                .collect();
            for rule_target in &rule_targets {
                let names = match &static_pattern {
                    Some(pattern) => static_prerequisites(pattern, rule_target, &prerequisites),
                    None => prerequisites.clone(),
                };
                if rule_target == target {
                    if has_recipe(&rule) {
                        return None;
                    }
                    explicit.extend(names.iter().cloned());
                }
                mentioned.extend(names);
            }
            targets.extend(rule_targets);
        }
        targets.extend(self.special_target_prerequisites_for(".PHONY", variant));
        mentioned.extend(targets.iter().cloned());

        let candidates = self.implicit_rule_candidates(variant);
        let mut search = Search {
            in_use: vec![false; candidates.len()],
            candidates: &candidates,
            exists,
            targets,
            mentioned,
            impossible: HashSet::new(),
        };
        if let Some(found) = search.search(target, 0, &explicit, false) {
            return Some(found);
        }
        // make only uses `.DEFAULT` for a file that has no rule and does
        // not exist.
        if search.targets.contains(target) || (search.exists)(target) {
            return None;
        }
        Some(ImplicitMatch {
            rule: self.default_rule(variant)?,
            target: target.to_string(),
            stem: String::new(),
            prerequisites: vec![],
            order_only_prerequisites: vec![],
            chain: vec![],
        })
    }

    /// The `.DEFAULT` rule whose recipe make uses: the last one with a
    /// recipe, unless a later one with neither a recipe nor prerequisites
    /// clears it.
    fn default_rule(&self, variant: MakefileVariant) -> Option<Rule> {
        let mut default = None;
        for rule in self
            .rules()
            .filter(|r| r.targets_for(variant).any(|t| t == ".DEFAULT"))
        {
            if has_recipe(&rule) {
                default = Some(rule);
            } else if rule.prerequisites_for(variant).next().is_none()
                && rule.order_only_prerequisites_for(variant).next().is_none()
            {
                default = None;
            }
        }
        default
    }

    /// The pattern rules GNU make tries, in order: those in the makefile,
    /// then those converted from suffix rules.
    fn implicit_rule_candidates(&self, variant: MakefileVariant) -> Vec<Candidate> {
        let mut candidates = Vec::new();
        for rule in self.rules() {
            if !rule.is_pattern_for(variant) {
                continue;
            }
            let targets: Vec<String> = rule.targets_for(variant).collect();
            // make rejects a pattern rule with a target that is not a
            // pattern.
            if targets.iter().any(|t| split_pattern(t).is_none()) {
                continue;
            }
            let candidate = Candidate {
                targets,
                prerequisites: rule.prerequisites_for(variant).collect(),
                order_only: rule.order_only_prerequisites_for(variant).collect(),
                has_recipe: has_recipe(&rule),
                terminal: rule.is_double_colon(),
                rule: Some(rule),
            };
            add_candidate(&mut candidates, candidate, true);
        }

        // make uses the last recipe given for a file.
        let suffix_rules: Vec<Rule> = self
            .rules()
            .filter(|r| has_recipe(r) && r.is_suffix_rule_for(variant))
            .collect();
        let recipe_rule = |name: &str| {
            suffix_rules
                .iter()
                .rev()
                .find(|r| r.targets_for(variant).any(|t| t == name))
                .cloned()
        };
        let suffixes = self.suffixes_for(variant);
        for source in &suffixes {
            add_candidate(
                &mut candidates,
                Candidate {
                    rule: None,
                    targets: vec![format!("%{source}")],
                    prerequisites: vec![],
                    order_only: vec![],
                    has_recipe: false,
                    terminal: false,
                },
                false,
            );
            if let Some(rule) = recipe_rule(source) {
                add_candidate(
                    &mut candidates,
                    Candidate {
                        rule: Some(rule),
                        targets: vec!["%".to_string()],
                        prerequisites: vec![format!("%{source}")],
                        order_only: vec![],
                        has_recipe: true,
                        terminal: false,
                    },
                    false,
                );
            }
            // TODO: GNU make also turns `.X.a:` into the archive member
            // rule `(%.o): %.X`.
            for target in suffixes.iter().filter(|t| *t != source) {
                let name = format!("{source}{target}");
                let Some(rule) = recipe_rule(&name) else {
                    continue;
                };
                add_candidate(
                    &mut candidates,
                    Candidate {
                        rule: Some(rule),
                        targets: vec![format!("%{target}")],
                        prerequisites: vec![format!("%{source}")],
                        order_only: vec![],
                        has_recipe: true,
                        terminal: false,
                    },
                    false,
                );
            }
        }
        candidates
    }
}

/// The implicit rule make would use for a file, as found by
/// [`Makefile::implicit_rule`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplicitMatch {
    rule: Rule,
    target: String,
    stem: String,
    prerequisites: Vec<String>,
    order_only_prerequisites: Vec<String>,
    chain: Vec<ImplicitMatch>,
}

impl ImplicitMatch {
    /// The pattern rule, the suffix rule such as `.c.o:`, or the `.DEFAULT`
    /// rule.
    pub fn rule(&self) -> &Rule {
        &self.rule
    }

    /// The file this rule makes.
    pub fn target(&self) -> &str {
        &self.target
    }

    /// The stem, as make sets `$*`: the part of the file name the `%`
    /// matched, with the directory in front if the pattern has no `/`.
    pub fn stem(&self) -> &str {
        &self.stem
    }

    /// The prerequisites, with the stem substituted.
    pub fn prerequisites(&self) -> &[String] {
        &self.prerequisites
    }

    /// The order-only prerequisites, with the stem substituted.
    pub fn order_only_prerequisites(&self) -> &[String] {
        &self.order_only_prerequisites
    }

    /// The matches for the prerequisites that do not exist and are made
    /// by implicit rules in turn, as intermediate files.
    pub fn chain(&self) -> &[ImplicitMatch] {
        &self.chain
    }
}

/// A pattern rule in the order make tries them, from a pattern rule in
/// the makefile or converted from a suffix rule.
struct Candidate {
    /// The rule it comes from; `None` for the rule make adds for each known
    /// suffix, which only stops match-anything rules from being used.
    rule: Option<Rule>,
    targets: Vec<String>,
    prerequisites: Vec<String>,
    order_only: Vec<String>,
    has_recipe: bool,
    terminal: bool,
}

impl Candidate {
    fn all_prerequisites(&self) -> impl Iterator<Item = &String> {
        self.prerequisites.iter().chain(&self.order_only)
    }

    fn is_match_anything(&self) -> bool {
        self.targets.iter().any(|t| t == "%")
    }
}

/// Add `new` to `candidates` as GNU make adds a pattern rule. An earlier
/// rule with the same prerequisites, all of whose targets are one of the
/// targets of `new`, is replaced, with `new` going at the end; if
/// `replace` is false, `new` is dropped instead.
fn add_candidate(candidates: &mut Vec<Candidate>, new: Candidate, replace: bool) {
    let same = candidates.iter().position(|old| {
        new.targets
            .iter()
            .any(|t| old.targets.iter().all(|o| o == t))
            && old.all_prerequisites().eq(new.all_prerequisites())
    });
    match same {
        Some(_) if !replace => return,
        Some(i) => {
            candidates.remove(i);
        }
        None => {}
    }
    candidates.push(new);
}

/// The prerequisites a static pattern rule with target pattern `pattern`
/// gives `target`: none if `target` does not match it.
fn static_prerequisites(pattern: &str, target: &str, prerequisites: &[String]) -> Vec<String> {
    let Some(m) = static_pattern_match(pattern, target) else {
        return vec![];
    };
    // Names with variable references can not be known, so are left out.
    prerequisites
        .iter()
        .filter_map(|p| substitute_stem(p, &m))
        .collect()
}

fn has_recipe(rule: &Rule) -> bool {
    rule.recipe_nodes().next().is_some()
}

/// A rule that matched `target`, as make keeps them while searching.
struct Try<'a> {
    candidate: usize,
    m: PatternMatch<'a>,
    rejected: bool,
}

struct Search<'a, F> {
    candidates: &'a [Candidate],
    exists: F,
    /// Files that are targets of explicit rules or phony.
    targets: HashSet<String>,
    /// Files that are targets or prerequisites of explicit rules.
    mentioned: HashSet<String>,
    in_use: Vec<bool>,
    impossible: HashSet<String>,
}

impl<F: Fn(&str) -> bool> Search<'_, F> {
    /// GNU make's `pattern_search`: find a rule for `name`, with
    /// `recursions` rules above it in the chain. `explicit` are the
    /// prerequisites the makefile gives for `name`. With `compat`, a
    /// prerequisite mentioned anywhere in the makefile ought to exist.
    fn search(
        &mut self,
        name: &str,
        recursions: usize,
        explicit: &[String],
        compat: bool,
    ) -> Option<ImplicitMatch> {
        let candidates = self.candidates;
        let mut tries = Vec::new();
        let mut specific_rule_matched = false;
        for (i, candidate) in candidates.iter().enumerate() {
            let has_prerequisites = candidate.all_prerequisites().next().is_some();
            if (has_prerequisites && !candidate.has_recipe) || self.in_use[i] {
                continue;
            }
            for target in &candidate.targets {
                // A match-anything rule can only make an intermediate file
                // if it is terminal.
                if recursions > 0 && target == "%" && !candidate.terminal {
                    continue;
                }
                let Some(m) = pattern_match(target, name) else {
                    continue;
                };
                if target != "%" {
                    specific_rule_matched = true;
                }
                if !has_prerequisites && !candidate.has_recipe {
                    continue;
                }
                tries.push(Try {
                    candidate: i,
                    m,
                    rejected: false,
                });
            }
        }
        tries.sort_by_key(|t| t.m.dir.len() + t.m.stem.len());
        if specific_rule_matched {
            for t in &mut tries {
                let candidate = &candidates[t.candidate];
                if !candidate.terminal && candidate.is_match_anything() {
                    t.rejected = true;
                }
            }
        }

        let mut found_compat_rule = false;
        for intermediates_ok in [false, true] {
            for t in tries.iter_mut() {
                let candidate = &candidates[t.candidate];
                if t.rejected || (intermediates_ok && candidate.terminal) {
                    continue;
                }
                let substitute = |names: &[String]| -> Option<Vec<String>> {
                    names.iter().map(|p| substitute_stem(p, &t.m)).collect()
                };
                // TODO: expand variable references in prerequisites;
                // until then a rule that needs it is not used.
                let (Some(prerequisites), Some(order_only)) = (
                    substitute(&candidate.prerequisites),
                    substitute(&candidate.order_only),
                ) else {
                    t.rejected = true;
                    continue;
                };
                self.in_use[t.candidate] = true;
                let mut chain = Vec::new();
                let mut failed = false;
                for prerequisite in prerequisites.iter().chain(&order_only) {
                    match self.check_prerequisite(
                        prerequisite,
                        recursions,
                        explicit,
                        compat,
                        intermediates_ok,
                        &mut found_compat_rule,
                    ) {
                        Prerequisite::Available => {}
                        Prerequisite::Intermediate(m) => chain.push(m),
                        Prerequisite::Impossible => {
                            t.rejected = true;
                            failed = true;
                            break;
                        }
                        Prerequisite::Missing => {
                            failed = true;
                            break;
                        }
                    }
                }
                self.in_use[t.candidate] = false;
                if failed {
                    continue;
                }
                return Some(ImplicitMatch {
                    rule: candidate
                        .rule
                        .clone()
                        .expect("rules without prerequisites or recipe are not tried"),
                    target: name.to_string(),
                    stem: t.m.full_stem(),
                    prerequisites,
                    order_only_prerequisites: order_only,
                    chain,
                });
            }
        }
        if found_compat_rule && !compat {
            return self.search(name, recursions, explicit, true);
        }
        None
    }

    fn check_prerequisite(
        &mut self,
        name: &str,
        recursions: usize,
        explicit: &[String],
        compat: bool,
        intermediates_ok: bool,
        found_compat_rule: &mut bool,
    ) -> Prerequisite {
        if self.impossible.contains(name) {
            return Prerequisite::Impossible;
        }
        if self.targets.contains(name) || explicit.iter().any(|e| e == name) || (self.exists)(name)
        {
            return Prerequisite::Available;
        }
        let mentioned = self.mentioned.contains(name);
        if mentioned && compat {
            return Prerequisite::Available;
        }
        // A prerequisite only mentioned elsewhere does not qualify as ought
        // to exist, but makes make search again allowing it if nothing else
        // is found.
        *found_compat_rule |= mentioned;
        if !intermediates_ok {
            return Prerequisite::Missing;
        }
        if let Some(m) = self.search(name, recursions + 1, &[], compat) {
            return Prerequisite::Intermediate(m);
        }
        if !mentioned {
            self.impossible.insert(name.to_string());
        }
        Prerequisite::Missing
    }
}

enum Prerequisite {
    /// It exists or ought to exist.
    Available,
    /// It can be made by this implicit rule.
    Intermediate(ImplicitMatch),
    /// An earlier search found it can not be made.
    Impossible,
    Missing,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The implicit rule for `target` in `text`, with the files in
    /// `files` existing, as `recipe: target <- prerequisites`, followed by
    /// the chain in parentheses. `.SUFFIXES:` comes first, which clears the
    /// default suffixes as `make -r` does.
    fn find(text: &str, target: &str, files: &[&str]) -> Option<String> {
        let makefile: Makefile = format!(".SUFFIXES:\n{text}").parse().unwrap();
        makefile
            .implicit_rule(target, |f| files.contains(&f))
            .map(|m| describe(&m))
    }

    fn describe(m: &ImplicitMatch) -> String {
        let recipe = m.rule().recipes().next().unwrap_or_default();
        let mut prerequisites = m.prerequisites().to_vec();
        if !m.order_only_prerequisites().is_empty() {
            prerequisites.push("|".to_string());
            prerequisites.extend(m.order_only_prerequisites().iter().cloned());
        }
        let mut s = format!("{recipe}: {} <- {}", m.target(), prerequisites.join(" "));
        for c in m.chain() {
            s.push_str(&format!(" ({})", describe(c)));
        }
        s
    }

    fn some(s: &str) -> Option<String> {
        Some(s.to_string())
    }

    #[test]
    fn test_directory_and_plain_prerequisites() {
        let text = "%.o: %.c common.h\n\tR1\n";
        assert_eq!(
            find(text, "foo.o", &["foo.c", "common.h"]),
            some("R1: foo.o <- foo.c common.h")
        );
        // The directory goes in front of the prerequisites with a `%` only.
        assert_eq!(
            find(text, "d/foo.o", &["d/foo.c", "common.h"]),
            some("R1: d/foo.o <- d/foo.c common.h")
        );
        assert_eq!(find(text, "d/foo.o", &["d/foo.c", "d/common.h"]), None);
        assert_eq!(find(text, "foo.o", &["foo.c"]), None);

        let text = "src/%.o: src/%.c\n\tR2\n";
        let makefile: Makefile = text.parse().unwrap();
        let m = makefile
            .implicit_rule("src/a/foo.o", |f| f == "src/a/foo.c")
            .unwrap();
        assert_eq!(m.stem(), "a/foo");
        assert_eq!(find(text, "x/src/foo.o", &["x/src/foo.c"]), None);
    }

    #[test]
    fn test_shortest_stem_first() {
        let text = "%.o: %.c\n\tgeneric\nlib%.o: lib%.c\n\tlib\n%.o: %.s\n\tasm\n";
        assert_eq!(
            find(text, "libx.o", &["libx.c", "libx.s"]),
            some("lib: libx.o <- libx.c")
        );
        // Equal stems are tried in makefile order.
        assert_eq!(
            find(text, "x.o", &["x.c", "x.s"]),
            some("generic: x.o <- x.c")
        );
        assert_eq!(find(text, "x.o", &["x.s"]), some("asm: x.o <- x.s"));
        let text = "%.o: %.s\n\tasm\n%.o: %.c\n\tgeneric\n";
        assert_eq!(find(text, "x.o", &["x.c", "x.s"]), some("asm: x.o <- x.s"));
        // The directory counts towards the length of the stem.
        for text in [
            "%.o: %.c\n\tnodir\nd/%.o: d/%.c\n\twithdir\n",
            "d/%.o: d/%.c\n\twithdir\n%.o: %.c\n\tnodir\n",
        ] {
            assert_eq!(
                find(text, "d/x.o", &["d/x.c"]),
                some("withdir: d/x.o <- d/x.c")
            );
        }
    }

    #[test]
    fn test_rules_without_recipe() {
        let files = ["x.c", "x.s", "foo.h"];
        let cases = [
            ("%.o: %.c\n", None),
            // An identical rule without a recipe cancels the earlier one.
            ("%.o: %.c\n\tc\n%.o: %.c\n", None),
            (
                "%.o: %.c\n\tc\n%.o: %.s\n\ts\n%.o: %.c\n",
                some("s: x.o <- x.s"),
            ),
            // An identical rule replaces the earlier one, at the end.
            (
                "%.o: %.c\n\tc1\n%.o: %.c\n\tc2\n%.o: %.s\n\ts\n",
                some("c2: x.o <- x.c"),
            ),
            (
                "%.o: %.c\n\tc1\n%.o: %.s\n\ts\n%.o: %.c\n\tc2\n",
                some("s: x.o <- x.s"),
            ),
            // Other prerequisites, or in another order, do not cancel it,
            // and a rule without a recipe is not used.
            ("%.o: %.c\n\tc\n%.o: %.c foo.h\n", some("c: x.o <- x.c")),
            ("%.o: %.c foo.h\n%.o: %.c\n\tc\n", some("c: x.o <- x.c")),
            ("%.o: %.c foo.h\n", None),
            (
                "%.o: %.c foo.h\n\ta\n%.o: foo.h %.c\n",
                some("a: x.o <- x.c foo.h"),
            ),
        ];
        for (text, expected) in cases {
            assert_eq!(find(text, "x.o", &files), expected, "{text:?}");
        }
    }

    #[test]
    fn test_replacing_rules_with_several_targets() {
        let files = ["x.c", "x.s"];
        let cases = [
            ("%.a %.b: %.c\n\tab\n%.b %.a: %.c\n", some("ab: x.a <- x.c")),
            ("%.a %.b: %.c\n\tab\n%.a: %.c\n", some("ab: x.a <- x.c")),
            // A rule is replaced if all its targets are one of the new
            // rule's targets.
            ("%.a: %.c\n\ta\n%.a %.b: %.c\n", None),
            (
                "%.a: %.c\n\ta\n%.b %.a: %.c\n\tba\n%.a: %.s\n\ts\n",
                some("ba: x.a <- x.c"),
            ),
            ("%.a %.a: %.c\n\taa\n%.a: %.c\n", None),
        ];
        for (text, expected) in cases {
            assert_eq!(find(text, "x.a", &files), expected, "{text:?}");
        }
    }

    #[test]
    fn test_match_anything_rules() {
        let any = "%: %.in\n\tany\n";
        assert_eq!(find(any, "x", &["x.in"]), some("any: x <- x.in"));
        let text = format!("{any}%.o: %.c\n\tc\n");
        // A rule for `%.o` matching, even if it can not be used, rules out
        // the match-anything rule.
        assert_eq!(find(&text, "x.o", &["x.o.in"]), None);
        assert_eq!(find(&text, "x.z", &["x.z.in"]), some("any: x.z <- x.z.in"));
        assert_eq!(find(&format!("{any}%.o:\n"), "x.o", &["x.o.in"]), None);
        // A rule with prerequisites but no recipe does not.
        assert_eq!(
            find(&format!("{any}%.o: %.c foo.h\n"), "x.o", &["x.o.in"]),
            some("any: x.o <- x.o.in")
        );
        // A terminal match-anything rule stays.
        assert_eq!(
            find("%:: %.in\n\tterm\n%.o: %.c\n\tc\n", "x.o", &["x.o.in"]),
            some("term: x.o <- x.o.in")
        );
    }

    #[test]
    fn test_default_suffixes_rule_out_match_anything() {
        // make adds a rule `%.h:` for the default suffix `.h`.
        let makefile: Makefile = "%: %.in\n\tany\n".parse().unwrap();
        let exists = |f: &str| f == "x.h.in" || f == "x.zz.in";
        assert_eq!(makefile.implicit_rule("x.h", exists), None);
        assert_eq!(
            makefile.implicit_rule("x.zz", exists).map(|m| describe(&m)),
            some("any: x.zz <- x.zz.in")
        );
    }

    #[test]
    fn test_ought_to_exist() {
        let rule = "%.o: %.c\n\tc\n";
        let cases = [
            ("x.c:\n\techo\n", true),
            ("x.o: x.c\n", true),
            ("x.c: ;\n", true),
            ("x.c: y\n", true),
            (".PHONY: x.c\n", true),
            // Mentioned elsewhere, which a second search for compatibility
            // allows.
            ("other: x.c\n", true),
            ("other: | x.c\n", true),
            (".PRECIOUS: x.c\n", true),
            // Not mentioned.
            ("other: $(X)\nX = x.c\n", false),
            ("%.z: x.c\n\techo\n", false),
        ];
        for (extra, expected) in cases {
            let text = format!("{rule}{extra}");
            assert_eq!(
                find(&text, "x.o", &["y"]),
                expected.then(|| "c: x.o <- x.c".to_string()),
                "{extra:?}"
            );
        }
    }

    #[test]
    fn test_static_pattern_prerequisites() {
        let rule = "%.o: %.c\n\tc\n";
        // A static pattern rule gives each target its prerequisites, with
        // the stem substituted, as an explicit rule does.
        assert_eq!(
            find(&format!("a.o: %.o: %.c\n{rule}"), "a.o", &[]),
            some("c: a.o <- a.c")
        );
        // They are mentioned, for the second search.
        assert_eq!(
            find(&format!("d.o: %.o: c.c\n\t@:\n{rule}"), "c.o", &[]),
            some("c: c.o <- c.c")
        );
        assert_eq!(find(rule, "c.o", &[]), None);
        // A target that does not match the target pattern gets no
        // prerequisites, and the directory is part of the match.
        assert_eq!(
            find(
                &format!("other d/xa.o: x%.o: %.c a.c\n\t@:\n{rule}"),
                "a.o",
                &[]
            ),
            None
        );
        // The stem of a static pattern rule may be empty.
        let needs_dot_c = "%.z: .c\n\tz\n";
        assert_eq!(
            find(&format!(".o: %.o: %.c\n\t@:\n{needs_dot_c}"), "a.z", &[]),
            some("z: a.z <- .c")
        );
        assert_eq!(find(needs_dot_c, "a.z", &[]), None);
    }

    #[test]
    fn test_default_rule() {
        let default = ".DEFAULT: ignored\n\tdefault\n";
        // `.DEFAULT` is used when there is no rule, with no stem or
        // prerequisites.
        assert_eq!(find(default, "x", &[]), some("default: x <- "));
        let m = format!("{default}%.o: %.c\n\tc\n")
            .parse::<Makefile>()
            .unwrap()
            .implicit_rule("a.o", |_| false)
            .unwrap();
        assert_eq!(m.rule().targets().collect::<Vec<_>>(), vec![".DEFAULT"]);
        assert_eq!(m.stem(), "");
        assert_eq!(m.prerequisites(), &[] as &[String]);
        // Not for a file that exists, a target with a rule, or a phony
        // target.
        assert_eq!(find(default, "x", &["x"]), None);
        assert_eq!(find(&format!("{default}y: z\n"), "y", &[]), None);
        assert_eq!(
            find(&format!("{default}y: z\n"), "z", &[]),
            some("default: z <- ")
        );
        assert_eq!(find(&format!("{default}.PHONY: p\n"), "p", &[]), None);
        // The last recipe is used, and `.DEFAULT:` without a recipe or
        // prerequisites clears it.
        let two = ".DEFAULT:\n\tfirst\n.DEFAULT:\n\tsecond\n";
        assert_eq!(find(two, "x", &[]), some("second: x <- "));
        assert_eq!(find(".DEFAULT:\n\tfirst\n.DEFAULT:\n", "x", &[]), None);
        assert_eq!(
            find(".DEFAULT:\n\tfirst\n.DEFAULT: foo\n", "x", &[]),
            some("first: x <- ")
        );
        assert_eq!(
            find(".DEFAULT:\n\tfirst\n.DEFAULT: ;\n", "x", &[]),
            some(": x <- ")
        );
    }

    #[test]
    fn test_chains() {
        let text = "%.o: %.c\n\tc\n%.c: %.y\n\ty\n";
        assert_eq!(
            find(text, "x.o", &["x.y"]),
            some("c: x.o <- x.c (y: x.c <- x.y)")
        );
        assert_eq!(find(text, "x.o", &["x.y", "x.c"]), some("c: x.o <- x.c"));
        let text = "%.o: %.c\n\tc\n%.c: %.y\n\ty\n%.y: %.w\n\tw\n";
        assert_eq!(
            find(text, "x.o", &["x.w"]),
            some("c: x.o <- x.c (y: x.c <- x.y (w: x.y <- x.w))")
        );
        let text = "%.o: %.c %.h\n\tc\n%.c: %.y\n\ty\n";
        assert_eq!(
            find(text, "x.o", &["x.y", "x.h"]),
            some("c: x.o <- x.c x.h (y: x.c <- x.y)")
        );
        assert_eq!(find(text, "x.o", &["x.y"]), None);
        let text = "%.o: %.c\n\tc\n%.c: %.y\n\ty\nx.y:\n\texplicit\n";
        assert_eq!(
            find(text, "x.o", &[]),
            some("c: x.o <- x.c (y: x.c <- x.y)")
        );
        // A rule is used once in a chain.
        let text = "%.q: %.q.q\n\tq\n";
        assert_eq!(find(text, "f.q", &["f.q.q.q"]), None);
        assert_eq!(find(text, "f.q", &["f.q.q"]), some("q: f.q <- f.q.q"));
    }

    #[test]
    fn test_chains_and_terminal_rules() {
        // A terminal rule can make an intermediate file, but does not use
        // one.
        assert_eq!(
            find("%.o: %.c\n\tc\n%.c:: %.y\n\tterm\n", "x.o", &["x.y"]),
            some("c: x.o <- x.c (term: x.c <- x.y)")
        );
        assert_eq!(
            find("%.o:: %.c\n\tterm\n%.c: %.y\n\ty\n", "x.o", &["x.y"]),
            None
        );
        assert_eq!(
            find("%.o:: %.c\n\tterm\nx.c:\n\texplicit\n", "x.o", &[]),
            some("term: x.o <- x.c")
        );
        // Only a terminal match-anything rule makes intermediate files.
        assert_eq!(
            find("%.o: %.c\n\tc\n%: %.in\n\tany\n", "x.o", &["x.c.in"]),
            None
        );
        assert_eq!(
            find("%.o: %.c\n\tc\n%:: %.in\n\tany\n", "x.o", &["x.c.in"]),
            some("c: x.o <- x.c (any: x.c <- x.c.in)")
        );
    }

    #[test]
    fn test_compatibility_search_in_chain() {
        let text = "%.o: %.c\n\tc\n%.c: %.y\n\ty\nother: x.y\n";
        assert_eq!(
            find(text, "x.o", &[]),
            some("c: x.o <- x.c (y: x.c <- x.y)")
        );
    }

    #[test]
    fn test_order_only_prerequisites() {
        let text = "%.o: %.c | %.d\n\tc\n";
        assert_eq!(find(text, "x.o", &["x.c"]), None);
        assert_eq!(
            find(text, "x.o", &["x.c", "x.d"]),
            some("c: x.o <- x.c | x.d")
        );
    }

    #[test]
    fn test_explicit_targets() {
        let rule = "%.o: %.c\n\tc\n";
        let files = ["x.c"];
        assert_eq!(find(&format!("{rule}x.o::\n\tdc\n"), "x.o", &files), None);
        assert_eq!(
            find(&format!("{rule}x.o::\n"), "x.o", &files),
            some("c: x.o <- x.c")
        );
        assert_eq!(find(&format!("{rule}.PHONY: x.o\n"), "x.o", &files), None);
    }

    #[test]
    fn test_suffix_rules() {
        let pattern = "%.r: %.q\n\tpattern\n";
        // A suffix rule does not replace a pattern rule, and comes after
        // the pattern rules.
        assert_eq!(
            find(
                &format!(".SUFFIXES: .q .r\n.q.r:\n\tsuffix\n{pattern}"),
                "x.r",
                &["x.q"]
            ),
            some("pattern: x.r <- x.q")
        );
        assert_eq!(
            find(
                ".SUFFIXES: .q .r .s\n.q.r:\n\tsuffix\n%.r: %.s\n\tpattern\n",
                "x.r",
                &["x.q", "x.s"]
            ),
            some("pattern: x.r <- x.s")
        );
        assert_eq!(
            find(".SUFFIXES: .q .r\n.q.r:\n\tsuffix\n", "x.r", &["x.q"]),
            some("suffix: x.r <- x.q")
        );
        assert_eq!(
            find(
                ".SUFFIXES: .q .r\n.q.r:\n\tfirst\n.q.r:\n\tsecond\n",
                "x.r",
                &["x.q"]
            ),
            some("second: x.r <- x.q")
        );
        let single = ".SUFFIXES: .q\n.q:\n\tsingle\n";
        assert_eq!(find(single, "x", &["x.q"]), some("single: x <- x.q"));
        // A single-suffix rule is a match-anything rule that is not terminal.
        let text = ".SUFFIXES: .q .r\n.q:\n\tsingle\n";
        assert_eq!(find(text, "x.r", &["x.r.q"]), None);
        assert_eq!(find(text, "x.z", &["x.z.q"]), some("single: x.z <- x.z.q"));
        assert_eq!(
            find(&format!("%.o: %.c\n\tc\n{single}"), "x.o", &["x.c.q"]),
            None
        );
        // The rule for a known suffix rules out match-anything rules.
        let text = ".SUFFIXES: .q\n%: %.in\n\tany\n";
        assert_eq!(find(text, "x.q", &["x.q.in"]), None);
        assert_eq!(find(text, "x.z", &["x.z.in"]), some("any: x.z <- x.z.in"));
    }

    #[test]
    fn test_implicit_rule_suffix_rule_with_prerequisites() {
        // GNU make ignores the prerequisites of a suffix rule, unless
        // `.POSIX` makes it an ordinary rule.
        let text = ".SUFFIXES: .c .o\n.c.o: foo.h\n\tsuffix\n";
        assert_eq!(
            find(text, "x.o", &["x.c", "foo.h"]),
            some("suffix: x.o <- x.c")
        );
        assert_eq!(
            find(&format!("{text}.POSIX:\n"), "x.o", &["x.c", "foo.h"]),
            None
        );
    }

    #[test]
    fn test_trailing_slash() {
        let makefile: Makefile = "x%:\n\tx\n".parse().unwrap();
        let stem = |t| {
            makefile
                .implicit_rule(t, |_| false)
                .map(|m| m.stem().to_string())
        };
        assert_eq!(stem("a/xb/"), some("a/b/"));
        assert_eq!(stem("xb/"), some("b/"));
    }

    #[test]
    fn test_other_variants() {
        let makefile: Makefile = "%.o: %.c\n\tc\n".parse().unwrap();
        let found = |variant| {
            makefile
                .implicit_rule_for("x.o", |f| f == "x.c", variant)
                .is_some()
        };
        assert!(found(MakefileVariant::GNUMake));
        assert!(found(MakefileVariant::POSIXMake));
        assert!(!found(MakefileVariant::BSDMake));
        assert!(!found(MakefileVariant::NMake));
    }

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
    fn test_is_pattern() {
        let cases = [
            ("%.o: %.c\n", true),
            ("%.tab.c %.tab.h: %.y\n", true),
            ("%:: %.in\n", true),
            ("$(DIR)/%.o: %.c\n", true),
            ("foo.o: foo.c\n", false),
            ("a\\%b:\n", false),
            ("a\\\\%b:\n", true),
            // make reads a rule whose first target is explicit as an
            // explicit rule, with a warning.
            ("explicit %.w:\n", false),
            ("$(patsubst %.c,%.o,x.c):\n", false),
            ("s1.v s2.v: %.v: %.u\n", false),
        ];
        for (text, expected) in cases {
            let rule: Rule = text.parse().unwrap();
            assert_eq!(rule.is_pattern(), expected, "{text:?}");
        }
    }

    #[test]
    fn test_is_pattern_for() {
        let rule: Rule = "%.o: %.c\n".parse().unwrap();
        let results: Vec<_> = [
            MakefileVariant::GNUMake,
            MakefileVariant::BSDMake,
            MakefileVariant::NMake,
            MakefileVariant::POSIXMake,
        ]
        .into_iter()
        .map(|v| rule.is_pattern_for(v))
        .collect();
        assert_eq!(results, vec![true, false, false, true]);
    }

    #[test]
    fn test_stem() {
        let rule: Rule = "%.tab.c %.tab.h: %.y\n\tbison $<\n".parse().unwrap();
        assert_eq!(rule.stem("parse.tab.c"), Some("parse".to_string()));
        assert_eq!(rule.stem("parse.tab.h"), Some("parse".to_string()));
        assert_eq!(rule.stem("src/parse.tab.h"), Some("src/parse".to_string()));
        assert_eq!(rule.stem("parse.c"), None);

        let rule: Rule = "foo.o: foo.c\n".parse().unwrap();
        assert_eq!(rule.stem("foo.o"), None);

        let rule: Rule = "a.o b.o: %.o: %.c\n".parse().unwrap();
        assert_eq!(rule.stem("a.o"), None);

        let rule: Rule = "%.o: %.c\n".parse().unwrap();
        assert_eq!(rule.stem_for("foo.o", MakefileVariant::BSDMake), None);
        assert_eq!(
            rule.stem_for("foo.o", MakefileVariant::POSIXMake),
            Some("foo".to_string())
        );
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_simple() {
        let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("foo.o");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "%.o");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_no_match() {
        let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("foo.c");
        assert!(rule.is_none());
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_exact() {
        let makefile: Makefile = "foo.o: foo.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("foo.o");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "foo.o");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_prefix() {
        let makefile: Makefile = "lib%.a: %.o\n\tar rcs $@ $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("libfoo.a");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "lib%.a");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_suffix() {
        let makefile: Makefile = "%_test.o: %.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("foo_test.o");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "%_test.o");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_middle() {
        let makefile: Makefile = "lib%_debug.a: %.o\n\tar rcs $@ $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("libfoo_debug.a");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "lib%_debug.a");
    }

    #[test]
    fn test_makefile_find_rule_by_target_pattern_wildcard_only() {
        let makefile: Makefile = "%: %.c\n\t$(CC) -o $@ $<\n".parse().unwrap();
        let rule = makefile.find_rule_by_target_pattern("anything");
        assert!(rule.is_some());
        assert_eq!(rule.unwrap().targets().next().unwrap(), "%");
    }

    #[test]
    fn test_makefile_find_rules_by_target_pattern_multiple() {
        let makefile: Makefile = "%.o: %.c\n\t$(CC) -c $<\n%.o: %.s\n\t$(AS) -o $@ $<\n"
            .parse()
            .unwrap();
        let rules: Vec<_> = makefile.rules_by_target_pattern("foo.o").collect();
        assert_eq!(rules.len(), 2);
    }

    #[test]
    fn test_makefile_find_rules_by_target_pattern_mixed() {
        let makefile: Makefile =
        "%.o: %.c\n\t$(CC) -c $<\nfoo.o: foo.h\n\t$(CC) -c foo.c\nbar.txt: baz.txt\n\tcp $< $@\n"
            .parse()
            .unwrap();
        let rules: Vec<_> = makefile.rules_by_target_pattern("foo.o").collect();
        assert_eq!(rules.len(), 2); // Matches both %.o and foo.o
        let rules: Vec<_> = makefile.rules_by_target_pattern("bar.txt").collect();
        assert_eq!(rules.len(), 1); // Only exact match
    }

    #[test]
    fn test_makefile_find_rules_by_target_pattern_no_wildcard() {
        let makefile: Makefile = "foo.o: foo.c\n\t$(CC) -c $<\n".parse().unwrap();
        let rules: Vec<_> = makefile.rules_by_target_pattern("foo.o").collect();
        assert_eq!(rules.len(), 1);
        let rules: Vec<_> = makefile.rules_by_target_pattern("bar.o").collect();
        assert_eq!(rules.len(), 0);
    }

    #[test]
    fn test_rules_by_target_pattern_like_make() {
        let makefile: Makefile = "%.x%:\n\techo\nlib%.a:\n\techo\na\\%b:\n\techo\n$(X:%=y):\n\techo\nfoo.o:\n\techo\nexplicit %.w:\n\techo\n"
            .parse()
            .unwrap();
        let matching = |target| {
            makefile
                .rules_by_target_pattern(target)
                .flat_map(|r| r.targets().collect::<Vec<_>>())
                .collect::<Vec<_>>()
        };
        assert_eq!(matching("a.x%"), vec!["%.x%"]);
        // Without a `/` in the pattern, the directory is left out.
        assert_eq!(matching("dir/libfoo.a"), vec!["lib%.a"]);
        // `\%` is a literal `%`.
        assert_eq!(matching("a\\Xb"), Vec::<String>::new());
        // A `%` inside a variable reference is not the pattern.
        assert_eq!(matching("$(X:abc=y)"), Vec::<String>::new());
        assert_eq!(matching("foo.o"), vec!["foo.o"]);
        // make reads a rule whose first target is explicit as an explicit rule.
        assert_eq!(matching("foo.w"), Vec::<String>::new());
        assert_eq!(matching("%.w"), vec!["explicit", "%.w"]);
    }
}
