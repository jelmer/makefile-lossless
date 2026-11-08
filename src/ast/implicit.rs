//! Implicit rule search.

use crate::lossless::{Makefile, Rule};
use crate::pattern::{pattern_match, split_pattern, substitute_stem, PatternMatch};
use crate::MakefileVariant;
use std::collections::HashSet;

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
    /// The pattern rule, or the suffix rule such as `.c.o:`.
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

impl Makefile {
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
    /// in the makefile.
    ///
    /// Only the rules in this makefile are used, not make's built-in rules,
    /// as with `make -r`; but the known suffixes include make's default
    /// ones, as [`Self::suffixes`] says. Names are not expanded, so a
    /// pattern rule with a variable reference in a target or prerequisite
    /// is not used. Rules in every branch of a conditional are read, and
    /// `vpath`, `.SECONDEXPANSION` and `.DEFAULT` are not taken into
    /// account.
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
    // TODO: use the .DEFAULT rule when no implicit rule is found.
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
            let is_static = rule.static_pattern_for(variant).is_some();
            // TODO: count the prerequisites of static pattern rules as
            // mentioned, with the stem of each target substituted.
            let prerequisites: Vec<String> = if is_static {
                vec![]
            } else {
                rule.prerequisites_for(variant)
                    .chain(rule.order_only_prerequisites_for(variant))
                    .collect()
            };
            if rule_targets.iter().any(|t| t == target) {
                if has_recipe(&rule) {
                    return None;
                }
                explicit.extend(prerequisites.iter().cloned());
            }
            mentioned.extend(prerequisites);
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
        search.search(target, 0, &explicit, false)
    }
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
    fn test_suffix_rule_with_prerequisites() {
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
}
