//! Finding the default goal of a makefile.

use crate::lossless::{Makefile, Rule, VariableDefinition};
use crate::MakefileVariant;
use rowan::ast::AstNode;

/// A way make may pick the default goal, the target it builds when none is
/// given on the command line; see [`Makefile::default_goal_candidates`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DefaultGoal {
    /// `target`, the first target of `rule` that can be the default goal.
    FirstTarget {
        /// The rule.
        rule: Rule,
        /// The target, as written.
        target: String,
    },
    /// GNU make's `.DEFAULT_GOAL`, as set by `definition`.
    Variable {
        /// The assignment.
        definition: VariableDefinition,
        /// The assigned value, unexpanded. For `!=` this is the shell
        /// command and for `+=` the appended words.
        value: String,
    },
    /// BSD make's `.MAIN` rule, whose sources make builds instead.
    Main {
        /// The `.MAIN` rule.
        rule: Rule,
        /// Its sources, unexpanded.
        targets: Vec<String>,
    },
}

impl DefaultGoal {
    /// The names of the targets this builds, unexpanded.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Makefile, MakefileVariant};
    /// let makefile: Makefile = ".DEFAULT_GOAL := all\nclean:\n".parse().unwrap();
    /// let goals = makefile.default_goal_candidates(MakefileVariant::GNUMake);
    /// assert_eq!(goals[0].names(), vec!["all".to_string()]);
    /// ```
    pub fn names(&self) -> Vec<String> {
        match self {
            Self::FirstTarget { target, .. } => vec![target.clone()],
            Self::Variable { value, .. } => value.split_whitespace().map(str::to_string).collect(),
            Self::Main { targets, .. } => targets.clone(),
        }
    }

    fn start(&self) -> rowan::TextSize {
        match self {
            Self::FirstTarget { rule, .. } | Self::Main { rule, .. } => {
                rule.syntax().text_range().start()
            }
            Self::Variable { definition, .. } => definition.syntax().text_range().start(),
        }
    }
}

/// The value of GNU make's `.DEFAULT_GOAL`, or for other variants whether a
/// rule has set the default goal yet.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Slot {
    /// Removed with `undefine`; rules no longer set it.
    Undefined,
    Empty,
    Set(DefaultGoal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct State {
    goal: Slot,
    /// The first `.MAIN` rule with sources, for BSD make.
    main: Option<DefaultGoal>,
}

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

/// Whether `name` looks like a suffix transformation rule, such as `.c.o`
/// or `.c`.
fn is_transformation(name: &str) -> bool {
    let Some(suffixes) = name.strip_prefix('.') else {
        return false;
    };
    !name.contains('/') && {
        let parts: Vec<&str> = suffixes.split('.').collect();
        parts.len() <= 2 && parts.iter().all(|p| !p.is_empty())
    }
}

/// The target of `rule` that becomes the default goal if none is set yet.
fn first_target(rule: &Rule, variant: MakefileVariant) -> Option<String> {
    let mut targets = rule.targets_for(variant);
    match variant {
        MakefileVariant::BSDMake => {
            let targets: Vec<String> = targets.collect();
            let first = targets.first()?;
            if BSD_SPECIAL_TARGETS.contains(&first.as_str()) || first.starts_with(".PATH.") {
                return None;
            }
            if rule
                .prerequisites_for(variant)
                .any(|p| matches!(p.as_str(), ".NOTMAIN" | ".USE" | ".EXEC"))
            {
                return None;
            }
            targets
                .into_iter()
                .find(|t| t != ".WAIT" && !is_transformation(t))
        }
        // TODO: check the nmake rules against nmake itself. These are GNU
        // make's, also skipping `{dir}.c{dir}.obj` inference rules.
        _ => {
            if rule.scoped_assignment().is_some() {
                return None;
            }
            targets.find(|t| {
                !t.contains('%')
                    && (!t.starts_with('.') || t.contains('/'))
                    && !(variant == MakefileVariant::NMake && t.starts_with('{'))
            })
        }
    }
}

fn apply_rule(rule: &Rule, states: &mut [State], variant: MakefileVariant) {
    if variant == MakefileVariant::BSDMake
        && rule.targets_for(variant).next().as_deref() == Some(".MAIN")
    {
        let targets: Vec<String> = rule.prerequisites_for(variant).collect();
        if !targets.is_empty() {
            let main = DefaultGoal::Main {
                rule: rule.clone(),
                targets,
            };
            for state in states.iter_mut().filter(|s| s.main.is_none()) {
                state.main = Some(main.clone());
            }
        }
        return;
    }
    let Some(target) = first_target(rule, variant) else {
        return;
    };
    let goal = DefaultGoal::FirstTarget {
        rule: rule.clone(),
        target,
    };
    for state in states.iter_mut().filter(|s| s.goal == Slot::Empty) {
        state.goal = Slot::Set(goal.clone());
    }
}

fn apply_default_goal_assignment(definition: &VariableDefinition, states: &mut [State]) {
    use crate::AssignmentOperator::*;
    if definition.is_undefine() {
        for state in states.iter_mut() {
            state.goal = Slot::Undefined;
        }
        return;
    }
    let value = definition
        .value_for(MakefileVariant::GNUMake)
        .unwrap_or_default();
    let new = if value.trim().is_empty() {
        Slot::Empty
    } else {
        Slot::Set(DefaultGoal::Variable {
            definition: definition.clone(),
            value,
        })
    };
    for state in states.iter_mut() {
        match definition.assignment_operator_kind() {
            // GNU make defines `.DEFAULT_GOAL` as empty to start with, so
            // this only has an effect after `undefine`.
            Some(IfUndefined) => {
                if state.goal == Slot::Undefined {
                    state.goal = new.clone();
                }
            }
            Some(Append) => {
                if new != Slot::Empty {
                    state.goal = new.clone();
                }
            }
            _ => state.goal = new.clone(),
        }
    }
}

fn push_unique(states: &mut Vec<State>, new: impl IntoIterator<Item = State>) {
    for state in new {
        if !states.contains(&state) {
            states.push(state);
        }
    }
}

fn walk(
    items: &mut dyn Iterator<Item = crate::MakefileItem>,
    mut states: Vec<State>,
    variant: MakefileVariant,
) -> Vec<State> {
    use crate::MakefileItem;
    for item in items {
        states = match item {
            MakefileItem::Rule(rule) => {
                apply_rule(&rule, &mut states, variant);
                // A rule's body can contain conditionals with further rules;
                // its direct variable child is a target-specific assignment.
                let mut nested = rule
                    .syntax()
                    .children()
                    .filter_map(MakefileItem::cast)
                    .filter(|i| !matches!(i, MakefileItem::Variable(_)));
                walk(&mut nested, states, variant)
            }
            MakefileItem::Variable(var)
                if variant == MakefileVariant::GNUMake
                    && var.name().as_deref() == Some(".DEFAULT_GOAL") =>
            {
                apply_default_goal_assignment(&var, &mut states);
                states
            }
            MakefileItem::Conditional(cond) => {
                let mut out = Vec::new();
                let mut exhaustive = false;
                for branch in cond.branches() {
                    exhaustive = branch.branch_kind() == Some(crate::BranchKind::Else);
                    let mut items = branch.items().filter_map(|i| match i {
                        crate::ConditionalItem::Item(item) => Some(item),
                        _ => None,
                    });
                    push_unique(&mut out, walk(&mut items, states.clone(), variant));
                }
                if !exhaustive {
                    push_unique(&mut out, states);
                }
                out
            }
            // The body of a `.for` loop runs once per word, which may be
            // none; after the first iteration the goal is set.
            MakefileItem::ForLoop(for_loop) => {
                let mut out = walk(&mut for_loop.items(), states.clone(), variant);
                push_unique(&mut out, states);
                out
            }
            _ => states,
        };
    }
    states
}

impl Makefile {
    /// The ways the default goal may be chosen if make reads this makefile
    /// first, in source order.
    ///
    /// Each item is one possible outcome; there is more than one when
    /// conditionals decide which rules or assignments make reads. An empty
    /// list means make reads no rule that can be the default goal.
    ///
    /// For GNU make, the default goal is the first target of the first rule
    /// that has one that is not a pattern and does not start with `.`
    /// unless it contains a `/`; `.PHONY .x all:` gives `all`. Lines with a
    /// target-specific variable assignment are not rules. A non-empty
    /// `.DEFAULT_GOAL` overrides that wherever it is set, and setting it to
    /// the empty value makes the next rule set it again.
    ///
    /// For BSD make, the default goal is the first target of the first rule
    /// that does not start with a special target such as `.SUFFIXES`, has
    /// none of the sources `.NOTMAIN`, `.USE` or `.EXEC` and is not a
    /// transformation rule. Since the known suffixes are not tracked, any
    /// target of the form `.a` or `.a.b` is taken to be a transformation
    /// rule. The sources of the first `.MAIN` rule override it.
    ///
    /// POSIX make and nmake are handled like GNU make without
    /// `.DEFAULT_GOAL`.
    ///
    /// Names are not expanded, so a target may be a reference expanding to
    /// nothing, and GNU make removes a leading `./`. Rules in other files
    /// that are read with `include` before the first rule and rules created
    /// with `$(eval)` are not taken into account.
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{DefaultGoal, Makefile, MakefileVariant};
    /// let makefile: Makefile = ".PHONY: all\nifdef X\nx:\nendif\nall: x\n".parse().unwrap();
    /// let names: Vec<_> = makefile
    ///     .default_goal_candidates(MakefileVariant::GNUMake)
    ///     .iter()
    ///     .flat_map(DefaultGoal::names)
    ///     .collect();
    /// assert_eq!(names, vec!["x", "all"]);
    /// ```
    pub fn default_goal_candidates(&self, variant: MakefileVariant) -> Vec<DefaultGoal> {
        let start = State {
            goal: Slot::Empty,
            main: None,
        };
        let mut goals: Vec<DefaultGoal> = Vec::new();
        for state in walk(&mut self.items(), vec![start], variant) {
            let goal = match (state.main, state.goal) {
                (Some(main), _) => main,
                (None, Slot::Set(goal)) => goal,
                (None, _) => continue,
            };
            if !goals.contains(&goal) {
                goals.push(goal);
            }
        }
        goals.sort_by_key(DefaultGoal::start);
        goals
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The candidates of `text`, checked against GNU make 4.4.1 and bmake
    /// 20200710.
    fn goals(text: &str, variant: MakefileVariant) -> Vec<String> {
        let parsed = Makefile::parse_with_variant(text, variant);
        assert_eq!(parsed.errors(), &[]);
        parsed
            .tree()
            .default_goal_candidates(variant)
            .iter()
            .map(|goal| match goal {
                DefaultGoal::FirstTarget { target, .. } => target.clone(),
                DefaultGoal::Variable { value, .. } => format!(".DEFAULT_GOAL={}", value),
                DefaultGoal::Main { targets, .. } => format!(".MAIN:{}", targets.join(",")),
            })
            .collect()
    }

    fn gnu(text: &str) -> Vec<String> {
        goals(text, MakefileVariant::GNUMake)
    }

    fn bsd(text: &str) -> Vec<String> {
        goals(text, MakefileVariant::BSDMake)
    }

    #[test]
    fn test_first_target() {
        assert_eq!(gnu("a b:\nc:\n"), vec!["a"]);
        assert_eq!(bsd("a b:\nc:\n"), vec!["a"]);
        assert_eq!(gnu(""), Vec::<String>::new());
        assert_eq!(gnu("X = 1\n"), Vec::<String>::new());
    }

    #[test]
    fn test_dot_targets_gnu() {
        assert_eq!(gnu(".foo bar:\nc:\n"), vec!["bar"]);
        assert_eq!(gnu(".foo:\nc:\n"), vec!["c"]);
        assert_eq!(gnu(".PHONY: c\n.SUFFIXES:\nc:\n"), vec!["c"]);
        assert_eq!(gnu(".c.o:\nc:\n"), vec!["c"]);
        assert_eq!(gnu(".:\n..:\nc:\n"), vec!["c"]);
        assert_eq!(gnu(".foo/bar:\nc:\n"), vec![".foo/bar"]);
        assert_eq!(gnu(".x/.y:\nc:\n"), vec![".x/.y"]);
        assert_eq!(gnu("../x:\nc:\n"), vec!["../x"]);
        assert_eq!(gnu(".x ./y:\n"), vec!["./y"]);
    }

    #[test]
    fn test_dot_targets_bsd() {
        assert_eq!(bsd(".foo/bar:\nc:\n"), vec![".foo/bar"]);
        assert_eq!(bsd(".PHONY: c\n.SUFFIXES:\nc:\n"), vec!["c"]);
        assert_eq!(bsd(".PATH.c: /tmp\nc:\n"), vec!["c"]);
        assert_eq!(bsd(".BEGIN c:\nd:\n"), vec!["d"]);
        assert_eq!(bsd("c .PHONY:\nd:\n"), vec!["c"]);
        assert_eq!(bsd(".c.o bar:\nc:\n"), vec!["bar"]);
        assert_eq!(bsd(".c bar:\nc:\n"), vec!["bar"]);
        assert_eq!(bsd(".:\nc:\n"), vec!["."]);
        assert_eq!(bsd("a .WAIT b:\nc:\n"), vec!["a"]);
        assert_eq!(bsd("./foo:\nc:\n"), vec!["./foo"]);
    }

    #[test]
    fn test_unknown_suffix_bsd() {
        // TODO: bmake only treats `.x` as a transformation rule if `.x` is
        // a known suffix, so its goal here is `.x`.
        assert_eq!(bsd(".x bar:\nc:\n"), vec!["bar"]);
    }

    #[test]
    fn test_bsd_attributes() {
        assert_eq!(bsd("a: .NOTMAIN\nc:\n"), vec!["c"]);
        assert_eq!(bsd("a: .USE\nc:\n"), vec!["c"]);
        assert_eq!(bsd("a: .EXEC\nc:\n"), vec!["c"]);
        assert_eq!(bsd("a: .PHONY\nc:\n"), vec!["a"]);
        assert_eq!(bsd("a: .OPTIONAL\nc:\n"), vec!["a"]);
        assert_eq!(bsd("a: .USEBEFORE\nc:\n"), vec!["a"]);
    }

    #[test]
    fn test_patterns() {
        assert_eq!(gnu("%.o: %.c\nc:\n"), vec!["c"]);
        assert_eq!(gnu("a%:\nc:\n"), vec!["c"]);
        assert_eq!(bsd("a%:\nc:\n"), vec!["a%"]);
        assert_eq!(gnu("a.o b.o: %.o: %.c\nc:\n"), vec!["a.o"]);
    }

    #[test]
    fn test_rule_kinds() {
        assert_eq!(gnu("a::\nc:\n"), vec!["a"]);
        assert_eq!(gnu("a b &:\nc:\n"), vec!["a"]);
        assert_eq!(gnu("a: | b\nb:\n"), vec!["a"]);
        assert_eq!(gnu("$(T):\nc:\n"), vec!["$(T)"]);
        assert_eq!(gnu("*.zz:\nc:\n"), vec!["*.zz"]);
    }

    #[test]
    fn test_target_specific_variable() {
        assert_eq!(gnu("a: X=1\nc:\n"), vec!["c"]);
        assert_eq!(gnu("%.o: X=1\nc:\n"), vec!["c"]);
        assert_eq!(gnu("a: .DEFAULT_GOAL := c\na:\nc:\n"), vec!["a"]);
        // bmake 20200710 reads `X=1` as a source.
        assert_eq!(bsd("a: X=1\nc:\n"), vec!["a"]);
    }

    #[test]
    fn test_conditional() {
        assert_eq!(gnu("ifdef X\na:\nelse\nb:\nendif\nc:\n"), vec!["a", "b"]);
        assert_eq!(gnu("ifdef X\na:\nendif\nc:\n"), vec!["a", "c"]);
        assert_eq!(
            gnu("ifeq (a,b)\na:\nelse ifdef X\nb:\nendif\nc:\n"),
            vec!["a", "b", "c"]
        );
        assert_eq!(gnu("ifdef X\nX = 1\nendif\nc:\nd:\n"), vec!["c"]);
        assert_eq!(gnu("c:\nifdef X\na:\nendif\n"), vec!["c"]);
        assert_eq!(
            bsd(".if defined(X)\na:\n.else\nb:\n.endif\nc:\n"),
            vec!["a", "b"]
        );
        assert_eq!(bsd(".if defined(X)\na:\n.endif\nc:\n"), vec!["a", "c"]);
    }

    #[test]
    fn test_conditional_in_rule_body() {
        assert_eq!(
            gnu("ifdef X\nc:\nifdef Y\nd:\nendif\nendif\ne:\n"),
            vec!["c", "e"]
        );
    }

    #[test]
    fn test_for_loop() {
        assert_eq!(
            bsd(".for i in p q\n${i}:\n.endfor\nc:\n"),
            vec!["${i}", "c"]
        );
    }

    #[test]
    fn test_define() {
        assert_eq!(gnu("define R\nz:\n\techo\nendef\na:\n"), vec!["a"]);
    }

    #[test]
    fn test_default_goal_variable() {
        assert_eq!(gnu(".DEFAULT_GOAL := c\na:\nc:\n"), vec![".DEFAULT_GOAL=c"]);
        assert_eq!(gnu("a:\nc:\n.DEFAULT_GOAL := c\n"), vec![".DEFAULT_GOAL=c"]);
        assert_eq!(
            gnu("G = c\n.DEFAULT_GOAL = $(G)\na:\n"),
            vec![".DEFAULT_GOAL=$(G)"]
        );
        assert_eq!(
            gnu("override .DEFAULT_GOAL := c\na:\n"),
            vec![".DEFAULT_GOAL=c"]
        );
        assert_eq!(
            gnu("export .DEFAULT_GOAL := c\na:\n"),
            vec![".DEFAULT_GOAL=c"]
        );
        assert_eq!(
            gnu("define .DEFAULT_GOAL\nc\nendef\na:\n"),
            vec![".DEFAULT_GOAL=c"]
        );
        assert_eq!(
            gnu(".DEFAULT_GOAL != echo c\na:\n"),
            vec![".DEFAULT_GOAL=echo c"]
        );
        assert_eq!(gnu(".DEFAULT_GOAL += c\na:\n"), vec![".DEFAULT_GOAL=c"]);
        // It is defined as empty to start with.
        assert_eq!(gnu(".DEFAULT_GOAL ?= c\na:\n"), vec!["a"]);
        assert_eq!(gnu("a:\n.DEFAULT_GOAL ?= c\nc:\n"), vec!["a"]);
        // Other variants don't have it.
        assert_eq!(bsd(".DEFAULT_GOAL := c\na:\nc:\n"), vec!["a"]);
        assert_eq!(
            goals(".DEFAULT_GOAL := c\na:\n", MakefileVariant::POSIXMake),
            vec!["a"]
        );
    }

    #[test]
    fn test_default_goal_cleared() {
        assert_eq!(
            gnu(".DEFAULT_GOAL := c\n.DEFAULT_GOAL :=\na:\nc:\n"),
            vec!["a"]
        );
        assert_eq!(gnu("a:\n.DEFAULT_GOAL :=\nc:\n"), vec!["c"]);
        assert_eq!(gnu("a:\n.DEFAULT_GOAL :=\n"), Vec::<String>::new());
    }

    #[test]
    fn test_default_goal_conditional() {
        assert_eq!(
            gnu("ifdef X\n.DEFAULT_GOAL := c\nendif\na:\nc:\n"),
            vec![".DEFAULT_GOAL=c", "a"]
        );
        assert_eq!(
            gnu("ifdef X\n.DEFAULT_GOAL := c\nelse\n.DEFAULT_GOAL := d\nendif\na:\n"),
            vec![".DEFAULT_GOAL=c", ".DEFAULT_GOAL=d"]
        );
    }

    #[test]
    fn test_default_goal_undefined() {
        // After `undefine`, rules no longer set it; GNU make 4.4.1 crashes
        // when it is left undefined.
        assert_eq!(
            gnu(".DEFAULT_GOAL := c\nundefine .DEFAULT_GOAL\na:\n"),
            Vec::<String>::new()
        );
        assert_eq!(
            gnu("undefine .DEFAULT_GOAL\n.DEFAULT_GOAL ?= a\nc:\n"),
            vec![".DEFAULT_GOAL=a"]
        );
    }

    #[test]
    fn test_main() {
        assert_eq!(bsd(".MAIN: c\na:\nc:\n"), vec![".MAIN:c"]);
        assert_eq!(bsd("a:\nc:\n.MAIN: c\n"), vec![".MAIN:c"]);
        assert_eq!(bsd(".MAIN: c a\na:\n"), vec![".MAIN:c,a"]);
        assert_eq!(bsd(".MAIN: c\n.MAIN: a\na:\nc:\n"), vec![".MAIN:c"]);
        assert_eq!(bsd(".MAIN:\n.MAIN: c\na:\nc:\n"), vec![".MAIN:c"]);
        assert_eq!(bsd(".MAIN:\na:\nc:\n"), vec!["a"]);
        assert_eq!(bsd(".MAIN: ${X}\na:\n"), vec![".MAIN:${X}"]);
        assert_eq!(
            bsd(".if defined(X)\n.MAIN: c\n.endif\na:\nc:\n"),
            vec![".MAIN:c", "a"]
        );
        // GNU make has no `.MAIN`.
        assert_eq!(gnu(".MAIN: c\na:\nc:\n"), vec!["a"]);
    }
}
