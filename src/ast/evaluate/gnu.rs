//! Expansion as GNU make does it, following its `expand.c` and `read.c`.
//! POSIX make is read with this too, without GNU make's functions.

use super::{Environment, Expansion, ExpansionPart, UnknownReason};
use crate::lossless::{Conditional, Makefile, VariableDefinition, VariableReference};
use crate::pattern::find_percent;
use crate::{
    AssignmentOperator, ConditionalBranch, ConditionalItem, FunctionCall, MakefileItem,
    MakefileVariant, ReferenceLocation, TextSize,
};
use rowan::ast::AstNode;
use std::collections::{HashMap, HashSet};

/// The names of the variables GNU make defines itself, as `make -p -f
/// /dev/null` lists them, apart from the automatic ones.
const BUILTIN_VARIABLES: &[&str] = &[
    "AR",
    "ARFLAGS",
    "AS",
    "CC",
    "CHECKOUT,v",
    "CO",
    "COFLAGS",
    "COMPILE.c",
    "COMPILE.C",
    "COMPILE.cc",
    "COMPILE.cpp",
    "COMPILE.def",
    "COMPILE.f",
    "COMPILE.F",
    "COMPILE.m",
    "COMPILE.mod",
    "COMPILE.p",
    "COMPILE.r",
    "COMPILE.s",
    "COMPILE.S",
    "CPP",
    "CTANGLE",
    "CURDIR",
    "CWEAVE",
    "CXX",
    ".DEFAULT_GOAL",
    "F77",
    "F77FLAGS",
    "FC",
    ".FEATURES",
    "GET",
    "GNUMAKEFLAGS",
    ".INCLUDE_DIRS",
    "LD",
    "LEX",
    "LEX.l",
    "LEX.m",
    ".LIBPATTERNS",
    "LINK.c",
    "LINK.C",
    "LINK.cc",
    "LINK.cpp",
    "LINK.f",
    "LINK.F",
    "LINK.m",
    "LINK.o",
    "LINK.p",
    "LINK.r",
    "LINK.s",
    "LINK.S",
    "LINT",
    "LINT.c",
    ".LOADED",
    "M2C",
    "MAKE",
    "MAKECMDGOALS",
    "MAKE_COMMAND",
    "MAKEFILE_LIST",
    "MAKEFILES",
    "MAKEFLAGS",
    "MAKE_HOST",
    "MAKEINFO",
    "MAKELEVEL",
    "MAKE_VERSION",
    "MFLAGS",
    "OBJC",
    "OUTPUT_OPTION",
    "PC",
    "PREPROCESS.F",
    "PREPROCESS.r",
    "PREPROCESS.S",
    ".RECIPEPREFIX",
    "RM",
    "SHELL",
    ".SHELLFLAGS",
    ".SHELLSTATUS",
    "SUFFIXES",
    "TANGLE",
    "TEX",
    "TEXI2DVI",
    ".VARIABLES",
    "WEAVE",
    "YACC",
    "YACC.m",
    "YACC.y",
];

/// Whether `b` is a space as C's `isspace` takes it, as GNU make splits
/// words.
fn is_space(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

/// The byte ranges of the words of `text`.
fn word_ranges(text: &str) -> Vec<(usize, usize)> {
    let bytes = text.as_bytes();
    let mut words = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        while i < bytes.len() && is_space(bytes[i]) {
            i += 1;
        }
        let start = i;
        while i < bytes.len() && !is_space(bytes[i]) {
            i += 1;
        }
        if i > start {
            words.push((start, i));
        }
    }
    words
}

fn words(text: &str) -> impl Iterator<Item = &str> {
    word_ranges(text).into_iter().map(move |(s, e)| &text[s..e])
}

fn strip(text: &str) -> &str {
    text.trim_matches(|c: char| c.is_ascii() && is_space(c as u8))
}

/// Whether `word` matches `pattern`, which has a `%` at `percent`.
fn matches_percent(pattern: &str, percent: usize, word: &str) -> bool {
    let (prefix, suffix) = (&pattern[..percent], &pattern[percent + 1..]);
    word.len() >= prefix.len() + suffix.len() && word.starts_with(prefix) && word.ends_with(suffix)
}

/// GNU make's `subst_expand`: replace `from` with `to` in `text`, with
/// `by_word` only where `from` is a whole word.
fn subst_expand(text: &str, from: &str, to: &str, by_word: bool) -> String {
    if from.is_empty() && !by_word {
        return format!("{text}{to}");
    }
    let bytes = text.as_bytes();
    let mut out = String::new();
    let mut t = 0;
    loop {
        let p = if by_word && from.is_empty() {
            let mut p = t;
            while p < bytes.len() && is_space(bytes[p]) {
                p += 1;
            }
            while p < bytes.len() && !is_space(bytes[p]) {
                p += 1;
            }
            p
        } else {
            match text[t..].find(from) {
                Some(i) => t + i,
                None => {
                    out.push_str(&text[t..]);
                    return out;
                }
            }
        };
        out.push_str(&text[t..p]);
        let after = p + from.len();
        let struck = by_word
            && ((p > 0 && !is_space(bytes[p - 1]))
                || (after < bytes.len() && !is_space(bytes[after])));
        out.push_str(if struck { from } else { to });
        t = after;
        if t >= bytes.len() {
            return out;
        }
    }
}

/// GNU make's `patsubst`.
fn patsubst(text: &str, pattern: &str, replacement: &str) -> String {
    let (pattern, pattern_percent) = find_percent(pattern);
    let (replacement, replacement_percent) = find_percent(replacement);
    let Some(percent) = pattern_percent else {
        return subst_expand(text, &pattern, &replacement, true);
    };
    let (prefix, suffix) = (&pattern[..percent], &pattern[percent + 1..]);
    let (before, after) = match replacement_percent {
        Some(p) => (&replacement[..p], Some(&replacement[p + 1..])),
        None => (replacement.as_str(), None),
    };
    let mut out = String::new();
    let mut any = false;
    for word in words(text) {
        let matched = matches_percent(&pattern, percent, word);
        if matched {
            out.push_str(before);
            if let Some(after) = after {
                out.push_str(&word[prefix.len()..word.len() - suffix.len()]);
                out.push_str(after);
            }
        } else {
            out.push_str(word);
        }
        if !matched || !before.is_empty() || after.is_some() {
            out.push(' ');
            any = true;
        }
    }
    if any {
        out.pop();
    }
    out
}

/// The substitution reference `$(VAR:pattern=replacement)` applied to
/// `value`: a pattern without `%` matches at the end of each word.
fn substitution_reference(value: &str, pattern: &str, replacement: &str) -> String {
    let (unescaped, percent) = find_percent(pattern);
    if percent.is_some() {
        patsubst(value, pattern, replacement)
    } else {
        patsubst(value, &format!("%{unescaped}"), &format!("%{replacement}"))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Origin {
    Environment,
    File,
    Override,
}

#[derive(Debug, Clone)]
struct Var {
    recursive: bool,
    /// The value as stored: for a recursively expanded variable, the known
    /// parts are still to be expanded.
    value: Expansion,
    origin: Origin,
}

#[derive(Debug, Clone)]
enum Binding {
    Set(Var),
    Undefined,
    Unknown(UnknownReason),
}

/// The variables as make knows them at some point while reading the
/// makefile.
#[derive(Debug, Clone, Default)]
struct State {
    vars: HashMap<String, Binding>,
    /// Why the variables not in `vars` are unknown, after an `include` or
    /// similar.
    others_unknown: Option<UnknownReason>,
    /// The names of variables with target-specific or pattern-specific
    /// values.
    target_specific: HashSet<String>,
    /// Whether a target-specific assignment to a variable whose name is
    /// not known was seen.
    target_specific_unknown: bool,
}

impl State {
    fn new(env: &Environment) -> Self {
        let mut state = Self::default();
        if let Environment::Known(vars) = env {
            for (name, value) in vars {
                state.vars.insert(
                    name.clone(),
                    Binding::Set(Var {
                        recursive: true,
                        value: Expansion::known(value),
                        origin: Origin::Environment,
                    }),
                );
            }
        }
        state
    }

    /// What `name` is if the makefile has not set it.
    fn absent(&self, name: &str, env: &Environment, deferred: bool) -> Binding {
        if let Some(reason) = &self.others_unknown {
            return Binding::Unknown(reason.clone());
        }
        if crate::lossless::is_automatic_name(name, MakefileVariant::GNUMake) {
            return if deferred {
                Binding::Unknown(UnknownReason::AutomaticVariable(name.to_string()))
            } else {
                Binding::Undefined
            };
        }
        match env {
            Environment::Unknown => {
                Binding::Unknown(UnknownReason::UndefinedVariable(name.to_string()))
            }
            Environment::Known(_) if BUILTIN_VARIABLES.contains(&name) => {
                Binding::Unknown(UnknownReason::BuiltinVariable(name.to_string()))
            }
            Environment::Known(_) => Binding::Undefined,
        }
    }

    fn binding(&self, name: &str, env: &Environment, deferred: bool) -> Binding {
        match self.vars.get(name) {
            Some(binding) => binding.clone(),
            None => self.absent(name, env, deferred),
        }
    }

    /// Make every variable unknown, as after an `include`.
    fn forget_all(&mut self, reason: UnknownReason) {
        for binding in self.vars.values_mut() {
            if !matches!(binding, Binding::Unknown(_)) {
                *binding = Binding::Unknown(reason.clone());
            }
        }
        self.others_unknown.get_or_insert(reason);
    }
}

/// The deepest nesting of variable expansions and function calls to follow.
const MAX_DEPTH: usize = 64;

/// Expands text with the variables of a [`State`], as GNU make's
/// `expand_string_buf` does.
struct Expander<'a> {
    state: &'a State,
    env: &'a Environment,
    variant: MakefileVariant,
    /// Whether this is a recipe or a recursively expanded value used later,
    /// where automatic variables are set.
    deferred: bool,
    /// Whether target-specific values may apply.
    target_context: bool,
    /// The recursively expanded variables being expanded.
    expanding: Vec<String>,
    depth: usize,
    /// Whether `eval` would be called.
    saw_eval: bool,
}

impl<'a> Expander<'a> {
    fn new(state: &'a State, env: &'a Environment, variant: MakefileVariant) -> Self {
        Self {
            state,
            env,
            variant,
            deferred: false,
            target_context: false,
            expanding: Vec::new(),
            depth: 0,
            saw_eval: false,
        }
    }

    fn binding(&self, name: &str) -> Binding {
        if self.target_context
            && (self.state.target_specific_unknown || self.state.target_specific.contains(name))
        {
            return Binding::Unknown(UnknownReason::TargetSpecificVariable(name.to_string()));
        }
        self.state.binding(name, self.env, self.deferred)
    }

    fn expand(&mut self, text: &str) -> Expansion {
        let mut out = Expansion::default();
        let mut i = 0;
        while let Some(offset) = text[i..].find('$') {
            let dollar = i + offset;
            out.push_str(&text[i..dollar]);
            let Some(c) = text[dollar + 1..].chars().next() else {
                out.push_str("$");
                return out;
            };
            i = match c {
                '$' => {
                    out.push_str("$");
                    dollar + 2
                }
                '(' | '{' => self.expand_parenthesised(text, dollar, &mut out),
                c => {
                    let end = dollar + 1 + c.len_utf8();
                    let value = self.value_of(&text[dollar + 1..end], &text[dollar..end]);
                    out.extend(value);
                    end
                }
            };
        }
        out.push_str(&text[i..]);
        out
    }

    /// Expand the reference or function call `$(...)` or `${...}` at
    /// `dollar` in `text`, returning the position after it.
    fn expand_parenthesised(&mut self, text: &str, dollar: usize, out: &mut Expansion) -> usize {
        let rest = &text[dollar..];
        if self.variant == MakefileVariant::GNUMake {
            match FunctionCall::parse_prefix(rest) {
                Ok(Some((call, len))) => {
                    out.extend(self.function(&rest[..len], &call));
                    return dollar + len;
                }
                Ok(None) => {}
                Err(_) => {
                    let name = rest[2..].split([' ', '\t']).next().unwrap_or_default();
                    let close = if rest.starts_with("${") { '}' } else { ')' };
                    out.push_unknown(
                        rest,
                        UnknownReason::Error(format!(
                            "unterminated call to function '{name}': missing '{close}'"
                        )),
                    );
                    return text.len();
                }
            }
        }
        let (open, close) = if rest.starts_with("$(") {
            ('(', ')')
        } else {
            ('{', '}')
        };
        let begin = dollar + 2;
        let Some(first_close) = text[begin..].find(close).map(|i| begin + i) else {
            out.push_unknown(
                rest,
                UnknownReason::Error("unterminated variable reference".to_string()),
            );
            return text.len();
        };
        let mut end = first_close;
        let mut name = Expansion::known(&text[begin..first_close]);
        if text[begin..first_close].contains('$') {
            if let Some(matched) = matching_close(text, begin, open, close) {
                end = matched;
                name = self.expand(&text[begin..end]);
            }
        }
        let reference = &text[dollar..=end];
        let Some(name) = name.text() else {
            let reason = name.unknown_reason().cloned().expect("an unknown part");
            out.push_unknown(reference, reason);
            return end + 1;
        };
        let substitution = name
            .find(':')
            .and_then(|colon| Some((colon, colon + 1 + name[colon + 1..].find('=')?)));
        let value = match substitution {
            Some((colon, equals)) => self.substitute(
                &name[..colon],
                &name[colon + 1..equals],
                &name[equals + 1..],
                reference,
            ),
            None => self.value_of(&name, reference),
        };
        out.extend(value);
        end + 1
    }

    /// The value of the variable `name`, referenced as `reference`.
    fn value_of(&mut self, name: &str, reference: &str) -> Expansion {
        let var = match self.binding(name) {
            Binding::Set(var) => var,
            Binding::Undefined => return Expansion::default(),
            Binding::Unknown(reason) => return Expansion::unknown(reference, reason),
        };
        if !var.recursive {
            return var.value;
        }
        if self.expanding.iter().any(|n| n == name) {
            return Expansion::unknown(reference, UnknownReason::Recursion(name.to_string()));
        }
        if self.depth >= MAX_DEPTH {
            return Expansion::unknown(reference, UnknownReason::DepthLimit);
        }
        self.expanding.push(name.to_string());
        self.depth += 1;
        let value = self.expand_value(&var.value);
        self.depth -= 1;
        self.expanding.pop();
        match value.fatal_reason() {
            Some(reason) => Expansion::unknown(reference, reason.clone()),
            None => value,
        }
    }

    /// Expand the stored value of a recursively expanded variable.
    fn expand_value(&mut self, value: &Expansion) -> Expansion {
        let mut out = Expansion::default();
        for part in &value.parts {
            match part {
                ExpansionPart::Known(text) => out.extend(self.expand(text)),
                part => out.parts.push(part.clone()),
            }
        }
        out
    }

    /// The substitution reference `$(name:pattern=replacement)`.
    fn substitute(
        &mut self,
        name: &str,
        pattern: &str,
        replacement: &str,
        reference: &str,
    ) -> Expansion {
        let value = self.value_of(name, reference);
        match value.text() {
            Some(text) if text.is_empty() => Expansion::default(),
            Some(text) => Expansion::known(&substitution_reference(&text, pattern, replacement)),
            None => {
                let reason = value.unknown_reason().cloned().expect("an unknown part");
                Expansion::unknown(reference, reason)
            }
        }
    }

    /// Evaluate the function call `text`.
    fn function(&mut self, text: &str, call: &FunctionCall) -> Expansion {
        let name = call.name.as_str();
        if contains_eval(text) {
            self.saw_eval = true;
        }
        // TODO: evaluate the text functions, and those that expand their
        // arguments themselves, such as `if` and `foreach`.
        if !matches!(name, "value" | "flavor" | "origin") {
            return Expansion::unknown(text, UnknownReason::UnsupportedFunction(name.to_string()));
        }
        if self.depth >= MAX_DEPTH {
            return Expansion::unknown(text, UnknownReason::DepthLimit);
        }
        self.depth += 1;
        let args: Vec<Expansion> = call
            .arguments
            .iter()
            .map(|range| self.expand(&text[range.clone()]))
            .collect();
        self.depth -= 1;
        if let Some(reason) = args.iter().find_map(Expansion::unknown_reason) {
            return Expansion::unknown(text, reason.clone());
        }
        let args: Vec<String> = args.iter().filter_map(Expansion::text).collect();
        self.known_function(text, name, &args)
    }

    /// Evaluate a function whose arguments are all known.
    fn known_function(&mut self, text: &str, name: &str, args: &[String]) -> Expansion {
        let arg = args.first().map(String::as_str).unwrap_or_default();
        match name {
            "value" => match self.binding(arg) {
                Binding::Set(var) => var.value,
                Binding::Undefined => Expansion::default(),
                Binding::Unknown(reason) => Expansion::unknown(text, reason),
            },
            "flavor" | "origin" => match self.binding(arg) {
                Binding::Set(var) => Expansion::known(if name == "flavor" {
                    if var.recursive {
                        "recursive"
                    } else {
                        "simple"
                    }
                } else {
                    match var.origin {
                        Origin::Environment => "environment",
                        Origin::File => "file",
                        Origin::Override => "override",
                    }
                }),
                Binding::Undefined => Expansion::known("undefined"),
                Binding::Unknown(reason) => Expansion::unknown(text, reason),
            },
            _ => Expansion::unknown(text, UnknownReason::UnsupportedFunction(name.to_string())),
        }
    }
}

/// The position of the `close` that matches the `open` before `begin` in
/// `text`, counting only that kind of parenthesis.
fn matching_close(text: &str, begin: usize, open: char, close: char) -> Option<usize> {
    let mut depth = 1;
    for (i, c) in text[begin..].char_indices() {
        if c == open {
            depth += 1;
        } else if c == close {
            depth -= 1;
            if depth == 0 {
                return Some(begin + i);
            }
        }
    }
    None
}

/// Whether `text` calls `eval` somewhere.
fn contains_eval(text: &str) -> bool {
    ["$(eval", "${eval"].iter().any(|start| {
        text.match_indices(start)
            .any(|(i, _)| text[i + start.len()..].starts_with([' ', '\t']))
    })
}

fn branch_items(branch: &ConditionalBranch) -> impl Iterator<Item = MakefileItem> {
    branch.items().filter_map(|item| match item {
        ConditionalItem::Item(item) => Some(item),
        ConditionalItem::Recipe(_) => None,
    })
}

/// The items in the body of a rule, such as conditionals between its
/// recipe lines, apart from its target-specific assignment.
fn rule_items(rule: &crate::Rule) -> impl Iterator<Item = MakefileItem> {
    rule.syntax()
        .children()
        .filter_map(MakefileItem::cast)
        .filter(|item| !matches!(item, MakefileItem::Variable(_) | MakefileItem::Recipe(_)))
}

/// Whether reading a line that expands to `expansion` may change any
/// variable: make reads it as makefile text unless it is empty. `info` and
/// `warning` expand to nothing.
fn may_set_variables(expansion: &Expansion) -> bool {
    expansion.parts().iter().any(|part| match part {
        ExpansionPart::Known(text) => !text.is_empty(),
        ExpansionPart::Unknown { reason, .. } => !matches!(
            reason,
            UnknownReason::UnsupportedFunction(name) if name == "info" || name == "warning"
        ),
    })
}

/// Reads a makefile as GNU make does, keeping track of the variables.
struct Walker<'a> {
    env: &'a Environment,
    variant: MakefileVariant,
    state: State,
    /// Where to stop reading, if not at the end.
    stop: Option<TextSize>,
    /// Whether the current line calls `eval`.
    pending_eval: bool,
}

impl<'a> Walker<'a> {
    fn run(
        makefile: &Makefile,
        env: &'a Environment,
        variant: MakefileVariant,
        stop: Option<TextSize>,
    ) -> Self {
        let mut walker = Self {
            env,
            variant,
            state: State::new(env),
            stop,
            pending_eval: false,
        };
        walker.walk(makefile.items());
        walker
    }

    /// Expand `text` with the variables as they are now, as make does when
    /// reading a line.
    fn expand_now(&mut self, text: &str) -> Expansion {
        let mut expander = Expander::new(&self.state, self.env, self.variant);
        let expansion = expander.expand(text);
        self.pending_eval |= expander.saw_eval;
        expansion
    }

    /// Read `items`, returning whether reading stopped at `self.stop`.
    fn walk(&mut self, items: impl Iterator<Item = MakefileItem>) -> bool {
        for item in items {
            let range = item.syntax().text_range();
            if let Some(stop) = self.stop {
                if stop <= range.start() {
                    return true;
                }
                if stop < range.end() {
                    match &item {
                        MakefileItem::Conditional(conditional) => {
                            self.conditional(conditional);
                        }
                        MakefileItem::Rule(rule) => {
                            self.walk(rule_items(rule));
                        }
                        _ => {}
                    }
                    return true;
                }
            }
            self.item(&item);
            if std::mem::take(&mut self.pending_eval) {
                self.state.forget_all(UnknownReason::Eval);
            }
        }
        false
    }

    fn item(&mut self, item: &MakefileItem) {
        match item {
            MakefileItem::Variable(definition) => self.assignment(definition),
            MakefileItem::Rule(rule) => {
                if let Some(definition) = rule.scoped_assignment() {
                    self.target_specific(&definition);
                }
                self.walk(rule_items(rule));
            }
            MakefileItem::Include(_) => self.state.forget_all(UnknownReason::Include),
            MakefileItem::Load(_) => self.state.forget_all(UnknownReason::Load),
            MakefileItem::Conditional(conditional) => {
                self.conditional(conditional);
            }
            MakefileItem::ExpressionStatement(statement) => {
                let expansion = self.expand_now(&statement.expression_for(self.variant));
                // TODO: read the expansion as makefile text, rather than
                // forgetting all variables.
                if may_set_variables(&expansion) {
                    self.state.forget_all(UnknownReason::Eval);
                }
            }
            _ => {}
        }
    }

    /// The name `definition` assigns to, `Some(None)` if that is not known.
    fn assigned_name(&mut self, definition: &VariableDefinition) -> Option<Option<String>> {
        let name = definition.name()?;
        if !name.contains('$') {
            return Some(Some(name));
        }
        Some(
            self.expand_now(&name)
                .text()
                .map(|name| strip(&name).to_string()),
        )
    }

    fn target_specific(&mut self, definition: &VariableDefinition) {
        match self.assigned_name(definition) {
            Some(Some(name)) => {
                self.state.target_specific.insert(name);
            }
            Some(None) => self.state.target_specific_unknown = true,
            None => {}
        }
    }

    /// Whether `name` is an override variable that an assignment without
    /// `override` does not change.
    fn is_protected(&self, name: &str, definition: &VariableDefinition) -> bool {
        !definition.is_override()
            && matches!(
                self.state.vars.get(name),
                Some(Binding::Set(Var {
                    origin: Origin::Override,
                    ..
                }))
            )
    }

    fn assignment(&mut self, definition: &VariableDefinition) {
        if definition.is_target_specific() {
            self.target_specific(definition);
            return;
        }
        let name = match self.assigned_name(definition) {
            Some(Some(name)) => name,
            Some(None) => return self.state.forget_all(UnknownReason::UnknownName),
            None => return,
        };
        if self.is_protected(&name, definition) {
            return;
        }
        if definition.is_undefine() {
            self.state.vars.insert(name, Binding::Undefined);
            return;
        }
        let op = match definition.assignment_operator_kind() {
            Some(op) => op,
            None if definition.is_define() => AssignmentOperator::Recursive,
            // An `export` or `unexport` without a value.
            None => return,
        };
        let origin = if definition.is_override() {
            Origin::Override
        } else {
            Origin::File
        };
        let value = definition.value_for(self.variant).unwrap_or_default();
        let recursive = |value: Expansion| {
            Binding::Set(Var {
                recursive: true,
                value,
                origin,
            })
        };
        let binding = match op {
            AssignmentOperator::Recursive => recursive(Expansion::known(&value)),
            AssignmentOperator::Simple | AssignmentOperator::PosixSimple => Binding::Set(Var {
                recursive: false,
                value: self.expand_now(&value),
                origin,
            }),
            AssignmentOperator::Immediate => recursive(self.expand_now(&value).escape_dollars()),
            AssignmentOperator::Append => self.append(&name, &value, origin),
            AssignmentOperator::IfUndefined => match self.state.binding(&name, self.env, false) {
                Binding::Undefined => recursive(Expansion::known(&value)),
                _ => return,
            },
            AssignmentOperator::Shell => {
                self.expand_now(&value);
                Binding::Unknown(UnknownReason::ShellAssignment)
            }
            AssignmentOperator::BsdShell => {
                Binding::Unknown(UnknownReason::UnsupportedVariant(self.variant))
            }
        };
        self.state.vars.insert(name, binding);
    }

    fn append(&mut self, name: &str, value: &str, origin: Origin) -> Binding {
        match self.state.binding(name, self.env, false) {
            Binding::Set(mut var) => {
                let addition = if var.recursive {
                    Expansion::known(value)
                } else {
                    self.expand_now(value)
                };
                var.value.append_word(addition);
                if origin == Origin::Override {
                    var.origin = origin;
                }
                Binding::Set(var)
            }
            // Like `=` for a variable that is not set.
            Binding::Undefined => Binding::Set(Var {
                recursive: true,
                value: Expansion::known(value),
                origin,
            }),
            unknown => unknown,
        }
    }

    /// Read a conditional, returning whether reading stopped in it.
    fn conditional(&mut self, conditional: &Conditional) -> bool {
        // TODO: follow the branches whose condition is known.
        for branch in conditional.branches() {
            if self
                .stop
                .is_some_and(|stop| stop < branch.directive_range().end())
            {
                return true;
            }
            if self
                .stop
                .is_some_and(|stop| stop < branch.text_range().end())
            {
                self.walk(branch_items(&branch));
                return true;
            }
            self.skip(branch_items(&branch));
        }
        false
    }

    /// Note `items`, of a conditional branch that make may or may not read:
    /// the variables they may set become unknown.
    fn skip(&mut self, items: impl Iterator<Item = MakefileItem>) {
        for item in items {
            match &item {
                MakefileItem::Conditional(conditional) => {
                    for branch in conditional.branches() {
                        self.skip(branch_items(&branch));
                    }
                }
                MakefileItem::Rule(rule) => {
                    if let Some(definition) = rule.scoped_assignment() {
                        self.target_specific(&definition);
                    }
                    self.skip(rule_items(rule));
                }
                MakefileItem::Variable(definition) => self.forget_assignment(definition),
                MakefileItem::Include(_) | MakefileItem::Load(_) => {
                    self.state.forget_all(UnknownReason::Conditional)
                }
                MakefileItem::ExpressionStatement(statement) => {
                    let expansion = self.expand_now(&statement.expression_for(self.variant));
                    if may_set_variables(&expansion) || std::mem::take(&mut self.pending_eval) {
                        self.state.forget_all(UnknownReason::Conditional);
                    }
                }
                _ => {}
            }
        }
    }

    /// Forget the value `definition` may set, in a branch make may or may
    /// not read.
    fn forget_assignment(&mut self, definition: &VariableDefinition) {
        if definition.is_target_specific() {
            return self.target_specific(definition);
        }
        let name = match self.assigned_name(definition) {
            Some(Some(name)) => name,
            Some(None) => return self.state.forget_all(UnknownReason::Conditional),
            None => return,
        };
        let sets = definition.is_undefine()
            || definition.is_define()
            || definition.assignment_operator_kind().is_some();
        if sets && !self.is_protected(&name, definition) {
            self.state
                .vars
                .insert(name, Binding::Unknown(UnknownReason::Conditional));
        }
    }
}

/// The variables of a makefile as GNU make reads it.
#[derive(Debug, Clone)]
pub(super) struct Engine {
    makefile: Makefile,
    variant: MakefileVariant,
    env: Environment,
    state: State,
}

impl Engine {
    pub(super) fn new(makefile: &Makefile, variant: MakefileVariant, env: Environment) -> Self {
        let state = Walker::run(makefile, &env, variant, None).state;
        Engine {
            makefile: makefile.clone(),
            variant,
            env,
            state,
        }
    }

    fn expander<'s>(&'s self, state: &'s State) -> Expander<'s> {
        Expander::new(state, &self.env, self.variant)
    }

    pub(super) fn variable(&self, name: &str) -> Option<Expansion> {
        let reference = format!("$({name})");
        match self.state.binding(name, &self.env, true) {
            Binding::Undefined => None,
            Binding::Unknown(reason) => Some(Expansion::unknown(&reference, reason)),
            Binding::Set(_) => {
                let mut expander = self.expander(&self.state);
                expander.deferred = true;
                Some(expander.value_of(name, &reference))
            }
        }
    }

    pub(super) fn expand_at(&self, text: &str, offset: TextSize) -> Expansion {
        let walker = Walker::run(&self.makefile, &self.env, self.variant, Some(offset));
        self.expander(&walker.state).expand(text)
    }

    pub(super) fn expand_reference(&self, reference: &VariableReference) -> Expansion {
        let text = reference.syntax().text().to_string();
        match self.deferred_context(reference) {
            None => self.expand_at(&text, reference.syntax().text_range().start()),
            Some(target_context) => {
                let mut expander = self.expander(&self.state);
                expander.deferred = true;
                expander.target_context = target_context;
                expander.expand(&text)
            }
        }
    }

    /// Whether make expands `reference` after reading the makefile, and if
    /// so whether target-specific values apply there.
    fn deferred_context(&self, reference: &VariableReference) -> Option<bool> {
        match reference.location() {
            ReferenceLocation::FunctionArgument(parent)
            | ReferenceLocation::ReferenceName(parent)
            | ReferenceLocation::Modifier(parent) => self.deferred_context(&parent),
            ReferenceLocation::Recipe(_) => Some(true),
            ReferenceLocation::VariableValue(definition) => {
                self.is_deferred(&definition).then_some(false)
            }
            ReferenceLocation::TargetSpecificValue(definition) => {
                self.is_deferred(&definition).then_some(true)
            }
            _ => None,
        }
    }

    /// Whether make expands the value of `definition` when it is used,
    /// rather than when it reads it.
    fn is_deferred(&self, definition: &VariableDefinition) -> bool {
        match definition.assignment_operator_kind() {
            None => definition.is_define(),
            Some(AssignmentOperator::Recursive | AssignmentOperator::IfUndefined) => true,
            Some(AssignmentOperator::Append) => {
                let Some(name) = definition.name() else {
                    return true;
                };
                let start = definition.syntax().text_range().start();
                let walker = Walker::run(&self.makefile, &self.env, self.variant, Some(start));
                match walker.state.binding(&name, &self.env, false) {
                    Binding::Set(var) => var.recursive,
                    _ => true,
                }
            }
            Some(_) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Evaluation;

    fn empty_env() -> Environment {
        Environment::known(Vec::<(String, String)>::new())
    }

    fn evaluate(text: &str, env: Environment) -> Evaluation {
        let makefile: Makefile = text.parse().unwrap();
        makefile.evaluate(env)
    }

    /// `expr` expanded after reading `text`, with an empty environment.
    fn at_end(text: &str, expr: &str) -> String {
        let expansion = evaluate(text, empty_env()).expand_at(expr, TextSize::of(text));
        expansion
            .text()
            .unwrap_or_else(|| panic!("{expr:?} after {text:?}: {expansion:?}"))
    }

    fn check(cases: &[(&str, &str, &str)]) {
        for (text, expr, expected) in cases {
            assert_eq!(at_end(text, expr), *expected, "{expr:?} after {text:?}");
        }
    }

    #[test]
    fn test_assignments() {
        check(&[
            ("A = $(B)\nB = b1\n", "[$(A)]", "[b1]"),
            (
                "B = b1\nS := $(B)\nB = b2\nA = $(B)\n",
                "[$(S)] [$(A)]",
                "[b1] [b2]",
            ),
            (
                "B = b2\nP ::= $(B)\nI :::= $(B) $$x\n",
                "[$(P)] [$(value I)] [$(flavor I)] [$(I)]",
                "[b2] [b2 $$x] [recursive] [b2 $x]",
            ),
            (
                "R = r\nR += $(B)\nB = b3\n",
                "[$(R)] [$(flavor R)]",
                "[r b3] [recursive]",
            ),
            (
                "B = b3\nQ := q\nQ += $(B)\nB = b4\n",
                "[$(Q)] [$(flavor Q)]",
                "[q b3] [simple]",
            ),
            (
                "N += $(B)\nB = b5\n",
                "[$(N)] [$(flavor N)] [$(origin N)]",
                "[b5] [recursive] [file]",
            ),
            ("E += \n", "[$(E)] [$(flavor E)]", "[] [recursive]"),
            ("E2 := x\nE2 += \n", "[$(E2)]", "[x]"),
            (
                "QQ ?= $(B)\nB = b6\nQQ ?= other\n",
                "[$(QQ)] [$(flavor QQ)]",
                "[b6] [recursive]",
            ),
            ("W =    lead trail   \n", "[$(W)]", "[lead trail   ]"),
            (
                "override O = o1\nO = o2\nO += o3\n",
                "[$(O)] [$(origin O)]",
                "[o1] [override]",
            ),
            ("override O = o1\noverride O += o4\n", "[$(O)]", "[o1 o4]"),
            (
                "export X1 = x1\nunexport X1\nprivate PV = pv\n",
                "[$(X1)] [$(PV)]",
                "[x1] [pv]",
            ),
            (
                "U = u\nundefine U\n",
                "[$(U)] [$(origin U)] [$(flavor U)]",
                "[] [undefined] [undefined]",
            ),
            ("override O = o\nundefine O\n", "[$(O)]", "[o]"),
            (
                "override O = o\noverride undefine O\n",
                "[$(O)] [$(origin O)]",
                "[] [undefined]",
            ),
            (
                "override P = p\nP ?= q\nP := r\ndefine P\ns\nendef\n",
                "[$(P)]",
                "[p]",
            ),
        ]);
    }

    #[test]
    fn test_define() {
        let text = "B = b1\ndefine D1\none $(B)\ntwo\nendef\ndefine D2 :=\nx $(B)\nendef\n\
                    define D3 +=\ny $(B)\nendef\nD4 = d4\ndefine D4 +=\nmore\nendef\n\
                    define D5 ?=\nfive\nendef\nB = b2\ndefine E\n\nendef\n";
        check(&[
            (text, "[$(D1)] [$(flavor D1)]", "[one b2\ntwo] [recursive]"),
            (text, "[$(D2)] [$(flavor D2)]", "[x b1] [simple]"),
            (text, "[$(D3)] [$(flavor D3)]", "[y b2] [recursive]"),
            (text, "[$(D4)] [$(D5)]", "[d4 more] [five]"),
            (text, "[$(E)]", "[]"),
        ]);
    }

    #[test]
    fn test_references() {
        let text = "X = x\nA_B = ab\nA = A\nL = a.c  b.c c.h\nCC = .c=.z\nSP = $(EMPTY) $(EMPTY)\n";
        check(&[
            (text, "[$X] [${X}] [$(X)] [$$X] [$]", "[x] [x] [x] [$X] ["),
            (text, "[$($(A)_B)] [${$(A)_B}]", "[ab] [ab]"),
            (
                text,
                "[$(L:.c=.o)] [$(L:%.c=%.o)] [$(L:c=x)] [$(L:=.y)]",
                "[a.o b.o c.h] [a.o b.o c.h] [a.x b.x c.h] [a.c.y b.c.y c.h.y]",
            ),
            (text, "[$(L:$(CC))]", "[a.z b.z c.h]"),
            (text, "[$(UNDEF:.c=.o)] [$(UNDEF)]", "[] []"),
            (text, "[$(SP)]", "[ ]"),
            (text, "$", "$"),
        ]);
    }

    #[test]
    fn test_recursion() {
        for text in ["X = $(X)\n", "X = $(Y)\nY = $(X)\n", "X = a $(X)\n"] {
            let evaluation = evaluate(text, empty_env());
            assert_eq!(
                evaluation.variable("X"),
                Some(Expansion::unknown(
                    "$(X)",
                    UnknownReason::Recursion("X".to_string())
                )),
                "{text:?}"
            );
        }
    }

    #[test]
    fn test_unknown_conditional() {
        let text = "R = before\nK = known\nifdef FROM_ENV\nR = set\nendif\n";
        let evaluation = evaluate(text, Environment::Unknown);
        assert_eq!(
            evaluation.variable("R"),
            Some(Expansion::unknown("$(R)", UnknownReason::Conditional))
        );
        assert_eq!(
            evaluation.variable("K").and_then(|e| e.text()),
            Some("known".to_string())
        );
        // A later conditional on it is unknown too.
        let text = format!("{text}ifeq ($(R),set)\nS = 1\nelse\nS = 2\nendif\n");
        let evaluation = evaluate(&text, Environment::Unknown);
        assert_eq!(
            evaluation.variable("S"),
            Some(Expansion::unknown("$(S)", UnknownReason::Conditional))
        );
    }

    #[test]
    fn test_partial_expansion() {
        let text = "DIR := /usr/local\nOUT = $(DIR)/$(PREFIX)/bin\n";
        let expansion = evaluate(text, Environment::Unknown)
            .variable("OUT")
            .unwrap();
        assert_eq!(
            expansion.parts(),
            &[
                ExpansionPart::Known("/usr/local/".to_string()),
                ExpansionPart::Unknown {
                    text: "$(PREFIX)".to_string(),
                    reason: UnknownReason::UndefinedVariable("PREFIX".to_string()),
                },
                ExpansionPart::Known("/bin".to_string()),
            ]
        );
        assert_eq!(expansion.to_string(), "/usr/local/$(PREFIX)/bin");
        assert_eq!(expansion.text(), None);
        // A function needs all its arguments.
        let text = "X = $(patsubst %.c,%.o,$(SRCS)) $(shell date)\n";
        assert_eq!(
            evaluate(text, Environment::Unknown)
                .variable("X")
                .unwrap()
                .to_string(),
            "$(patsubst %.c,%.o,$(SRCS)) $(shell date)"
        );
    }

    #[test]
    fn test_environment() {
        let env = Environment::known([("HOME", "/home/x"), ("FLAGS", "-a")]);
        let text = "FLAGS += -b\nD ?= d\nH = $(HOME)\n";
        let evaluation = evaluate(text, env);
        let value = |name| evaluation.variable(name).and_then(|e| e.text());
        assert_eq!(value("H"), Some("/home/x".to_string()));
        assert_eq!(value("FLAGS"), Some("-a -b".to_string()));
        assert_eq!(value("D"), Some("d".to_string()));
        assert_eq!(evaluation.variable("NOPE"), None);
        assert_eq!(
            evaluation.variable("CC"),
            Some(Expansion::unknown(
                "$(CC)",
                UnknownReason::BuiltinVariable("CC".to_string())
            ))
        );
        // Without a known environment, `?=` and `+=` on a variable the
        // makefile has not set are unknown.
        let evaluation = evaluate(text, Environment::Unknown);
        for name in ["FLAGS", "D"] {
            assert_eq!(
                evaluation.variable(name),
                Some(Expansion::unknown(
                    &format!("$({name})"),
                    UnknownReason::UndefinedVariable(name.to_string())
                ))
            );
        }
    }

    #[test]
    fn test_include_load_eval() {
        let cases = [
            ("include x.mk\n", UnknownReason::Include),
            ("-include x.mk\n", UnknownReason::Include),
            ("sinclude x.mk\n", UnknownReason::Include),
            ("load x.so\n", UnknownReason::Load),
            ("$(eval A = 2)\n", UnknownReason::Eval),
            ("S := $(eval A = 2)\n", UnknownReason::Eval),
            ("$(ASSIGN)\n", UnknownReason::Eval),
            ("$(NOT_SET)_X = 1\n", UnknownReason::UnknownName),
        ];
        for (line, reason) in cases {
            let text = format!("A = 1\nB := $(Y)\n{line}C = 3\n");
            let evaluation = evaluate(&text, Environment::Unknown);
            assert_eq!(
                evaluation.variable("A"),
                Some(Expansion::unknown("$(A)", reason.clone())),
                "{line:?}"
            );
            assert_eq!(
                evaluation.variable("OTHER"),
                Some(Expansion::unknown("$(OTHER)", reason.clone())),
                "{line:?}"
            );
            assert_eq!(
                evaluation.variable("C").and_then(|e| e.text()),
                Some("3".to_string()),
                "{line:?}"
            );
        }
        // `info` does not change any variable.
        let evaluation = evaluate("A = 1\n$(info $(A))\n", Environment::Unknown);
        assert_eq!(
            evaluation.variable("A").and_then(|e| e.text()),
            Some("1".to_string())
        );
    }

    #[test]
    fn test_expand_at() {
        let text = "A = 1\nB := $(A)\nA = 2\n";
        let evaluation = evaluate(text, empty_env());
        let second_line = TextSize::of("A = 1\n");
        assert_eq!(
            evaluation.expand_at("$(A)", second_line).text(),
            Some("1".to_string())
        );
        assert_eq!(
            evaluation.expand_at("$(A)", TextSize::of(text)).text(),
            Some("2".to_string())
        );
    }

    #[test]
    fn test_expand_reference() {
        let text = "A = 1\nB := $(A)\nC = $(A)\nall: $(A)\n\techo $(A) $@\nA = 2\n";
        let makefile: Makefile = text.parse().unwrap();
        let evaluation = makefile.evaluate(empty_env());
        let expanded: Vec<_> = makefile
            .syntax()
            .descendants()
            .filter_map(VariableReference::cast)
            .map(|r| evaluation.expand_reference(&r).to_string())
            .collect();
        assert_eq!(expanded, vec!["1", "2", "1", "2", "$@"]);
    }

    #[test]
    fn test_automatic_variables_in_recipes() {
        let makefile: Makefile = "all:\n\techo $(@D) $(|D)\n".parse().unwrap();
        let evaluation = makefile.evaluate(empty_env());
        let recipe: Vec<_> = makefile
            .syntax()
            .descendants()
            .filter_map(VariableReference::cast)
            .map(|r| evaluation.expand_reference(&r))
            .collect();
        // GNU make has no `$(|D)`, so it is an ordinary undefined variable.
        assert_eq!(
            recipe,
            vec![
                Expansion::unknown("$(@D)", UnknownReason::AutomaticVariable("@D".to_string())),
                Expansion::known(""),
            ]
        );
    }

    #[test]
    fn test_automatic_and_target_specific() {
        let text = "CFLAGS = -O2\nall: CFLAGS += -g\nall:\n\techo $(CFLAGS)\nX := [$@]\n";
        let makefile: Makefile = text.parse().unwrap();
        let evaluation = makefile.evaluate(empty_env());
        // Automatic variables are empty while reading the makefile.
        assert_eq!(
            evaluation.variable("X").and_then(|e| e.text()),
            Some("[]".to_string())
        );
        assert_eq!(
            evaluation.variable("CFLAGS").and_then(|e| e.text()),
            Some("-O2".to_string())
        );
        let recipe = makefile
            .syntax()
            .descendants()
            .filter_map(VariableReference::cast)
            .find(|r| matches!(r.location(), ReferenceLocation::Recipe(_)))
            .unwrap();
        assert_eq!(
            evaluation.expand_reference(&recipe),
            Expansion::unknown(
                "$(CFLAGS)",
                UnknownReason::TargetSpecificVariable("CFLAGS".to_string())
            )
        );
    }

    #[test]
    fn test_posix() {
        let text = "X = $(subst a,b,aa)\nY = y\nZ = $(Y:y=z)\n";
        let makefile = Makefile::parse_with_variant(text, MakefileVariant::POSIXMake).tree();
        let evaluation = makefile.evaluate_for(MakefileVariant::POSIXMake, empty_env());
        let value = |name| evaluation.variable(name).and_then(|e| e.text());
        // POSIX make has no functions, so this is a variable reference.
        assert_eq!(value("X"), Some(String::new()));
        assert_eq!(value("Z"), Some("z".to_string()));
    }
}
