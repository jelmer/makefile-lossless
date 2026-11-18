//! Static expansion of variable references, as make would expand them
//! when reading a makefile.

use crate::lossless::{Makefile, VariableReference};
use crate::{ConditionalBranch, MakefileVariant, TextSize};
use std::collections::HashMap;
use std::fmt;

mod gnu;

/// The variables make gets from outside the makefile.
///
/// Variables given on the command line are not modelled.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub enum Environment {
    /// Nothing is known about the environment, so a variable the makefile
    /// does not set is unknown.
    #[default]
    Unknown,
    /// The environment variables, as names and values. A variable the
    /// makefile does not set and that is not in the environment is empty,
    /// except for those make defines itself, such as `CC`, `MAKE` or
    /// `CURDIR`, which are unknown unless given here.
    Known(HashMap<String, String>),
}

impl Environment {
    /// An environment with exactly the given variables.
    pub fn known<K: Into<String>, V: Into<String>>(vars: impl IntoIterator<Item = (K, V)>) -> Self {
        Self::Known(
            vars.into_iter()
                .map(|(k, v)| (k.into(), v.into()))
                .collect(),
        )
    }
}

/// Why part of an [`Expansion`] is not known.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UnknownReason {
    /// The variable is not set in the makefile, so it may come from the
    /// environment.
    UndefinedVariable(String),
    /// A variable make defines itself, such as `CC` or `MAKE`, that the
    /// [`Environment`] does not give.
    BuiltinVariable(String),
    /// An automatic variable such as `$@`, which make sets for each recipe.
    AutomaticVariable(String),
    /// A variable that a target-specific or pattern-specific assignment
    /// sets, in a recipe or target-specific value where that may apply.
    TargetSpecificVariable(String),
    /// A call of a function that is not evaluated, such as `shell` or
    /// `wildcard`.
    UnsupportedFunction(String),
    /// The value of a `!=` assignment, which comes from a shell command.
    ShellAssignment,
    /// After an `include` directive, whose makefiles can set any variable.
    Include,
    /// After a `load` directive, whose objects can set any variable.
    Load,
    /// After a call of `eval`, or a line whose expansion make reads as
    /// makefile text, either of which can set any variable.
    Eval,
    /// Set in a conditional branch that make may or may not read.
    Conditional,
    /// After an assignment to a variable whose name is not known, which may
    /// be any variable.
    UnknownName,
    /// A recursively expanded variable that refers to itself, which is an
    /// error in make.
    Recursion(String),
    /// Expansion nested too deeply, as in a `call` that never ends.
    DepthLimit,
    /// An error that stops make, with make's message.
    Error(String),
    /// The make variant is not supported.
    UnsupportedVariant(MakefileVariant),
}

impl fmt::Display for UnknownReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UndefinedVariable(name) => write!(f, "'{name}' is not set in the makefile"),
            Self::BuiltinVariable(name) => write!(f, "'{name}' is set by make"),
            Self::AutomaticVariable(name) => write!(f, "'{name}' is an automatic variable"),
            Self::TargetSpecificVariable(name) => {
                write!(f, "'{name}' has target-specific values")
            }
            Self::UnsupportedFunction(name) => write!(f, "'{name}' is not evaluated"),
            Self::ShellAssignment => write!(f, "the value comes from a shell command"),
            Self::Include => write!(f, "an included makefile can change it"),
            Self::Load => write!(f, "a loaded object can change it"),
            Self::Eval => write!(f, "an eval can change it"),
            Self::Conditional => write!(f, "it is set in a conditional that may not apply"),
            Self::UnknownName => write!(f, "a variable with an unknown name is set"),
            Self::Recursion(name) => write!(f, "'{name}' references itself"),
            Self::DepthLimit => write!(f, "expansion is nested too deeply"),
            Self::Error(message) => write!(f, "{message}"),
            Self::UnsupportedVariant(variant) => write!(f, "{variant:?} is not supported"),
        }
    }
}

impl UnknownReason {
    /// Whether make stops with an error here, so that the whole value it is
    /// part of is unknown.
    fn is_fatal(&self) -> bool {
        matches!(self, Self::Recursion(_) | Self::DepthLimit | Self::Error(_))
    }
}

/// A part of an [`Expansion`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ExpansionPart {
    /// Text whose expansion is known.
    Known(String),
    /// Text whose expansion is not known.
    Unknown {
        /// The text as written, such as `$(shell date)`.
        text: String,
        /// Why it is not known.
        reason: UnknownReason,
    },
}

/// The result of expanding text, which may be only partly known.
///
/// Its [`Display`](fmt::Display) shows the known parts expanded and the
/// unknown ones as written.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Expansion {
    parts: Vec<ExpansionPart>,
}

impl Expansion {
    fn known(text: &str) -> Self {
        let mut expansion = Self::default();
        expansion.push_str(text);
        expansion
    }

    fn unknown(text: &str, reason: UnknownReason) -> Self {
        let mut expansion = Self::default();
        expansion.push_unknown(text, reason);
        expansion
    }

    /// The parts, in order. Adjacent known parts are merged.
    pub fn parts(&self) -> &[ExpansionPart] {
        &self.parts
    }

    /// The expanded text, if all of it is known.
    pub fn text(&self) -> Option<String> {
        let mut text = String::new();
        for part in &self.parts {
            match part {
                ExpansionPart::Known(known) => text.push_str(known),
                ExpansionPart::Unknown { .. } => return None,
            }
        }
        Some(text)
    }

    /// Whether all of the expansion is known.
    pub fn is_known(&self) -> bool {
        self.unknown_reason().is_none()
    }

    /// The reason the first unknown part is not known, if there is one.
    pub fn unknown_reason(&self) -> Option<&UnknownReason> {
        self.parts.iter().find_map(|part| match part {
            ExpansionPart::Unknown { reason, .. } => Some(reason),
            ExpansionPart::Known(_) => None,
        })
    }

    fn fatal_reason(&self) -> Option<&UnknownReason> {
        self.parts.iter().find_map(|part| match part {
            ExpansionPart::Unknown { reason, .. } if reason.is_fatal() => Some(reason),
            _ => None,
        })
    }

    fn push_str(&mut self, text: &str) {
        if text.is_empty() {
            return;
        }
        if let Some(ExpansionPart::Known(last)) = self.parts.last_mut() {
            last.push_str(text);
        } else {
            self.parts.push(ExpansionPart::Known(text.to_string()));
        }
    }

    fn push_unknown(&mut self, text: &str, reason: UnknownReason) {
        self.parts.push(ExpansionPart::Unknown {
            text: text.to_string(),
            reason,
        });
    }

    fn extend(&mut self, other: Expansion) {
        for part in other.parts {
            match part {
                ExpansionPart::Known(text) => self.push_str(&text),
                part => self.parts.push(part),
            }
        }
    }

    /// Whether the expansion is empty, if that is known.
    fn is_empty_known(&self) -> Option<bool> {
        let mut empty = Some(true);
        for part in &self.parts {
            match part {
                ExpansionPart::Known(text) if !text.is_empty() => return Some(false),
                ExpansionPart::Known(_) => {}
                ExpansionPart::Unknown { .. } => empty = None,
            }
        }
        empty
    }

    /// Append `addition` after a space, as `+=` does: there is no space if
    /// either is empty.
    fn append_word(&mut self, addition: Expansion) {
        let added = addition.is_empty_known();
        if added == Some(true) {
            return;
        }
        match (self.is_empty_known(), added) {
            (Some(true), _) => *self = addition,
            (Some(false), Some(false)) => {
                self.push_str(" ");
                self.extend(addition);
            }
            _ => {
                let reason = self
                    .unknown_reason()
                    .or(addition.unknown_reason())
                    .cloned()
                    .unwrap_or(UnknownReason::Conditional);
                self.push_unknown(" ", reason);
                self.extend(addition);
            }
        }
    }

    /// The expansion with each `$` in its known parts doubled, as `:::=`
    /// stores the value.
    fn escape_dollars(self) -> Expansion {
        let parts = self
            .parts
            .into_iter()
            .map(|part| match part {
                ExpansionPart::Known(text) => ExpansionPart::Known(text.replace('$', "$$")),
                part => part,
            })
            .collect();
        Expansion { parts }
    }
}

impl fmt::Display for Expansion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for part in &self.parts {
            match part {
                ExpansionPart::Known(text) | ExpansionPart::Unknown { text, .. } => {
                    f.write_str(text)?
                }
            }
        }
        Ok(())
    }
}

/// The variables of a makefile, as make knows them while reading it; see
/// [`Makefile::evaluate`].
#[derive(Debug, Clone)]
pub struct Evaluation {
    engine: Engine,
}

#[derive(Debug, Clone)]
enum Engine {
    Gnu(Box<gnu::Engine>),
    Unsupported(MakefileVariant),
}

impl Evaluation {
    /// The value of the variable `name` at the end of the makefile, or
    /// `None` if it is not set.
    ///
    /// A recursively expanded variable is expanded with the variables at
    /// the end of the makefile, as in a recipe, so automatic variables in
    /// it are unknown.
    pub fn variable(&self, name: &str) -> Option<Expansion> {
        match &self.engine {
            Engine::Gnu(engine) => engine.variable(name),
            Engine::Unsupported(variant) => Some(unsupported(&format!("$({name})"), *variant)),
        }
    }

    /// Expand `text` with the variables as make knows them when it reads
    /// the line at `offset`.
    pub fn expand_at(&self, text: &str, offset: TextSize) -> Expansion {
        match &self.engine {
            Engine::Gnu(engine) => engine.expand_at(text, offset),
            Engine::Unsupported(variant) => unsupported(text, *variant),
        }
    }

    /// Expand `reference` as make does where it is.
    ///
    /// GNU make expands references in targets, prerequisites, conditions,
    /// directives and the values of `:=`, `::=`, `:::=` and `!=`
    /// assignments when it reads them, so these are expanded with the
    /// variables at that point, as with [`Self::expand_at`]. References in
    /// recipes and in the values of `=`, `?=` and `define` assignments, and
    /// of `+=` on a recursively expanded variable, are expanded later, with
    /// the variables at the end of the makefile; there, automatic variables
    /// and, in recipes and target-specific values, variables with
    /// target-specific values are unknown.
    ///
    /// A reference nested in a function call or another reference is
    /// expanded on its own, so a variable that `foreach` or `call` sets is
    /// taken from the makefile instead.
    pub fn expand_reference(&self, reference: &VariableReference) -> Expansion {
        match &self.engine {
            Engine::Gnu(engine) => engine.expand_reference(reference),
            Engine::Unsupported(variant) => {
                unsupported(&reference.syntax().text().to_string(), *variant)
            }
        }
    }

    /// Whether make reads `branch`, or `None` if that is not known.
    pub fn branch_taken(&self, branch: &ConditionalBranch) -> Option<bool> {
        match &self.engine {
            Engine::Gnu(engine) => engine.branch_taken(branch),
            Engine::Unsupported(_) => None,
        }
    }
}

fn unsupported(text: &str, variant: MakefileVariant) -> Expansion {
    Expansion::unknown(text, UnknownReason::UnsupportedVariant(variant))
}

impl Makefile {
    /// Follow the variables of this makefile as GNU make reads it, given
    /// what is known about the environment; see
    /// [`Self::evaluate_for`].
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::{Environment, Makefile};
    /// let makefile: Makefile = "DIR := /usr/local\nBIN = $(DIR)/bin\n".parse().unwrap();
    /// let evaluation = makefile.evaluate(Environment::default());
    /// let bin = evaluation.variable("BIN").unwrap();
    /// assert_eq!(bin.text(), Some("/usr/local/bin".to_string()));
    /// ```
    pub fn evaluate(&self, env: Environment) -> Evaluation {
        self.evaluate_for(MakefileVariant::GNUMake, env)
    }

    /// Follow the variables of this makefile as `variant` reads it.
    ///
    /// For GNU make, assignments, `define`, `undefine` and `override` are
    /// followed, and conditionals whose condition is known: a variable set
    /// in a branch that may or may not be read is unknown afterwards. After
    /// an `include` or `load` directive, a call of `eval` or a line whose
    /// expansion make reads as makefile text, every variable is unknown
    /// until it is set again. The pure text functions are evaluated;
    /// others, such as `shell` and `wildcard`, are unknown. Variables given
    /// on the command line are not taken into account.
    ///
    /// POSIX make is read like GNU make without its functions. For BSD
    /// make and nmake, everything is unknown.
    pub fn evaluate_for(&self, variant: MakefileVariant, env: Environment) -> Evaluation {
        let engine = match variant {
            MakefileVariant::GNUMake | MakefileVariant::POSIXMake => {
                Engine::Gnu(Box::new(gnu::Engine::new(self, variant, env)))
            }
            // TODO: support BSD make and nmake.
            MakefileVariant::BSDMake | MakefileVariant::NMake => Engine::Unsupported(variant),
        };
        Evaluation { engine }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty_env() -> Environment {
        Environment::known(Vec::<(String, String)>::new())
    }

    #[test]
    fn test_unsupported_variants() {
        for variant in [MakefileVariant::BSDMake, MakefileVariant::NMake] {
            let makefile: Makefile = "X = 1\n".parse().unwrap();
            let evaluation = makefile.evaluate_for(variant, empty_env());
            assert_eq!(
                evaluation.variable("X"),
                Some(Expansion::unknown(
                    "$(X)",
                    UnknownReason::UnsupportedVariant(variant)
                ))
            );
        }
    }
}
