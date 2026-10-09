use super::*;
use crate::bsd_condition::BsdConditionErrorKind;
use crate::lex::{lex, lex_first_non_recipe_line, lex_non_recipe_line};
use crate::syntax_rules::{
    ends_with_unescaped_backslash, escapes_next, is_assignment_modifier, is_bsd_elif, is_bsd_if,
    is_colons_before_subst, is_gnu_conditional_start, ASSIGNMENT_OPERATORS,
    GNU_CONDITIONAL_KEYWORDS, GNU_CONDITIONAL_STARTS, GNU_INCLUDE_KEYWORDS, POSIX_INCLUDE_KEYWORDS,
};
use crate::MakefileVariant;
use rowan::GreenNode;

mod assignment;
mod conditional;
mod directive;
mod errors;
mod lookahead;
mod recipe;
mod reference;
mod rule;
mod tokens;

pub(crate) use directive::{has_nmake_directive, may_have_nmake_directives};
pub(crate) use errors::locate_error_line;
pub(crate) use reference::bsd_logical_line;
use tokens::{token_stack, Token};

/// The parse results are stored as a "green tree".
#[derive(Debug)]
pub(crate) struct Parse {
    pub(crate) green_node: GreenNode,
    pub(crate) errors: Vec<ErrorInfo>,
    pub(crate) positioned_errors: Vec<PositionedParseError>,
    /// The range of each line ending that ends a logical line, in order.
    pub(crate) line_ends: Vec<rowan::TextRange>,
}

/// Whether a tab-indented line is a recipe line.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RuleContext {
    Outside,
    Inside,
    /// Inside on some paths through the preceding conditionals but not on
    /// others, so it depends on which branches make takes.
    Varies,
}

impl RuleContext {
    fn join(self, other: Self) -> Self {
        if self == other {
            self
        } else {
            Self::Varies
        }
    }
}

struct Parser<'a> {
    /// input tokens, including whitespace,
    /// in *reverse* order.
    tokens: Vec<Token<'a>>,
    /// the in-progress tree.
    builder: GreenNodeBuilder<'static>,
    /// the list of syntax errors we've accumulated
    /// so far.
    errors: Vec<ErrorInfo>,
    /// positioned errors with location information
    positioned_errors: Vec<PositionedParseError>,
    /// The original text
    original_text: &'a str,
    /// The offset of the start of each line in `original_text`.
    line_starts: Vec<usize>,
    /// The makefile variant
    variant: Option<MakefileVariant>,
    /// Number of enclosing BSD `.for` loops.
    for_depth: usize,
    /// Number of enclosing BSD `.if` or nmake `!IF` conditionals.
    block_conditional_depth: usize,
    /// Number of enclosing conditionals and loops of any kind.
    nesting_depth: usize,
    /// Number of variable references being parsed that enclose the
    /// current token.
    reference_depth: usize,
    /// Parity of the current run of bumped BACKSLASH tokens: true once an
    /// odd number have been seen, meaning the next backslash is escaped
    /// (`\\`) and a following newline is a literal backslash, not a line
    /// continuation. Reset to false by any other token. Like the lexer's
    /// `pending_backslash_escape`, this follows [`escapes_next`].
    pending_backslash_escape: bool,
    /// The quote that ends the quoted `ifeq` argument being parsed, if
    /// any. It ends any variable reference in the argument too.
    argument_quote: Option<String>,
    /// Whether we are in rule context, i.e. a tab-indented line is a
    /// recipe line. Set by a rule line and cleared by any other line
    /// except comments, blank lines and conditional directives.
    in_rule: RuleContext,
    /// The logical line last used to find a BSD make expression.
    bsd_line: Option<BsdLine>,
    /// Number of times tokens were lexed again, which may change where
    /// a logical line ends.
    token_edits: usize,
    /// The result of the last call to [`Parser::recipe_continues`].
    recipe_continues: std::cell::Cell<Option<RecipeContinues>>,
    /// The range of each NEWLINE token consumed so far that ends a
    /// logical line, rather than continuing it.
    line_ends: Vec<rowan::TextRange>,
}

/// The result of [`Parser::recipe_continues`] at the start of a line. It
/// is the same at the start of any later comment or blank line before
/// the first other line, as those don't change rule context.
#[derive(Clone, Copy)]
struct RecipeContinues {
    /// The number of tokens left at the start of the line.
    start: usize,
    /// The number of tokens left at the first line that is not a
    /// comment or blank line.
    end: usize,
    in_rule: RuleContext,
    token_edits: usize,
    result: bool,
}

/// A logical line lexed again, from [`Parser::lex_as_non_recipe_line`].
struct RelexedLine<'a> {
    /// The new tokens, in reverse order.
    tokens: Vec<Token<'a>>,
    /// The number of current tokens they replace.
    replaces: usize,
}

/// The rest of a logical line, from [`Parser::bsd_logical_line`].
struct BsdLine {
    text: String,
    /// `text` as make sees it, with `\#` replaced by `#`, and the
    /// expressions parsed in it.
    exprs: crate::reference::BsdExprLine,
    /// The source position of each token and its offset in `text`.
    starts: Vec<(rowan::TextSize, usize)>,
    /// The source position of the end of the line.
    end: rowan::TextSize,
    /// The value of `Parser::token_edits` when the line was built.
    token_edits: usize,
}

impl Parser<'_> {
    fn parse_comment(&mut self) {
        if self.current() == Some(COMMENT) {
            self.bump(); // Consume the comment token

            // Handle end of line or file after comment
            if self.current() == Some(NEWLINE) {
                self.bump(); // Consume the newline
            } else if self.current() == Some(WHITESPACE) {
                // For whitespace after a comment, just consume it
                self.skip_ws();
                if self.current() == Some(NEWLINE) {
                    self.bump();
                }
            }
            // If we're at EOF after a comment, that's fine
        } else {
            self.error(ParseErrorKind::Other, "expected comment".to_string());
        }
    }

    // Helper to parse normal content (define block, assignment, include,
    // vpath, expression statement or rule). This is shared by the top
    // level and conditional bodies.
    fn parse_normal_content(&mut self) {
        // Skip any leading whitespace
        self.skip_ws();

        // Like GNU Make, check for an assignment before include/vpath so
        // that e.g. "vpath = foo" defines a variable.
        if self.is_define_line() {
            self.parse_define();
        } else if self.is_variable_assignment_line() {
            self.parse_assignment();
        } else if self.at_include_keyword() {
            self.parse_include();
        } else if self.at_load_keyword() {
            self.parse_load();
        } else if self.at_vpath_keyword() {
            self.parse_vpath();
        } else if self.is_expression_statement_line() {
            self.parse_expression_statement();
        } else {
            // Try to handle as a rule
            self.parse_rule();
        }
    }

    /// Whether parsing for BSD make only, where GNU make's directives
    /// such as `define` and `override` are not recognized.
    fn is_bsd_make(&self) -> bool {
        self.variant == Some(MakefileVariant::BSDMake)
    }

    /// Whether GNU make only directives such as `define` and `undefine`
    /// are recognized.
    fn gnu_directives_enabled(&self) -> bool {
        matches!(self.variant, None | Some(MakefileVariant::GNUMake))
    }

    fn bsd_directives_enabled(&self) -> bool {
        matches!(self.variant, None | Some(MakefileVariant::BSDMake))
    }

    fn parse_token(&mut self) -> bool {
        if let Some((name, count)) = self.directive() {
            self.parse_directive(name, count);
            return true;
        }
        match self.current() {
            None => false,
            Some(IDENTIFIER) => {
                if self.at_conditional_keyword() {
                    self.parse_conditional();
                } else {
                    self.parse_normal_content();
                }
                true
            }
            Some(DOLLAR) => {
                self.parse_normal_content();
                true
            }
            Some(NEWLINE) => {
                self.builder.start_node(BLANK_LINE.into());
                self.bump();
                self.builder.finish_node();
                true
            }
            Some(COMMENT) => {
                self.parse_comment();
                true
            }
            Some(WHITESPACE) => {
                // Leading whitespace before an ordinary makefile line
                self.skip_ws();
                true
            }
            Some(INDENT) => {
                // In rule context here, this is a recipe line after a
                // conditional whose branches all end in rule context. It
                // belongs to the rule ending the branch that is taken,
                // so it can't be part of any one rule node.
                self.parse_indented_line();
                true
            }
            // Variable names may start with a backslash, e.g. `\n := ...`
            Some(BACKSLASH) if self.is_variable_assignment_line() => {
                self.parse_assignment();
                true
            }
            Some(OPERATOR) if self.bsd_directives_enabled() && self.at_assignment_operator() => {
                self.parse_assignment();
                true
            }
            // Like make, check for an assignment first, so that `!x = 1`
            // defines a variable even where `!` is a dependency operator.
            Some(OPERATOR) if self.at_bang() && self.is_variable_assignment_line() => {
                self.parse_assignment();
                true
            }
            Some(OPERATOR) if self.at_dependency_operator() => {
                self.parse_rule();
                true
            }
            Some(OPERATOR) if self.at_literal_bang() && self.line_has_dependency_operator() => {
                self.parse_normal_content();
                true
            }
            // Lines may also start with characters such as `*` in
            // `*.o: *.c` or `}` in `}: dep`. BSD make takes a leading
            // `(` as an archive member list without an archive name.
            Some(kind @ (TEXT | BACKSLASH | LPAREN | RPAREN | LBRACE | RBRACE | COMMA | QUOTE))
                if (kind != LPAREN || !self.is_bsd_make())
                    && (self.line_has_dependency_operator()
                        || self.is_assignment_line()
                        || (self.bsd_directives_enabled() && self.is_bsd_assignment_line())) =>
            {
                self.parse_normal_content();
                true
            }
            Some(kind) => {
                // `error()` already consumes the offending token; bumping
                // again here would pop past the end of the stack when
                // this is the last token.
                self.error(
                    ParseErrorKind::UnexpectedToken,
                    format!("unexpected token {:?}", kind),
                );
                true
            }
        }
    }

    fn parse(mut self) -> Parse {
        self.builder.start_node(ROOT.into());

        while self.parse_token() {}

        self.builder.finish_node();

        let green_node = self.builder.finish();
        crate::lossless::remember_line_starts(
            &green_node,
            self.line_starts[1..]
                .iter()
                .map(|&start| rowan::TextSize::try_from(start).unwrap())
                .collect(),
        );
        for error in &mut self.positioned_errors {
            locate_error_line(&self.line_ends, self.original_text, error);
        }

        Parse {
            green_node,
            errors: self.errors,
            positioned_errors: self.positioned_errors,
            line_ends: self.line_ends,
        }
    }
}

pub(crate) fn parse(text: &str, variant: Option<MakefileVariant>) -> Parse {
    Parser {
        tokens: token_stack(0.into(), lex(text, variant)),
        builder: GreenNodeBuilder::new(),
        errors: Vec::new(),
        positioned_errors: Vec::new(),
        original_text: text,
        line_starts: std::iter::once(0)
            .chain(text.match_indices('\n').map(|(i, _)| i + 1))
            .collect(),
        variant,
        for_depth: 0,
        block_conditional_depth: 0,
        nesting_depth: 0,
        reference_depth: 0,
        pending_backslash_escape: false,
        argument_quote: None,
        in_rule: RuleContext::Outside,
        bsd_line: None,
        token_edits: 0,
        recipe_continues: std::cell::Cell::new(None),
        line_ends: Vec::new(),
    }
    .parse()
}

impl Parse {
    pub(crate) fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root_mut(self.green_node.clone())
    }

    pub(crate) fn root(&self) -> Makefile {
        Makefile::cast(self.syntax()).unwrap()
    }
}
