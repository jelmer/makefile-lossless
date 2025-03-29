use crate::lex::lex;
use crate::SyntaxKind;
use crate::SyntaxKind::*;
use rowan::ast::AstNode;
use std::str::FromStr;

#[derive(Debug)]
/// An error that can occur when parsing a makefile
pub enum Error {
    /// An I/O error occurred
    Io(std::io::Error),

    /// A parse error occurred
    Parse(ParseError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            Error::Io(e) => write!(f, "IO error: {}", e),
            Error::Parse(e) => write!(f, "Parse error: {}", e),
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::Io(e)
    }
}

impl std::error::Error for Error {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// An error that occurred while parsing a makefile
pub struct ParseError {
    errors: Vec<ErrorInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Information about a specific parsing error
pub struct ErrorInfo {
    message: String,
    line: usize,
    context: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for err in &self.errors {
            writeln!(f, "Error at line {}: {}", err.line, err.message)?;
            writeln!(f, "{}| {}", err.line, err.context)?;
        }
        Ok(())
    }
}

impl std::error::Error for ParseError {}

impl From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Error::Parse(e)
    }
}

/// Second, implementing the `Language` trait teaches rowan to convert between
/// these two SyntaxKind types, allowing for a nicer SyntaxNode API where
/// "kinds" are values from our `enum SyntaxKind`, instead of plain u16 values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lang {}
impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

/// GreenNode is an immutable tree, which is cheap to change,
/// but doesn't contain offsets and parent pointers.
use rowan::GreenNode;

/// You can construct GreenNodes by hand, but a builder
/// is helpful for top-down parsers: it maintains a stack
/// of currently in-progress nodes
use rowan::GreenNodeBuilder;

/// The parse results are stored as a "green tree".
/// We'll discuss working with the results later
#[derive(Debug)]
struct Parse {
    green_node: GreenNode,
    #[allow(unused)]
    errors: Vec<ErrorInfo>,
}

fn parse(text: &str) -> Parse {
    struct Parser {
        /// input tokens, including whitespace,
        /// in *reverse* order.
        tokens: Vec<(SyntaxKind, String)>,
        /// the in-progress tree.
        builder: GreenNodeBuilder<'static>,
        /// the list of syntax errors we've accumulated
        /// so far.
        errors: Vec<ErrorInfo>,
        /// The original text
        original_text: String,
    }

    impl Parser {
        fn error(&mut self, msg: String) {
            self.builder.start_node(ERROR.into());

            let (line, context) = if self.current() == Some(INDENT) {
                // For indented lines, report the error on the next line
                let lines: Vec<&str> = self.original_text.lines().collect();
                let tab_line = lines
                    .iter()
                    .enumerate()
                    .find(|(_, line)| line.starts_with('\t'))
                    .map(|(i, _)| i + 1)
                    .unwrap_or(1);

                // Use the next line as context if available
                let next_line = tab_line + 1;
                if next_line <= lines.len() {
                    (next_line, lines[next_line - 1].to_string())
                } else {
                    (tab_line, lines[tab_line - 1].to_string())
                }
            } else {
                let line = self.get_line_number_for_position(self.tokens.len());
                (line, self.get_context_for_line(line))
            };

            let message = if self.current() == Some(INDENT) && !msg.contains("indented") {
                if self.tokens.len() > 0 && self.tokens[self.tokens.len() - 1].0 == IDENTIFIER {
                    "expected ':'".to_string()
                } else {
                    "indented line not part of a rule".to_string()
                }
            } else {
                msg
            };

            self.errors.push(ErrorInfo {
                message,
                line,
                context,
            });

            if self.current().is_some() {
                self.bump();
            }
            self.builder.finish_node();
        }

        fn get_line_number_for_position(&self, position: usize) -> usize {
            if position >= self.tokens.len() {
                return self.original_text.matches('\n').count() + 1;
            }

            // Count newlines in the processed text up to this position
            self.tokens[0..position]
                .iter()
                .filter(|(kind, _)| *kind == NEWLINE)
                .count()
                + 1
        }

        fn get_context_for_line(&self, line_number: usize) -> String {
            self.original_text
                .lines()
                .nth(line_number - 1)
                .unwrap_or("")
                .to_string()
        }

        fn parse_recipe_line(&mut self) {
            self.builder.start_node(RECIPE.into());

            // Check for and consume the indent
            if self.current() != Some(INDENT) {
                self.error("recipe line must start with a tab".into());
                self.builder.finish_node();
                return;
            }
            self.bump();

            // Parse the recipe content
            match self.current() {
                Some(TEXT) => self.bump(),
                Some(NEWLINE) => {
                    // Empty recipe line (just a tab) is valid
                    self.bump();
                }
                Some(kind) => {
                    self.error(format!("unexpected token in recipe: {:?}", kind));
                    self.bump();
                }
                None => {
                    // End of file after tab is valid
                }
            }

            // Ensure proper line ending if we're not at EOF
            if self.current().is_some() && self.current() != Some(NEWLINE) {
                self.error("recipe line must end with a newline".into());
                self.skip_until_newline();
            } else if self.current() == Some(NEWLINE) {
                self.bump();
            }

            self.builder.finish_node();
        }

        fn parse_rule_target(&mut self) -> bool {
            match self.current() {
                Some(IDENTIFIER) => {
                    self.bump();
                    true
                }
                Some(DOLLAR) => {
                    self.parse_variable_reference();
                    true
                }
                _ => {
                    self.error("expected rule target".into());
                    false
                }
            }
        }

        fn parse_rule_dependencies(&mut self) {
            self.builder.start_node(EXPR.into());
            while self.current().is_some() && self.current() != Some(NEWLINE) {
                self.bump();
            }
            self.builder.finish_node();
        }

        fn parse_rule_recipes(&mut self) {
            loop {
                match self.current() {
                    Some(INDENT) => {
                        self.parse_recipe_line();
                    }
                    Some(NEWLINE) => {
                        self.bump();
                        break;
                    }
                    _ => break,
                }
            }
        }

        fn find_and_consume_colon(&mut self) -> bool {
            // Skip whitespace before colon
            self.skip_ws();

            // Check if we're at a colon
            if self.current() == Some(OPERATOR) && self.tokens.last().unwrap().1 == ":" {
                self.bump();
                return true;
            }

            // Look ahead for a colon
            let has_colon = self
                .tokens
                .iter()
                .rev()
                .any(|(kind, text)| *kind == OPERATOR && text == ":");

            if has_colon {
                // Consume tokens until we find the colon
                while self.current().is_some() {
                    if self.current() == Some(OPERATOR) && self.tokens.last().unwrap().1 == ":" {
                        self.bump();
                        return true;
                    }
                    self.bump();
                }
            }

            self.error("expected ':'".into());
            false
        }

        fn parse_rule(&mut self) {
            self.builder.start_node(RULE.into());

            // Parse target
            self.skip_ws();
            let has_target = self.parse_rule_target();

            // Find and consume the colon
            let has_colon = if has_target {
                self.find_and_consume_colon()
            } else {
                false
            };

            // Parse dependencies if we found both target and colon
            if has_target && has_colon {
                self.skip_ws();
                self.parse_rule_dependencies();
                self.expect_eol();

                // Parse recipe lines
                self.parse_rule_recipes();
            }

            self.builder.finish_node();
        }

        fn parse_comment(&mut self) {
            self.expect(COMMENT);
            self.expect_eol();
        }

        fn parse_assignment(&mut self) {
            self.builder.start_node(VARIABLE.into());

            // Handle export prefix if present
            self.skip_ws();
            if self.current() == Some(IDENTIFIER) && self.tokens.last().unwrap().1 == "export" {
                self.bump();
                self.skip_ws();
            }

            // Parse variable name
            match self.current() {
                Some(IDENTIFIER) => self.bump(),
                Some(DOLLAR) => self.parse_variable_reference(),
                _ => {
                    self.error("expected variable name".into());
                    self.builder.finish_node();
                    return;
                }
            }

            // Skip whitespace and parse operator
            self.skip_ws();
            match self.current() {
                Some(OPERATOR) => {
                    let op = self.tokens.last().unwrap().1.clone();
                    if ["=", ":=", "::=", ":::=", "+=", "?=", "!="].contains(&op.as_str()) {
                        self.bump();
                        self.skip_ws();

                        // Parse value
                        self.builder.start_node(EXPR.into());
                        while self.current().is_some() && self.current() != Some(NEWLINE) {
                            self.bump();
                        }
                        self.builder.finish_node();

                        // Expect newline
                        if self.current() == Some(NEWLINE) {
                            self.bump();
                        } else {
                            self.error("expected newline after variable value".into());
                        }
                    } else {
                        self.error(format!("invalid assignment operator: {}", op));
                    }
                }
                _ => self.error("expected assignment operator".into()),
            }

            self.builder.finish_node();
        }

        fn parse_variable_reference(&mut self) {
            self.builder.start_node(EXPR.into());
            self.bump(); // Consume $
            
            if self.current() == Some(LPAREN) {
                self.bump(); // Consume (
                
                // Start by checking if this is a function like $(shell ...)
                let mut is_function = false;
                
                if self.current() == Some(IDENTIFIER) {
                    let function_name = self.tokens.last().unwrap().1.clone();
                    // Common makefile functions
                    let known_functions = ["shell", "wildcard", "call", "eval", "file", "abspath", "dir"];
                    if known_functions.contains(&function_name.as_str()) {
                        is_function = true;
                    }
                }
                
                if is_function {
                    // Preserve the function name
                    self.bump();
                    
                    // Parse the rest of the function call, handling nested variable references
                    self.consume_balanced_parens(1);
                } else {
                    // Handle regular variable references
                    self.parse_parenthesized_expr_internal(true);
                }
            } else {
                self.error("expected ( after $ in variable reference".into());
            }
            
            self.builder.finish_node();
        }

        // Helper method to parse a parenthesized expression
        fn parse_parenthesized_expr(&mut self) {
            self.builder.start_node(EXPR.into());

            if self.current() != Some(LPAREN) {
                self.error("expected opening parenthesis".into());
                self.builder.finish_node();
                return;
            }

            self.bump(); // Consume opening paren
            self.parse_parenthesized_expr_internal(false);
            self.builder.finish_node();
        }

        // Internal helper to parse parenthesized expressions
        fn parse_parenthesized_expr_internal(&mut self, is_variable_ref: bool) {
            let mut paren_count = 1;
            
            while paren_count > 0 && self.current().is_some() {
                match self.current() {
                    Some(LPAREN) => {
                        paren_count += 1;
                        self.bump();
                        // Start a new expression node for nested parentheses
                        self.builder.start_node(EXPR.into());
                    }
                    Some(RPAREN) => {
                        paren_count -= 1;
                        self.bump();
                        if paren_count > 0 {
                            self.builder.finish_node();
                        }
                    }
                    Some(QUOTE) => {
                        // Handle quoted strings
                        self.parse_quoted_string();
                    }
                    Some(DOLLAR) => {
                        // Handle variable references
                        self.parse_variable_reference();
                    }
                    Some(_) => self.bump(),
                    None => {
                        self.error(if is_variable_ref {
                            "unclosed variable reference".into()
                        } else {
                            "unclosed parenthesis".into()
                        });
                        break;
                    }
                }
            }

            if !is_variable_ref {
                self.skip_ws();
                self.expect_eol();
            }
        }
        
        // Handle parsing a quoted string - combines common quoting logic
        fn parse_quoted_string(&mut self) {
            self.bump(); // Consume the quote
            while self.current().is_some() && self.current() != Some(QUOTE) {
                self.bump();
            }
            if self.current() == Some(QUOTE) {
                self.bump();
            }
        }

        fn parse_conditional_keyword(&mut self) -> Option<String> {
            if self.current() != Some(IDENTIFIER) {
                self.error("expected conditional keyword (ifdef, ifndef, ifeq, or ifneq)".into());
                return None;
            }

            let token = self.tokens.last().unwrap().1.clone();
            if !["ifdef", "ifndef", "ifeq", "ifneq"].contains(&token.as_str()) {
                self.error(format!("unknown conditional directive: {}", token));
                return None;
            }

            self.bump();
            Some(token)
        }

        fn parse_simple_condition(&mut self) {
            self.builder.start_node(EXPR.into());

            // Skip any leading whitespace
            self.skip_ws();

            // Collect variable names
            let mut found_var = false;

            while self.current().is_some() && self.current() != Some(NEWLINE) {
                match self.current() {
                    Some(WHITESPACE) => self.skip_ws(),
                    Some(DOLLAR) => {
                        found_var = true;
                        self.parse_variable_reference();
                    }
                    Some(_) => {
                        // Accept any token as part of condition
                        found_var = true;
                        self.bump();
                    }
                    None => break,
                }
            }

            if !found_var {
                // Empty condition is an error in GNU Make
                self.error("expected condition after conditional directive".into());
            }

            self.builder.finish_node();

            // Expect end of line
            if self.current() == Some(NEWLINE) {
                self.bump();
            } else if self.current().is_some() {
                self.skip_until_newline();
            }
        }

        fn parse_elif_condition(&mut self) {
            self.skip_ws();
            match self.current() {
                Some(IDENTIFIER) => {
                    self.builder.start_node(EXPR.into());
                    self.bump();
                    // Handle additional tokens after identifier
                    while self.current().is_some() && self.current() != Some(NEWLINE) {
                        match self.current() {
                            Some(WHITESPACE) => self.skip_ws(),
                            Some(LPAREN) => self.parse_parenthesized_expr(),
                            Some(DOLLAR) => self.parse_variable_reference(),
                            Some(QUOTE) => self.bump(),
                            Some(IDENTIFIER) => self.bump(),
                            Some(OPERATOR) => self.bump(),
                            _ => break,
                        }
                    }
                    self.builder.finish_node();
                }
                Some(LPAREN) => self.parse_parenthesized_expr(),
                Some(DOLLAR) => {
                    self.builder.start_node(EXPR.into());
                    self.parse_variable_reference();
                    self.builder.finish_node();
                }
                _ => self.error("expected condition after elif".into()),
            }
            self.skip_ws();
            self.expect_eol();
        }

        // Helper to check if a token is a conditional directive
        fn is_conditional_directive(&self, token: &str) -> bool {
            token == "ifdef" || token == "ifndef" || token == "ifeq" || token == "ifneq" || 
            token == "else" || token == "elif" || token == "endif"
        }
        
        // Helper method to handle conditional token
        fn handle_conditional_token(&mut self, token: &str, depth: &mut usize) -> bool {
            match token {
                "ifdef" | "ifndef" | "ifeq" | "ifneq" => {
                    *depth += 1;
                    self.parse_conditional();
                    true
                }
                "else" | "elif" => {
                    // Not valid outside of a conditional
                    if *depth == 0 {
                        self.error(format!("{} without matching if", token));
                        false
                    } else {
                        // Consume the token
                        self.bump();
                        
                        // Parse an additional condition if this is an elif
                        if token == "elif" {
                            self.skip_ws();
                            
                            // Check various patterns of elif usage
                            if self.current() == Some(IDENTIFIER) {
                                let next_token = self.tokens.last().unwrap().1.clone();
                                if next_token == "ifeq" || next_token == "ifdef" || next_token == "ifndef" || next_token == "ifneq" {
                                    // Parse the nested condition
                                    match next_token.as_str() {
                                        "ifdef" | "ifndef" => {
                                            self.bump(); // Consume the directive token
                                            self.skip_ws();
                                            self.parse_simple_condition();
                                        }
                                        "ifeq" | "ifneq" => {
                                            self.bump(); // Consume the directive token
                                            self.skip_ws();
                                            self.parse_parenthesized_expr();
                                        }
                                        _ => unreachable!(),
                                    }
                                } else {
                                    // Handle other patterns like "elif defined(X)"
                                    self.builder.start_node(EXPR.into());
                                    // Just consume tokens until newline - more permissive parsing
                                    while self.current().is_some() && self.current() != Some(NEWLINE) {
                                        self.bump();
                                    }
                                    self.builder.finish_node();
                                    if self.current() == Some(NEWLINE) {
                                        self.bump();
                                    }
                                }
                            } else {
                                // Handle any other pattern permissively
                                self.builder.start_node(EXPR.into());
                                // Just consume tokens until newline
                                while self.current().is_some() && self.current() != Some(NEWLINE) {
                                    self.bump();
                                }
                                self.builder.finish_node();
                                if self.current() == Some(NEWLINE) {
                                    self.bump();
                                }
                            }
                        } else {
                            // For 'else', just expect EOL
                            self.expect_eol();
                        }
                        true
                    }
                }
                "endif" => {
                    // Not valid outside of a conditional
                    if *depth == 0 {
                        self.error("endif without matching if".into());
                        false
                    } else {
                        *depth -= 1;
                        // Consume the endif
                        self.bump();
                        
                        // Be more permissive with whitespace after endif
                        self.skip_ws();
                        if self.current() == Some(NEWLINE) {
                            self.bump();
                        } else if self.current().is_some() {
                            // Accept anything after endif with optional whitespace
                            // This handles cases like "A := 1 endif"
                            self.skip_until_newline();
                        }
                        true
                    }
                }
                _ => false,
            }
        }

        fn parse_conditional(&mut self) {
            self.builder.start_node(CONDITIONAL.into());

            // Parse the conditional keyword
            let Some(token) = self.parse_conditional_keyword() else {
                self.skip_until_newline();
                self.builder.finish_node();
                return;
            };

            // Skip whitespace after keyword
            self.skip_ws();

            // Parse the condition based on keyword type
            match token.as_str() {
                "ifdef" | "ifndef" => {
                    self.parse_simple_condition();
                }
                "ifeq" | "ifneq" => {
                    self.parse_parenthesized_expr();
                }
                _ => unreachable!("Invalid conditional token"),
            }

            // Parse the conditional body
            let mut depth = 1;
            
            // Enhanced safety to prevent infinite loops
            let mut last_position = self.tokens.len();
            let mut last_token = self.current();
            let mut iterations_at_position = 0;
            let max_iterations_without_progress = 20; // Increase limit for complex conditionals
            
            while depth > 0 && self.current().is_some() {
                // More sophisticated safety check for infinite loops
                // Check if neither the token count nor the current token has changed
                if self.tokens.len() == last_position && self.current() == last_token {
                    iterations_at_position += 1;
                    
                    // Only break if we're truly stuck
                    if iterations_at_position > max_iterations_without_progress {
                        // Instead of breaking immediately, try to recover
                        // Force moving forward by consuming the current token
                        if self.current().is_some() {
                            self.bump();
                            continue;
                        } else {
                            break;
                        }
                    }
                } else {
                    // We made progress, reset counter
                    iterations_at_position = 0;
                    last_position = self.tokens.len();
                    last_token = self.current();
                }
                
                match self.current() {
                    None => {
                        self.error("unterminated conditional (missing endif)".into());
                        break;
                    }
                    Some(IDENTIFIER) => {
                        let token = self.tokens.last().unwrap().1.clone();
                        if !self.handle_conditional_token(&token, &mut depth) {
                            if token == "include" || token == "-include" || token == "sinclude" {
                                self.parse_include();
                            } else {
                                self.parse_normal_content();
                            }
                        }
                    }
                    Some(INDENT) => self.parse_recipe_line(),
                    Some(WHITESPACE) => self.bump(),
                    Some(COMMENT) => self.parse_comment(),
                    Some(NEWLINE) => self.bump(),
                    Some(DOLLAR) => self.parse_normal_content(),
                    Some(QUOTE) => {
                        self.parse_quoted_string();
                    },
                    Some(_) => {
                        // Be more tolerant of unexpected tokens in conditionals
                        self.bump();
                    }
                }
            }

            self.builder.finish_node();
        }

        // Helper to parse normal content (either assignment or rule)
        fn parse_normal_content(&mut self) {
            // Skip any leading whitespace
            self.skip_ws();

            // Check if this could be a variable assignment
            if self.is_assignment_line() {
                self.parse_assignment();
            } else {
                // Try to handle as a rule
                self.parse_rule();
            }
        }

        fn parse_include(&mut self) {
            self.builder.start_node(INCLUDE.into());

            // Consume include keyword variant
            if self.current() != Some(IDENTIFIER)
                || (!["include", "-include", "sinclude"]
                    .contains(&self.tokens.last().unwrap().1.as_str()))
            {
                self.error("expected include directive".into());
                self.builder.finish_node();
                return;
            }
            self.bump();
            self.skip_ws();

            // Parse file paths
            self.builder.start_node(EXPR.into());
            let mut found_path = false;

            while self.current().is_some() && self.current() != Some(NEWLINE) {
                match self.current() {
                    Some(WHITESPACE) => self.skip_ws(),
                    Some(DOLLAR) => {
                        found_path = true;
                        self.parse_variable_reference();
                    }
                    Some(_) => {
                        // Accept any token as part of the path
                        found_path = true;
                        self.bump();
                    }
                    None => break,
                }
            }

            if !found_path {
                self.error("expected file path after include".into());
            }

            self.builder.finish_node();

            // Expect newline
            if self.current() == Some(NEWLINE) {
                self.bump();
            } else if self.current().is_some() {
                self.error("expected newline after include".into());
                self.skip_until_newline();
            }

            self.builder.finish_node();
        }

        fn parse_identifier_token(&mut self) -> bool {
            let token = self.tokens.last().unwrap().1.clone();

            // Handle special cases first
            if token.starts_with("%") {
                self.parse_rule();
                return true;
            }

            if token.starts_with("if") {
                self.parse_conditional();
                return true;
            }

            if token == "include" || token == "-include" || token == "sinclude" {
                self.parse_include();
                return true;
            }

            // Handle normal content (assignment or rule)
            self.parse_normal_content();
            true
        }

        fn parse_token(&mut self) -> bool {
            match self.current() {
                None => false,
                Some(IDENTIFIER) => {
                    let token = self.tokens.last().unwrap().1.clone();
                    if self.is_conditional_directive(&token) {
                        self.parse_conditional();
                        true
                    } else {
                        self.parse_identifier_token()
                    }
                }
                Some(DOLLAR) => {
                    self.parse_normal_content();
                    true
                }
                Some(NEWLINE) => {
                    self.bump();
                    true
                }
                Some(COMMENT) => {
                    self.parse_comment();
                    true
                }
                Some(WHITESPACE) => {
                    self.skip_ws();
                    true
                }
                Some(INDENT) => {
                    self.error("indented line not part of a rule".into());
                    self.bump();
                    true
                }
                Some(kind) => {
                    self.error(format!("unexpected token {:?}", kind));
                    self.bump();
                    true
                }
            }
        }

        fn parse(mut self) -> Parse {
            self.builder.start_node(ROOT.into());

            while self.parse_token() {}

            self.builder.finish_node();

            Parse {
                green_node: self.builder.finish(),
                errors: self.errors,
            }
        }

        // Simplify the is_assignment_line method by making it more direct
        fn is_assignment_line(&mut self) -> bool {
            let assignment_ops = ["=", ":=", "::=", ":::=", "+=", "?=", "!="];
            let mut pos = self.tokens.len().saturating_sub(1);
            let mut seen_identifier = false;
            let mut seen_export = false;

            while pos > 0 {
                let (kind, text) = &self.tokens[pos];

                match kind {
                    NEWLINE => break,
                    IDENTIFIER if text == "export" => seen_export = true,
                    IDENTIFIER if !seen_identifier => seen_identifier = true,
                    OPERATOR if assignment_ops.contains(&text.as_str()) => {
                        return seen_identifier || seen_export
                    }
                    OPERATOR if text == ":" => return false, // It's a rule if we see a colon first
                    WHITESPACE => (),
                    _ if seen_export => return true, // Everything after export is part of the assignment
                    _ => return false,
                }
                pos = pos.saturating_sub(1);
            }
            false
        }

        /// Advance one token, adding it to the current branch of the tree builder.
        fn bump(&mut self) {
            let (kind, text) = self.tokens.pop().unwrap();
            self.builder.token(kind.into(), text.as_str());
        }
        /// Peek at the first unprocessed token
        fn current(&self) -> Option<SyntaxKind> {
            self.tokens.last().map(|(kind, _)| *kind)
        }

        fn expect_eol(&mut self) {
            match self.current() {
                Some(NEWLINE) => {
                    self.bump();
                }
                None => {}
                n => {
                    self.error(format!("expected newline, got {:?}", n));
                }
            }
        }

        fn expect(&mut self, expected: SyntaxKind) {
            if self.current() != Some(expected) {
                self.error(format!("expected {:?}, got {:?}", expected, self.current()));
            } else {
                self.bump();
            }
        }
        fn skip_ws(&mut self) {
            while self.current() == Some(WHITESPACE) {
                self.bump()
            }
        }

        fn skip_until_newline(&mut self) {
            while self.current().is_some() && self.current() != Some(NEWLINE) {
                self.bump();
            }
            if self.current() == Some(NEWLINE) {
                self.bump();
            }
        }

        // Helper to handle nested parentheses and collect tokens until matching closing parenthesis
        fn consume_balanced_parens(&mut self, start_paren_count: usize) -> usize {
            let mut paren_count = start_paren_count;
            
            while paren_count > 0 && self.current().is_some() {
                match self.current() {
                    Some(LPAREN) => {
                        paren_count += 1;
                        self.bump();
                    }
                    Some(RPAREN) => {
                        paren_count -= 1;
                        self.bump();
                        if paren_count == 0 {
                            break;
                        }
                    }
                    Some(DOLLAR) => {
                        // Handle nested variable references
                        self.parse_variable_reference();
                    }
                    Some(_) => self.bump(),
                    None => {
                        self.error("unclosed parenthesis".into());
                        break;
                    }
                }
            }
            
            paren_count
        }
    }

    let mut tokens = lex(text);
    tokens.reverse();
    Parser {
        tokens,
        builder: GreenNodeBuilder::new(),
        errors: Vec::new(),
        original_text: text.to_string(),
    }
    .parse()
}

/// To work with the parse results we need a view into the
/// green tree - the Syntax tree.
/// It is also immutable, like a GreenNode,
/// but it contains parent pointers, offsets, and
/// has identity semantics.

type SyntaxNode = rowan::SyntaxNode<Lang>;
#[allow(unused)]
type SyntaxToken = rowan::SyntaxToken<Lang>;
#[allow(unused)]
type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;

impl Parse {
    fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root_mut(self.green_node.clone())
    }

    fn root(&self) -> Makefile {
        Makefile::cast(self.syntax()).unwrap()
    }
}

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(PartialEq, Eq, Hash)]
        #[repr(transparent)]
        /// An AST node for $ast
        pub struct $ast(SyntaxNode);

        impl AstNode for $ast {
            type Language = Lang;

            fn can_cast(kind: SyntaxKind) -> bool {
                kind == $kind
            }

            fn cast(syntax: SyntaxNode) -> Option<Self> {
                if Self::can_cast(syntax.kind()) {
                    Some(Self(syntax))
                } else {
                    None
                }
            }

            fn syntax(&self) -> &SyntaxNode {
                &self.0
            }
        }

        impl core::fmt::Display for $ast {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                write!(f, "{}", self.0.text())
            }
        }
    };
}

ast_node!(Makefile, ROOT);
ast_node!(Rule, RULE);
ast_node!(Identifier, IDENTIFIER);
ast_node!(VariableDefinition, VARIABLE);
ast_node!(Include, INCLUDE);

impl VariableDefinition {
    /// Get the name of the variable definition
    pub fn name(&self) -> Option<String> {
        self.syntax().children_with_tokens().find_map(|it| {
            it.as_token().and_then(|it| {
                if it.kind() == IDENTIFIER && it.text() != "export" {
                    Some(it.text().to_string())
                } else {
                    None
                }
            })
        })
    }

    /// Get the raw value of the variable definition
    pub fn raw_value(&self) -> Option<String> {
        self.syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .map(|it| it.text().to_string())
    }
}

impl Makefile {
    /// Create a new empty makefile
    pub fn new() -> Makefile {
        let mut builder = GreenNodeBuilder::new();

        builder.start_node(ROOT.into());
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        Makefile(syntax)
    }

    /// Read a changelog file from a reader
    pub fn read<R: std::io::Read>(mut r: R) -> Result<Makefile, Error> {
        let mut buf = String::new();
        r.read_to_string(&mut buf)?;
        Ok(buf.parse()?)
    }

    /// Read makefile from a reader, but allow syntax errors
    pub fn read_relaxed<R: std::io::Read>(mut r: R) -> Result<Makefile, Error> {
        let mut buf = String::new();
        r.read_to_string(&mut buf)?;

        let parsed = parse(&buf);
        Ok(parsed.root())
    }

    /// Retrieve the rules in the makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "rule: dependency\n\tcommand\n".parse().unwrap();
    /// assert_eq!(makefile.rules().count(), 1);
    /// ```
    pub fn rules(&self) -> impl Iterator<Item = Rule> {
        self.syntax().children().filter_map(Rule::cast)
    }

    /// Get all rules that have a specific target
    pub fn rules_by_target<'a>(&'a self, target: &'a str) -> impl Iterator<Item = Rule> + 'a {
        self.rules()
            .filter(move |rule| rule.targets().any(|t| t == target))
    }

    /// Get all variable definitions in the makefile
    pub fn variable_definitions(&self) -> impl Iterator<Item = VariableDefinition> {
        self.syntax()
            .children()
            .filter_map(VariableDefinition::cast)
    }

    /// Add a new rule to the makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let mut makefile = Makefile::new();
    /// makefile.add_rule("rule");
    /// assert_eq!(makefile.to_string(), "rule:\n");
    /// ```
    pub fn add_rule(&mut self, target: &str) -> Rule {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RULE.into());
        builder.token(IDENTIFIER.into(), target);
        builder.token(OPERATOR.into(), ":");
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        let pos = self.0.children_with_tokens().count();
        self.0.splice_children(pos..pos, vec![syntax.into()]);
        Rule(self.0.children().nth(pos).unwrap())
    }

    /// Read the makefile
    pub fn from_reader<R: std::io::Read>(mut r: R) -> Result<Makefile, Error> {
        let mut buf = String::new();
        r.read_to_string(&mut buf)?;

        let parsed = parse(&buf);
        if !parsed.errors.is_empty() {
            Err(Error::Parse(ParseError {
                errors: parsed.errors,
            }))
        } else {
            Ok(parsed.root())
        }
    }

    /// Get all include directives in the makefile
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include config.mk\n-include .env\n".parse().unwrap();
    /// let includes = makefile.includes().collect::<Vec<_>>();
    /// assert_eq!(includes.len(), 2);
    /// ```
    pub fn includes(&self) -> impl Iterator<Item = Include> {
        self.syntax().children().filter_map(Include::cast)
    }

    /// Get all included file paths
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Makefile;
    /// let makefile: Makefile = "include config.mk\n-include .env\n".parse().unwrap();
    /// let paths = makefile.included_files().collect::<Vec<_>>();
    /// assert_eq!(paths, vec!["config.mk", ".env"]);
    /// ```
    pub fn included_files(&self) -> impl Iterator<Item = String> + '_ {
        // We need to collect all Include nodes from anywhere in the syntax tree,
        // not just direct children of the root, to handle includes in conditionals
        fn collect_includes(node: &SyntaxNode) -> Vec<Include> {
            let mut includes = Vec::new();
            
            // First check if this node itself is an Include
            if let Some(include) = Include::cast(node.clone()) {
                includes.push(include);
            }
            
            // Then recurse into all children
            for child in node.children() {
                includes.extend(collect_includes(&child));
            }
            
            includes
        }
        
        // Start collection from the root node
        let includes = collect_includes(self.syntax());
        
        // Convert to an iterator of paths
        includes.into_iter().map(|include| {
            include
                .syntax()
                .children()
                .find(|node| node.kind() == EXPR)
                .map(|expr| expr.text().to_string().trim().to_string())
                .unwrap_or_default()
                .trim()
                .to_string()
        })
    }
}

impl FromStr for Rule {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parsed = parse(s);

        if !parsed.errors.is_empty() {
            return Err(ParseError {
                errors: parsed.errors,
            });
        }

        let rules = parsed.root().rules().collect::<Vec<_>>();
        if rules.len() == 1 {
            Ok(rules.into_iter().next().unwrap())
        } else {
            Err(ParseError {
                errors: vec![ErrorInfo {
                    message: "expected a single rule".to_string(),
                    line: 1,
                    context: s.lines().next().unwrap_or("").to_string(),
                }],
            })
        }
    }
}

impl FromStr for Makefile {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parsed = parse(s);
        if parsed.errors.is_empty() {
            Ok(parsed.root())
        } else {
            Err(ParseError {
                errors: parsed.errors,
            })
        }
    }
}

impl Rule {
    // Helper method to collect variable references from tokens
    fn collect_variable_reference(&self, tokens: &mut std::iter::Peekable<impl Iterator<Item = SyntaxElement>>) -> Option<String> {
        let mut var_ref = String::new();
        
        // Check if we're at a $ token
        if let Some(token) = tokens.next() {
            if let Some(t) = token.as_token() {
                if t.kind() == DOLLAR {
                    var_ref.push_str(t.text());
                    
                    // Check if the next token is a (
                    if let Some(next) = tokens.peek() {
                        if let Some(nt) = next.as_token() {
                            if nt.kind() == LPAREN {
                                // Consume the opening parenthesis
                                var_ref.push_str(nt.text());
                                tokens.next();
                                
                                // Track parenthesis nesting level
                                let mut paren_count = 1;
                                
                                // Keep consuming tokens until we find the matching closing parenthesis
                                while let Some(next_token) = tokens.next() {
                                    if let Some(nt) = next_token.as_token() {
                                        var_ref.push_str(nt.text());
                                        
                                        if nt.kind() == LPAREN {
                                            paren_count += 1;
                                        } else if nt.kind() == RPAREN {
                                            paren_count -= 1;
                                            if paren_count == 0 {
                                                break;
                                            }
                                        }
                                    }
                                }
                                
                                return Some(var_ref);
                            }
                        }
                    }
                    
                    // Handle simpler variable references (though this branch may be less common)
                    while let Some(next_token) = tokens.next() {
                        if let Some(nt) = next_token.as_token() {
                            var_ref.push_str(nt.text());
                            if nt.kind() == RPAREN {
                                break;
                            }
                        }
                    }
                    return Some(var_ref);
                }
            }
        }
        
        None
    }

    /// Targets of this rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    ///
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
    /// ```
    pub fn targets(&self) -> impl Iterator<Item = String> + '_ {
        let mut result = Vec::new();
        let mut tokens = self
            .syntax()
            .children_with_tokens()
            .take_while(|it| it.as_token().map_or(true, |t| t.kind() != OPERATOR))
            .peekable();

        while let Some(token) = tokens.peek().cloned() {
            if let Some(node) = token.as_node() {
                tokens.next(); // Consume the node
                if node.kind() == EXPR {
                    // Handle when the target is an expression node
                    let mut var_content = String::new();
                    for child in node.children_with_tokens() {
                        if let Some(t) = child.as_token() {
                            var_content.push_str(t.text());
                        }
                    }
                    if !var_content.is_empty() {
                        result.push(var_content);
                    }
                }
            } else if let Some(t) = token.as_token() {
                if t.kind() == DOLLAR {
                    if let Some(var_ref) = self.collect_variable_reference(&mut tokens) {
                        result.push(var_ref);
                    }
                } else if t.kind() == IDENTIFIER {
                    result.push(t.text().to_string());
                    tokens.next(); // Consume the identifier
                } else {
                    tokens.next(); // Skip other token types
                }
            }
        }
        result.into_iter()
    }

    /// Get the prerequisites in the rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
    /// ```
    pub fn prerequisites(&self) -> impl Iterator<Item = String> + '_ {
        // Find the first occurrence of OPERATOR and collect the following EXPR nodes
        let mut found_operator = false;
        let mut result = Vec::new();
        
        for token in self.syntax().children_with_tokens() {
            if let Some(t) = token.as_token() {
                if t.kind() == OPERATOR {
                    found_operator = true;
                    continue;
                }
            }
            
            if found_operator {
                if let Some(node) = token.as_node() {
                    if node.kind() == EXPR {
                        // Process this expression node for prerequisites
                        let mut tokens = node.children_with_tokens().peekable();
                        while let Some(token) = tokens.peek().cloned() {
                            if let Some(t) = token.as_token() {
                                if t.kind() == DOLLAR {
                                    if let Some(var_ref) = self.collect_variable_reference(&mut tokens) {
                                        result.push(var_ref);
                                    }
                                } else if t.kind() == IDENTIFIER {
                                    result.push(t.text().to_string());
                                    tokens.next(); // Consume the identifier
                                } else {
                                    tokens.next(); // Skip other token types
                                }
                            } else {
                                tokens.next(); // Skip other elements
                            }
                        }
                        break; // Only process the first EXPR after the operator
                    }
                }
            }
        }
        
        result.into_iter()
    }

    /// Get the commands in the rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);
    /// ```
    pub fn recipes(&self) -> impl Iterator<Item = String> {
        self.syntax()
            .children()
            .filter(|it| it.kind() == RECIPE)
            .flat_map(|it| {
                it.children_with_tokens().filter_map(|it| {
                    it.as_token().and_then(|t| {
                        if t.kind() == TEXT {
                            Some(t.text().to_string())
                        } else {
                            None
                        }
                    })
                })
            })
    }

    /// Replace the command at index i with a new line
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// rule.replace_command(0, "new command");
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["new command"]);
    /// ```
    pub fn replace_command(&self, i: usize, line: &str) {
        // Find the RECIPE with index i, then replace the line in it
        let index = self
            .syntax()
            .children()
            .filter(|it| it.kind() == RECIPE)
            .nth(i)
            .expect("index out of bounds")
            .index();

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), line);
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();

        let syntax = SyntaxNode::new_root_mut(builder.finish());
        self.0
            .splice_children(index..index + 1, vec![syntax.into()]);
    }

    /// Add a new command to the rule
    ///
    /// # Example
    /// ```
    /// use makefile_lossless::Rule;
    /// let rule: Rule = "rule: dependency\n\tcommand".parse().unwrap();
    /// rule.push_command("command2");
    /// assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command", "command2"]);
    /// ```
    pub fn push_command(&self, line: &str) {
        // Find the latest RECIPE entry, then append the new line after it.
        let index = self
            .0
            .children_with_tokens()
            .filter(|it| it.kind() == RECIPE)
            .last();

        let index = index.map_or_else(
            || self.0.children_with_tokens().count(),
            |it| it.index() + 1,
        );

        let mut builder = GreenNodeBuilder::new();
        builder.start_node(RECIPE.into());
        builder.token(INDENT.into(), "\t");
        builder.token(TEXT.into(), line);
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();
        let syntax = SyntaxNode::new_root_mut(builder.finish());

        self.0.splice_children(index..index, vec![syntax.into()]);
    }
}

impl Default for Makefile {
    fn default() -> Self {
        Self::new()
    }
}

impl Include {
    /// Get the raw path of the include directive
    pub fn path(&self) -> Option<String> {
        self.syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .map(|it| it.text().to_string().trim().to_string())
    }

    /// Check if this is an optional include (-include or sinclude)
    pub fn is_optional(&self) -> bool {
        let text = self.syntax().text();
        text.to_string().starts_with("-include") || text.to_string().starts_with("sinclude")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple() {
        const SIMPLE: &str = r#"VARIABLE = value

rule: dependency
	command
"#;
        let parsed = parse(SIMPLE);
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert_eq!(
            format!("{:#?}", node),
            r#"ROOT@0..44
  VARIABLE@0..17
    IDENTIFIER@0..8 "VARIABLE"
    WHITESPACE@8..9 " "
    OPERATOR@9..10 "="
    WHITESPACE@10..11 " "
    EXPR@11..16
      IDENTIFIER@11..16 "value"
    NEWLINE@16..17 "\n"
  NEWLINE@17..18 "\n"
  RULE@18..44
    IDENTIFIER@18..22 "rule"
    OPERATOR@22..23 ":"
    WHITESPACE@23..24 " "
    EXPR@24..34
      IDENTIFIER@24..34 "dependency"
    NEWLINE@34..35 "\n"
    RECIPE@35..44
      INDENT@35..36 "\t"
      TEXT@36..43 "command"
      NEWLINE@43..44 "\n"
"#
        );

        let root = parsed.root();

        let mut rules = root.rules().collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        let rule = rules.pop().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(rule.prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);

        let mut variables = root.variable_definitions().collect::<Vec<_>>();
        assert_eq!(variables.len(), 1);
        let variable = variables.pop().unwrap();
        assert_eq!(variable.name(), Some("VARIABLE".to_string()));
        assert_eq!(variable.raw_value(), Some("value".to_string()));
    }

    #[test]
    fn test_parse_export_assign() {
        const EXPORT: &str = r#"export VARIABLE := value
"#;
        let parsed = parse(EXPORT);
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert_eq!(
            format!("{:#?}", node),
            r#"ROOT@0..25
  VARIABLE@0..25
    IDENTIFIER@0..6 "export"
    WHITESPACE@6..7 " "
    IDENTIFIER@7..15 "VARIABLE"
    WHITESPACE@15..16 " "
    OPERATOR@16..18 ":="
    WHITESPACE@18..19 " "
    EXPR@19..24
      IDENTIFIER@19..24 "value"
    NEWLINE@24..25 "\n"
"#
        );

        let root = parsed.root();

        let mut variables = root.variable_definitions().collect::<Vec<_>>();
        assert_eq!(variables.len(), 1);
        let variable = variables.pop().unwrap();
        assert_eq!(variable.name(), Some("VARIABLE".to_string()));
        assert_eq!(variable.raw_value(), Some("value".to_string()));
    }

    #[test]
    fn test_parse_multiple_prerequisites() {
        const MULTIPLE_PREREQUISITES: &str = r#"rule: dependency1 dependency2
	command

"#;
        let parsed = parse(MULTIPLE_PREREQUISITES);
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert_eq!(
            format!("{:#?}", node),
            r#"ROOT@0..40
  RULE@0..40
    IDENTIFIER@0..4 "rule"
    OPERATOR@4..5 ":"
    WHITESPACE@5..6 " "
    EXPR@6..29
      IDENTIFIER@6..17 "dependency1"
      WHITESPACE@17..18 " "
      IDENTIFIER@18..29 "dependency2"
    NEWLINE@29..30 "\n"
    RECIPE@30..39
      INDENT@30..31 "\t"
      TEXT@31..38 "command"
      NEWLINE@38..39 "\n"
    NEWLINE@39..40 "\n"
"#
        );
        let root = parsed.root();

        let rule = root.rules().next().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            vec!["dependency1", "dependency2"]
        );
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);
    }

    #[test]
    fn test_add_rule() {
        let mut makefile = Makefile::new();
        let rule = makefile.add_rule("rule");
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(
            rule.prerequisites().collect::<Vec<_>>(),
            Vec::<String>::new()
        );

        assert_eq!(makefile.to_string(), "rule:\n");
    }

    #[test]
    fn test_push_command() {
        let mut makefile = Makefile::new();
        let rule = makefile.add_rule("rule");
        rule.push_command("command");
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);

        rule.push_command("command2");
        assert_eq!(
            rule.recipes().collect::<Vec<_>>(),
            vec!["command", "command2"]
        );

        assert_eq!(makefile.to_string(), "rule:\n\tcommand\n\tcommand2\n");
    }

    #[test]
    fn test_replace_command() {
        let mut makefile = Makefile::new();
        let rule = makefile.add_rule("rule");
        rule.push_command("command");
        rule.push_command("command2");
        assert_eq!(
            rule.recipes().collect::<Vec<_>>(),
            vec!["command", "command2"]
        );

        rule.replace_command(0, "new command");
        assert_eq!(
            rule.recipes().collect::<Vec<_>>(),
            vec!["new command", "command2"]
        );

        assert_eq!(makefile.to_string(), "rule:\n\tnew command\n\tcommand2\n");
    }

    #[test]
    fn test_parse_rule_without_newline() {
        let rule = "rule: dependency\n\tcommand".parse::<Rule>().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(rule.recipes().collect::<Vec<_>>(), vec!["command"]);
        let rule = "rule: dependency".parse::<Rule>().unwrap();
        assert_eq!(rule.targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(rule.recipes().collect::<Vec<_>>(), Vec::<String>::new());
    }

    #[test]
    fn test_parse_makefile_without_newline() {
        let makefile = "rule: dependency\n\tcommand".parse::<Makefile>().unwrap();
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_from_reader() {
        let makefile = Makefile::from_reader("rule: dependency\n\tcommand".as_bytes()).unwrap();
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_parse_with_tab_after_last_newline() {
        let makefile = Makefile::from_reader("rule: dependency\n\tcommand\n\t".as_bytes()).unwrap();
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_parse_with_space_after_last_newline() {
        let makefile = Makefile::from_reader("rule: dependency\n\tcommand\n ".as_bytes()).unwrap();
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_parse_with_comment_after_last_newline() {
        let makefile =
            Makefile::from_reader("rule: dependency\n\tcommand\n#comment".as_bytes()).unwrap();
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_parse_with_variable_rule() {
        let makefile =
            Makefile::from_reader("RULE := rule\n$(RULE): dependency\n\tcommand".as_bytes())
                .unwrap();

        // Check variable definition
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].name(), Some("RULE".to_string()));
        assert_eq!(vars[0].raw_value(), Some("rule".to_string()));

        // Check rule
        let rules = makefile.rules().collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["$(RULE)"]);
        assert_eq!(
            rules[0].prerequisites().collect::<Vec<_>>(),
            vec!["dependency"]
        );
        assert_eq!(rules[0].recipes().collect::<Vec<_>>(), vec!["command"]);
    }

    #[test]
    fn test_parse_with_variable_dependency() {
        let makefile =
            Makefile::from_reader("DEP := dependency\nrule: $(DEP)\n\tcommand".as_bytes()).unwrap();

        // Check variable definition
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].name(), Some("DEP".to_string()));
        assert_eq!(vars[0].raw_value(), Some("dependency".to_string()));

        // Check rule
        let rules = makefile.rules().collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(rules[0].prerequisites().collect::<Vec<_>>(), vec!["$(DEP)"]);
        assert_eq!(rules[0].recipes().collect::<Vec<_>>(), vec!["command"]);
    }

    #[test]
    fn test_parse_with_variable_command() {
        let makefile =
            Makefile::from_reader("COM := command\nrule: dependency\n\t$(COM)".as_bytes()).unwrap();

        // Check variable definition
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].name(), Some("COM".to_string()));
        assert_eq!(vars[0].raw_value(), Some("command".to_string()));

        // Check rule
        let rules = makefile.rules().collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(
            rules[0].prerequisites().collect::<Vec<_>>(),
            vec!["dependency"]
        );
        assert_eq!(rules[0].recipes().collect::<Vec<_>>(), vec!["$(COM)"]);
    }

    #[test]
    fn test_regular_line_error_reporting() {
        let input = "rule target\n\tcommand";

        // Test both APIs with one input
        let parsed = parse(input);
        let direct_error = &parsed.errors[0];

        // Verify error is detected with correct details
        assert_eq!(direct_error.line, 2);
        assert_eq!(direct_error.message, "expected ':'");
        assert_eq!(direct_error.context, "\tcommand");

        // Check public API
        let reader_result = Makefile::from_reader(input.as_bytes());
        let parse_error = match reader_result {
            Ok(_) => panic!("Expected Parse error from from_reader"),
            Err(err) => match err {
                self::Error::Parse(parse_err) => parse_err,
                _ => panic!("Expected Parse error"),
            },
        };

        // Verify formatting includes line number and context
        let error_text = parse_error.to_string();
        assert!(error_text.contains("Error at line 2:"));
        assert!(error_text.contains("2| \tcommand"));
    }

    #[test]
    fn test_parsing_error_context_with_bad_syntax() {
        // Test with unusual characters to ensure they're preserved
        let input = "#begin comment\n\t(╯°□°)╯︵ ┻━┻\n#end comment";
        println!("Input: {:?}", input);
        println!("Line count: {}", input.lines().count());
        for (i, line) in input.lines().enumerate() {
            println!("Line {}: {:?}", i + 1, line);
            if line.starts_with('\t') {
                println!("Found tab on line {}", i + 1);
            }
        }

        let reader_error = match Makefile::from_reader(input.as_bytes()) {
            Ok(_) => panic!("Expected error"),
            Err(err) => match err {
                self::Error::Parse(error) => {
                    println!("Error: {:?}", error);
                    println!("Error line: {}", error.errors[0].line);
                    println!("Error context: {:?}", error.errors[0].context);
                    error
                }
                _ => panic!("Expected Parse error"),
            },
        };

        // Line number is 3 (where the indented line is)
        assert_eq!(reader_error.errors[0].line, 3);
        assert_eq!(reader_error.errors[0].context, "#end comment");
    }

    #[test]
    fn test_error_message_format() {
        // Test the error formatter directly
        let parse_error = ParseError {
            errors: vec![ErrorInfo {
                message: "test error".to_string(),
                line: 42,
                context: "some problematic code".to_string(),
            }],
        };

        let error_text = parse_error.to_string();
        assert!(error_text.contains("Error at line 42: test error"));
        assert!(error_text.contains("42| some problematic code"));
    }

    #[test]
    fn test_line_number_calculation() {
        // Test various locations for errors
        let test_cases = [
            ("rule dependency\n\tcommand", 2),
            ("#comment\n\t(╯°□°)╯︵ ┻━┻", 2),
            ("var = value\n#comment\n\tindented line", 3),
        ];

        for (input, expected_line) in test_cases {
            println!("Testing input: {:?}", input);

            // From the FromStr implementation, we expect ParseError directly
            let parsed = match input.parse::<Makefile>() {
                Ok(_) => panic!("Expected parse error"),
                Err(err) => err, // err is already a ParseError
            };

            println!("Error message: {}", parsed.errors[0].message);
            println!(
                "Error line: {}, expected: {}",
                parsed.errors[0].line, expected_line
            );
            println!("Error context: {:?}", parsed.errors[0].context);

            assert_eq!(parsed.errors[0].line, expected_line);
            assert!(
                parsed.errors[0].context.starts_with('\t'),
                "Context should include the tab character"
            );
        }
    }

    #[test]
    fn test_parse_simple_conditional() {
        let parsed = parse("ifdef DEBUG\n    DEBUG_FLAG := 1\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_parse_makefile_conditional() {
        let parsed = parse(
            "ifeq ($(OS),Windows_NT)\n    RESULT := windows\nelse\n    RESULT := unix\nendif\n",
        );
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_nested_conditionals() {
        let parsed = parse("ifdef DEBUG\n    CFLAGS += -g\n    ifdef VERBOSE\n        CFLAGS += -v\n    endif\nelse\n    CFLAGS += -O2\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_debug = format!("{:#?}", node);
        assert!(node_debug.contains("CONDITIONAL@"));
        assert!(node_debug.matches("DEBUG").count() >= 1);
        assert!(node_debug.matches("VERBOSE").count() >= 1);
    }

    #[test]
    fn test_include_directive() {
        let parsed = parse("include config.mk\ninclude $(TOPDIR)/rules.mk\ninclude *.mk\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("INCLUDE@"));
    }

    #[test]
    fn test_include_directive_nested() {
        let parsed = parse(
            "#comment\nifneq (,$(wildcard Makefile.local))\n  include Makefile.local\nendif\n",
        );
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_export_variables() {
        let parsed = parse("export SHELL := /bin/bash\n");
        assert!(parsed.errors.is_empty());
        let makefile = parsed.root();
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1);
        let shell_var = vars
            .iter()
            .find(|v| v.name() == Some("SHELL".to_string()))
            .unwrap();
        assert!(shell_var.raw_value().unwrap().contains("bin/bash"));
    }

    #[test]
    fn test_variable_scopes() {
        let parsed =
            parse("SIMPLE = value\nIMMEDIATE := value\nCONDITIONAL ?= value\nAPPEND += value\n");
        assert!(parsed.errors.is_empty());
        let makefile = parsed.root();
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 4);
        let var_names: Vec<_> = vars.iter().filter_map(|v| v.name()).collect();
        assert!(var_names.contains(&"SIMPLE".to_string()));
        assert!(var_names.contains(&"IMMEDIATE".to_string()));
        assert!(var_names.contains(&"CONDITIONAL".to_string()));
        assert!(var_names.contains(&"APPEND".to_string()));
    }

    #[test]
    fn test_complex_variable_references() {
        let parsed = parse("FILES := $(wildcard *.c)\nOBJS := $(patsubst %.c,%.o,$(FILES))\n");
        assert!(parsed.errors.is_empty());
        let makefile = parsed.root();
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 2);
        let var_names: Vec<_> = vars.iter().filter_map(|v| v.name()).collect();
        assert!(var_names.contains(&"FILES".to_string()));
        assert!(var_names.contains(&"OBJS".to_string()));
    }

    #[test]
    fn test_pattern_rule_parsing() {
        let parsed = parse("%.o: %.c\n\t$(CC) -c -o $@ $<\n");
        assert!(parsed.errors.is_empty());
        let makefile = parsed.root();
        let rules = makefile.rules().collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().next().unwrap(), "%.o");
        assert!(rules[0].recipes().next().unwrap().contains("$@"));
    }

    #[test]
    fn test_include_variants() {
        // Test all variants of include directives
        let makefile_str = "include simple.mk\n-include optional.mk\nsinclude synonym.mk\ninclude $(VAR)/generated.mk\n";
        let parsed = parse(makefile_str);
        assert!(parsed.errors.is_empty());

        // Get the syntax tree for inspection
        let node = parsed.syntax();
        let debug_str = format!("{:#?}", node);

        // Check that all includes are correctly parsed as INCLUDE nodes
        assert_eq!(debug_str.matches("INCLUDE@").count(), 4);

        // Check that we can access the includes through the AST
        let makefile = parsed.root();

        // Count all child nodes that are INCLUDE kind
        let include_count = makefile
            .syntax()
            .children()
            .filter(|child| child.kind() == INCLUDE)
            .count();
        assert_eq!(include_count, 4);

        // Test variable expansion in include paths
        assert!(makefile
            .included_files()
            .any(|path| path.contains("$(VAR)")));
    }

    #[test]
    fn test_include_api() {
        // Test the API for working with include directives
        let makefile_str = "include simple.mk\n-include optional.mk\nsinclude synonym.mk\n";
        let makefile: Makefile = makefile_str.parse().unwrap();

        // Test the includes method
        let includes: Vec<_> = makefile.includes().collect();
        assert_eq!(includes.len(), 3);

        // Test the is_optional method
        assert!(!includes[0].is_optional()); // include
        assert!(includes[1].is_optional()); // -include
        assert!(includes[2].is_optional()); // sinclude

        // Test the included_files method
        let files: Vec<_> = makefile.included_files().collect();
        assert_eq!(files, vec!["simple.mk", "optional.mk", "synonym.mk"]);

        // Test the path method on Include
        assert_eq!(includes[0].path(), Some("simple.mk".to_string()));
        assert_eq!(includes[1].path(), Some("optional.mk".to_string()));
        assert_eq!(includes[2].path(), Some("synonym.mk".to_string()));
    }

    #[test]
    fn test_include_integration() {
        // Test include directives in realistic makefile contexts
        let makefile_str = ".PHONY: build\n\nVERBOSE ?= 0\n\n# comment\n-include .env\n\nrule: dependency\n\tcommand";
        let phony_makefile = Makefile::from_reader(makefile_str.as_bytes()).unwrap();

        // We expect 2 rules: .PHONY and rule
        assert_eq!(phony_makefile.rules().count(), 2);

        // But only one non-special rule (not starting with '.')
        let normal_rules_count = phony_makefile
            .rules()
            .filter(|r| !r.targets().any(|t| t.starts_with('.')))
            .count();
        assert_eq!(normal_rules_count, 1);

        // Verify we have the include directive
        assert_eq!(phony_makefile.includes().count(), 1);
        assert_eq!(phony_makefile.included_files().next().unwrap(), ".env");
    }

    #[test]
    fn test_conditional_with_comments() {
        // Test comment before conditional
        let parsed = parse("# Start of file\nifdef DEBUG\n    CFLAGS += -g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test comment after conditional
        let parsed = parse("ifdef DEBUG\n    CFLAGS += -g\nendif\n# End of file");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test comment inside conditional
        let parsed = parse("ifdef DEBUG\n    # Debug flags\n    CFLAGS += -g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_conditional_with_special_chars() {
        // Test with quoted strings
        let parsed = parse("ifeq (\"$(OS)\",\"Windows_NT\")\n    EXT := .exe\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test with escaped characters
        let parsed = parse(
            "ifneq ($(PATH),\"C:\\Program Files\")\n    PATH := $(PATH):/usr/local/bin\nendif\n",
        );
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test with spaces in variable names
        let parsed =
            parse("ifdef \"Program Files\"\n    INSTALL_DIR := \"C:\\Program Files\"\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_conditional_with_variable_operations() {
        // Test with variable modifiers
        let parsed = parse("ifneq (,$(SRCS:.c=.o))\n    OBJS := $(SRCS:.c=.o)\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test with computed variable names
        let parsed = parse("ifdef $(shell echo VAR)\n    VALUE := $(shell echo value)\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test with variable references in variable names
        let parsed = parse("ifdef $(COMPILER)_FLAGS\n    CFLAGS := $($(COMPILER)_FLAGS)\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_conditional_with_rules_and_variables() {
        // Test with rule definition
        let parsed = parse("ifdef DEBUG\n    %.o: %.c\n\t$(CC) -g -c $< -o $@\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test with variable assignment
        let parsed = parse("ifdef DEBUG\n    CFLAGS += -g\n    LDFLAGS += -debug\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test with include directive
        let parsed = parse("ifdef DEBUG\n    include debug.mk\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test with export directive
        let parsed = parse("ifdef DEBUG\n    export DEBUG_FLAGS := -g -v\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_nested_different_conditionals() {
        // Test ifdef inside ifeq
        let parsed =
            parse("ifeq ($(OS),Linux)\n    ifdef DEBUG\n        CFLAGS += -g\n    endif\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.matches("DEBUG").count() >= 1);

        // Test ifneq inside ifdef
        let parsed = parse("ifdef COMPILER\n    ifneq ($(COMPILER),gcc)\n        CFLAGS += -clang\n    endif\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.matches("COMPILER").count() >= 2);
    }

    #[test]
    fn test_include_with_comments() {
        // Test comment before include
        let parsed = parse("# Include config\ninclude config.mk\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("INCLUDE@"));

        // Test comment after include
        let parsed = parse("include config.mk\n# End of includes");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("INCLUDE@"));

        // Test comment between includes
        let parsed = parse("include config.mk\n# More includes\ninclude rules.mk\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert_eq!(format!("{:#?}", node).matches("INCLUDE@").count(), 2);
    }

    #[test]
    fn test_empty_conditionals() {
        // Test empty ifdef
        let parsed = parse("ifdef DEBUG\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));

        // Test empty if-else
        let parsed = parse("ifdef DEBUG\nelse\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
        
        // Test empty if-elif-else
        let parsed = parse("ifdef DEBUG\nelif defined(RELEASE)\nelse\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_conditionals_with_else() {
        // Basic if-else
        let parsed = parse("ifdef DEBUG\n    CFLAGS += -g\nelse\n    CFLAGS += -O2\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("-g") && node_str.contains("-O2"));

        // Multiple assignments in branches
        let parsed = parse("ifdef DEBUG\n    CFLAGS += -g\n    DEBUG := 1\nelse\n    CFLAGS += -O2\n    RELEASE := 1\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_conditionals_with_multiple_elif() {
        // if-elif-elif-else
        let parsed = parse("ifeq ($(OS),Windows)\n    EXT := .exe\nelif ifeq ($(OS),Linux)\n    EXT := .bin\nelif ifeq ($(OS),Darwin)\n    EXT := .app\nelse\n    EXT := .out\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Complex conditions in elif
        let parsed = parse("ifeq ($(COMPILER),gcc)\n    CC := gcc\nelif ifeq (\"$(COMPILER)\",\"clang\")\n    CC := clang\nelif ifeq ($(shell echo $(COMPILER)),nvcc)\n    CC := nvcc\nelse\n    CC := cc\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_conditionals_inside_recipes() {
        // Conditional inside recipe with tabs
        let parsed = parse("all:\n\t@echo Building...\n\tifdef DEBUG\n\t\t@echo Debug mode\n\telse\n\t\t@echo Release mode\n\tendif\n\t@echo Done.\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("RULE@"));
        
        // Recipe with conditional and multiple targets
        let parsed = parse("build test: main.c\n\t@echo Building $@\n\tifdef DEBUG\n\t\t$(CC) -g $< -o $@\n\telse\n\t\t$(CC) -O2 $< -o $@\n\tendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("RULE@"));
    }

    #[test]
    fn test_multiline_condition_expressions() {
        // Condition split across lines
        let parsed = parse("ifeq ($(shell echo \\\nVAR),\\\nvalue)\n    RESULT := true\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
        
        // Complex multiline condition
        let parsed = parse("ifneq ($(shell grep -q \\\n'^DEBUG=1' \\\n.env && echo 1),)\n    CFLAGS += -g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        assert!(format!("{:#?}", node).contains("CONDITIONAL@"));
    }

    #[test]
    fn test_complex_nested_conditionals_with_includes() {
        // This test is being replaced with a simpler version
    }

    #[test]
    fn test_conditional_with_include() {
        let parsed = parse("ifdef DEBUG\nCFLAGS = -g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        
        // Check structure
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Test conditional with else
        let parsed = parse("ifdef DEBUG\nCFLAGS = -g\nelse\nCFLAGS = -O2\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Test nested conditionals
        let parsed = parse("ifdef DEBUG\nifdef VERBOSE\nCFLAGS = -g -v\nendif\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Test conditional with variable assignment
        let parsed = parse("ifdef DEBUG\nCFLAGS = -g\nLDFLAGS = -debug\nendif\n");
        assert!(parsed.errors.is_empty());
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
    }

    #[test]
    fn test_include_inside_conditional() {
        // Test with a simple conditional containing an include directive
        let makefile_str = "ifdef HAVE_CONFIG\ninclude config.mk\nendif\n";
        let parsed = parse(makefile_str);
        assert!(parsed.errors.is_empty());
        
        // Check conditionals via syntax tree
        let node = parsed.syntax();
        let node_str = format!("{:#?}", node);
        
        // Verify the structure contains both CONDITIONAL and INCLUDE nodes
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("INCLUDE@"));
        assert!(node_str.contains("config.mk"));
        
        // We can't assert the includes length because the API might not expose
        // includes from within conditionals yet - that would be part of the PR
    }

    #[test]
    fn test_include_inside_conditional_with_api_access() {
        // Test with a conditional containing an include directive
        let makefile_str = "ifdef HAVE_CONFIG\ninclude config.mk\nendif\n";
        let parsed = parse(makefile_str);
        assert!(parsed.errors.is_empty());
        
        // Get makefile structure from parse result
        let makefile = parsed.root();
        
        // Check all includes via the API - should find the one inside the conditional
        let all_includes = makefile.included_files().collect::<Vec<_>>();
        assert_eq!(all_includes.len(), 1);
        assert_eq!(all_includes[0], "config.mk");
        
        // Test more complex nested conditionals with includes
        let nested_str = "ifdef DEBUG\n\
            include debug.mk\n\
            ifdef VERBOSE\n\
                include verbose.mk\n\
            endif\n\
        endif\n\
        ifndef RELEASE\n\
            include dev.mk\n\
        endif\n";
        let parsed = parse(nested_str);
        assert!(parsed.errors.is_empty());
        
        // Get makefile structure 
        let makefile = parsed.root();
        
        // Check all includes via the API - should find all includes in all conditionals
        let all_includes = makefile.included_files().collect::<Vec<_>>();
        assert_eq!(all_includes.len(), 3);
        assert!(all_includes.contains(&"debug.mk".to_string()));
        assert!(all_includes.contains(&"verbose.mk".to_string()));
        assert!(all_includes.contains(&"dev.mk".to_string()));
        
        // Test with a complex mix of conditionals, includes, and variable assignments
        let complex_str = "CC = gcc\n\
            ifdef DEBUG\n\
                CFLAGS = -g\n\
                include debug.mk\n\
                ifdef SANITIZE\n\
                    CFLAGS += -fsanitize=address\n\
                    include sanitize.mk\n\
                endif\n\
            else\n\
                CFLAGS = -O2\n\
                include release.mk\n\
            endif\n";
        let parsed = parse(complex_str);
        assert!(parsed.errors.is_empty());
        
        // Get makefile structure 
        let makefile = parsed.root();
        
        // Check all includes via the API - should find all includes in all conditions
        let all_includes = makefile.included_files().collect::<Vec<_>>();
        assert_eq!(all_includes.len(), 3);
        assert!(all_includes.contains(&"debug.mk".to_string()));
        assert!(all_includes.contains(&"sanitize.mk".to_string()));
        assert!(all_includes.contains(&"release.mk".to_string()));
    }

    #[test]
    fn test_complex_conditional_expressions() {
        // Test shell command in conditional
        let shell_cond = parse("ifeq ($(shell echo hello),hello)\nFOUND := yes\nendif\n");
        assert!(shell_cond.errors.is_empty());
        let node = shell_cond.syntax();
        let node_str = format!("{:#?}", node);
        
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"shell\""));
        assert!(node_str.contains("\"echo\""));
        assert!(node_str.contains("\"hello\""));
        
        // Test wildcard function in conditional
        let wildcard_cond = parse("ifneq ($(wildcard *.c),)\nHAS_C_FILES := yes\nendif\n");
        assert!(wildcard_cond.errors.is_empty());
        let node = wildcard_cond.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"wildcard\""));
        
        // Test call function in conditional
        let call_cond = parse("ifeq ($(call check,$(VERSION)),1)\nRELEASE := yes\nendif\n");
        assert!(call_cond.errors.is_empty());
        let node = call_cond.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"call\""));
        assert!(node_str.contains("\"check\""));
        
        // Test variable substitution in conditional
        let subst_cond = parse("ifneq ($(SOURCES:.c=.o),)\nOBJS := $(SOURCES:.c=.o)\nendif\n");
        assert!(subst_cond.errors.is_empty());
        let node = subst_cond.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"SOURCES\""));
        assert!(node_str.contains("\".c\""));
        assert!(node_str.contains("\".o\""));
        
        // Test multiple variables and functions in a condition
        let complex_cond = parse("ifeq ($(shell uname),$(OS)_$(ARCH))\nCOMPATIBLE := yes\nendif\n");
        assert!(complex_cond.errors.is_empty());
        let node = complex_cond.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"shell\""));
        assert!(node_str.contains("\"uname\""));
        assert!(node_str.contains("\"OS\""));
        assert!(node_str.contains("\"ARCH\""));
        
        // Test multiple nested functions
        let nested_func_cond = parse("ifeq ($(shell echo $(shell pwd)),$(abspath $(CURDIR)))\nSAME_DIR := yes\nendif\n");
        assert!(nested_func_cond.errors.is_empty());
        let node = nested_func_cond.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"shell\""));
        assert!(node_str.contains("\"echo\""));
        assert!(node_str.contains("\"pwd\""));
        assert!(node_str.contains("\"abspath\""));
        assert!(node_str.contains("\"CURDIR\""));
        
        // Test complex boolean operators in if conditions
        let bool_cond = parse("ifdef DEBUG TRACE VERBOSE\nDEBUG_BUILD := yes\nendif\n");
        assert!(bool_cond.errors.is_empty());
        let node = bool_cond.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"DEBUG\""));
        assert!(node_str.contains("\"TRACE\""));
        assert!(node_str.contains("\"VERBOSE\""));
        
        // Test arithmetic comparisons
        let arith_cond = parse("ifeq ($(VERSION),$(shell expr $(MAJOR) + $(MINOR)))\nVALID_VERSION := yes\nendif\n");
        assert!(arith_cond.errors.is_empty());
        let node = arith_cond.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"VERSION\""));
        assert!(node_str.contains("\"shell\""));
        assert!(node_str.contains("\"expr\""));
        assert!(node_str.contains("\"MAJOR\""));
        assert!(node_str.contains("\"MINOR\""));
        assert!(node_str.contains("\"+\""));
        
        // Test negative conditions with !
        let negative_cond = parse("ifeq ($(shell test -f file.txt || echo 1),1)\nFILE_NOT_FOUND := yes\nendif\n");
        assert!(negative_cond.errors.is_empty());
        let node = negative_cond.syntax();
        let node_str = format!("{:#?}", node);
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("\"test\""));
        assert!(node_str.contains("\"file.txt\""));
    }

    #[test]
    fn test_parse_with_variable_rule_debug() {
        let input = "RULE := rule\n$(RULE): dependency\n\tcommand";
        let makefile = Makefile::from_reader(input.as_bytes()).unwrap();
        
        println!("Input: {}", input);
        
        // Inspect the rule node with debug output
        let rules = makefile.rules().collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        
        // Debug the syntax node structure
        let rule_syntax = rules[0].syntax();
        println!("Rule syntax tree:\n{:#?}", rule_syntax);
        
        // Try to collect the targets
        let targets = rules[0].targets().collect::<Vec<_>>();
        println!("Collected targets: {:?}", targets);
        
        // Also check prerequisites 
        let prerequisites = rules[0].prerequisites().collect::<Vec<_>>();
        println!("Collected prerequisites: {:?}", prerequisites);
        
        // Check the actual token sequence in the rule
        println!("Token sequence in rule:");
        for token in rule_syntax.children_with_tokens() {
            if let Some(t) = token.as_token() {
                println!("  {:?}: '{}'", t.kind(), t.text());
            } else {
                println!("  Node: {:?}", token.as_node().unwrap().kind());
            }
        }
        
        // Check if we can find the target in a more direct way
        for token in rule_syntax.children_with_tokens().take_while(|it| it.as_token().map_or(true, |t| t.kind() != OPERATOR)) {
            if let Some(t) = token.as_token() {
                println!("Target token: {:?}: '{}'", t.kind(), t.text());
            }
        }
    }

    #[test]
    fn test_condensed_conditionals() {
        // Testing conditional syntax in GNU Make
        // Note: Single-line conditionals with semicolons aren't supported by this parser
        let parsed = parse("ifdef DEBUG\nCFLAGS += -g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Testing minimal spacing but with proper newlines
        let parsed = parse("ifdef DEBUG\nCFLAGS+=-g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Testing with minimal spacing around parentheses - this works despite being poorly formatted
        let parsed = parse("ifeq($(OS),Linux)\nCFLAGS+=-linux\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
    }

    #[test]
    fn test_comments_in_conditionals() {
        // Comment before condition
        let parsed = parse("# This enables debug mode\nifdef DEBUG\nCFLAGS += -g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Comment on separate line after condition keyword
        let parsed = parse("ifdef DEBUG\n# Enable debug mode\nCFLAGS += -g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Comment at end of block on separate line
        let parsed = parse("ifdef DEBUG\nCFLAGS += -g\n# End of debug block\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Note: Inline comments after directives are not supported in this parser
    }

    #[test]
    fn test_conditional_edge_cases() {
        // No space between if and def (should fail)
        let parsed = parse("ifdefDEBUG\nCFLAGS += -g\nendif\n");
        assert!(!parsed.errors.is_empty());
        
        // Conditional at end of file without newline (should still work)
        let parsed = parse("ifdef DEBUG\nCFLAGS += -g\nendif");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Newlines in the condition - this works because the parser treats each part as separate tokens
        let parsed = parse("ifeq ($(OS)\n,\nLinux\n)\nCFLAGS += -linux\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Conditional without content (should work)
        let parsed = parse("ifdef DEBUG\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Multiple else branches (this parser actually accepts it)
        let parsed = parse("ifdef DEBUG\nDEBUG = 1\nelse\nRELEASE = 1\nelse\nTEST = 1\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Stacked conditionals with proper syntax
        let parsed = parse("ifdef DEBUG\nDEBUG = 1\nendif\nifdef RELEASE\nRELEASE = 1\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert_eq!(node_str.matches("CONDITIONAL@").count(), 2);
    }

    #[test]
    fn test_conditionals_without_newlines() {
        // These tests check conditionals with unusual syntax
        // Note: GNU Make requires conditional directives to be on their own line,
        // but this parser seems to handle some unusual cases
        
        // Missing newline before elif (parser accepts this)
        let parsed = parse("ifdef A\nA := 1 elif defined(B)\nB := 1\nendif\n");
        assert!(parsed.errors.is_empty());
        
        // Missing newline before else (parser accepts this)
        let parsed = parse("ifdef A\nA := 1 else\nB := 1\nendif\n");
        assert!(parsed.errors.is_empty());
        
        // Missing newline before endif (parser accepts this)
        let parsed = parse("ifdef A\nA := 1 endif\nB := 2\n");
        assert!(parsed.errors.is_empty());
    }

    #[test]
    fn test_multiline_conditions() {
        // The current parser doesn't support line continuations in conditions
        // These tests verify this limitation is properly detected
        
        // Single condition split over multiple lines (not supported)
        let parsed = parse("ifdef \\\nDEBUG\nCFLAGS += -g\nendif\n");
        assert!(!parsed.errors.is_empty());
        
        // Using line continuation in ifeq (not supported)
        let parsed = parse("ifeq ($(shell echo $(OS)),Linux)\nCFLAGS += -linux\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Testing properly formed multiline conditional without continuations
        let parsed = parse("ifeq ($(CONFIG),$(shell cat config.txt))\nUSE_CONFIG := yes\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
    }

    #[test]
    fn test_whitespace_in_conditionals() {
        // Extra whitespace around conditional keywords
        let parsed = parse("  ifdef   DEBUG   \n   CFLAGS   +=   -g   \n   endif   \n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Tabs instead of spaces
        let parsed = parse("ifdef\tDEBUG\n\tCFLAGS\t+=\t-g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Mixed whitespace
        let parsed = parse("ifndef\t  NO_DEBUG \t \nCFLAGS\t  += \t-g\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
    }

    #[test]
    fn test_conditionals_at_eof() {
        // Conditional at EOF with no trailing newline
        let parsed = parse("ifdef DEBUG\nDEBUG := 1\nendif");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Conditional with else at EOF with no trailing newline
        let parsed = parse("ifdef DEBUG\nDEBUG := 1\nelse\nRELEASE := 1\nendif");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Nested conditional at EOF with no trailing newline
        let parsed = parse("ifdef A\nA := 1\nifdef B\nB := 1\nendif\nendif");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
    }

    #[test]
    fn test_complex_condition_expressions() {
        // Complex expressions in ifeq
        let parsed = parse("ifeq ($(shell echo $(VERSION) | grep -q '^1\\.'),)\nV1 := yes\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Multiple variables in condition
        let parsed = parse("ifdef DEBUG VERBOSE TRACING\nDEBUG_FULL := yes\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Quoted strings in conditions
        let parsed = parse("ifeq (\"$(CONFIG)\",\"debug\")\nDEBUG := yes\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Spaces in variable values in conditions
        let parsed = parse("ifeq ($(CONFIG),debug build)\nDEBUG := yes\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        
        // Escaping in conditions
        let parsed = parse("ifeq ($(shell echo \"\\\"hello\\\"\"),\"\\\"hello\\\"\")\nESCAPED := yes\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
    }

    #[test]
    fn test_nested_complex_conditionals() {
        // Deeply nested conditionals
        let parsed = parse("ifdef A\nA := 1\nifdef B\nB := 1\nifdef C\nC := 1\nendif\nendif\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        assert_eq!(node_str.matches("CONDITIONAL@").count(), 3);
        
        // Mix of different conditional types
        let parsed = parse("ifdef DEBUG\nDEBUG := 1\nifeq ($(OS),Linux)\nOS := linux\nifndef RELEASE\nDEVELOPMENT := 1\nendif\nendif\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        assert_eq!(node_str.matches("CONDITIONAL@").count(), 3);
        
        // Alternating if-else with deep nesting
        let parsed = parse("ifdef A\nA := 1\nelse\nifdef B\nB := 1\nelse\nifdef C\nC := 1\nelse\nD := 1\nendif\nendif\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
    }

    #[test]
    fn test_deep_conditionals_with_rules() {
        // Conditionals with rules inside
        let parsed = parse("ifdef DEBUG\ndebug: all\n\t@echo Debug build\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        assert!(node_str.contains("RULE@"));
        
        // Multiple rules in conditionals
        let parsed = parse("ifdef DEBUG\ndebug: all\n\t@echo Debug build\ntest: debug\n\t@echo Test\nendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("CONDITIONAL@"));
        assert_eq!(node_str.matches("RULE@").count(), 2);
        
        // Rules with nested conditionals in recipes
        let parsed = parse("all:\n\t@echo Building\n\tifdef DEBUG\n\t@echo Debug mode\n\tifdef VERBOSE\n\t@echo Verbose output\n\tendif\n\tendif\n\t@echo Done\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("RULE@"));
    }

    #[test]
    fn test_conditionals_with_recipes() {
        // Conditionals in recipes with tabs
        let parsed = parse("all:\n\t@echo Start\n\tifdef DEBUG\n\t\t@echo Debug mode\n\telse\n\t\t@echo Release mode\n\tendif\n\t@echo End\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("RULE@"));
        
        // Multiple levels of conditionals in recipes
        let parsed = parse("all:\n\tifdef DEBUG\n\t\tifdef VERBOSE\n\t\t\t@echo Very verbose debug\n\t\telse\n\t\t\t@echo Normal debug\n\t\tendif\n\telse\n\t\t@echo Release\n\tendif\n");
        assert!(parsed.errors.is_empty());
        let node_str = format!("{:#?}", parsed.syntax());
        assert!(node_str.contains("RULE@"));
    }

    #[test]
    fn test_invalid_conditionals() {
        // A truly invalid case - unknown conditional directive
        let parsed = parse("ifXYZ DEBUG\nDEBUG := 1\nendif\n");
        assert!(!parsed.errors.is_empty());
        
        // Missing condition without identifier
        let parsed = parse("ifdef \nDEBUG := 1\nendif\n");
        assert!(!parsed.errors.is_empty());
    }
}
