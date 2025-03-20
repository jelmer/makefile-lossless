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
                let tab_line = lines.iter()
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
                if self.tokens.len() > 0 && self.tokens[self.tokens.len()-1].0 == IDENTIFIER {
                    "expected ':'".to_string()
                } else {
                    "indented line not part of a rule".to_string()
                }
            } else {
                msg
            };
            
            self.errors.push(ErrorInfo { message, line, context });
            
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
                .count() + 1
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

        fn parse_rule(&mut self) {
            self.builder.start_node(RULE.into());
            self.skip_ws();
            
            // Parse rule target - either an identifier or a variable reference
            match self.current() {
                Some(IDENTIFIER) => {
                    self.bump();
                }
                Some(DOLLAR) => {
                    // Handle variable reference: $(VAR)
                    self.bump(); // Consume $
                    if self.current() == Some(LPAREN) {
                        self.bump(); // Consume (
                        // Parse everything until closing paren
                        let mut paren_depth = 1;
                        while paren_depth > 0 && self.current().is_some() {
                            match self.current() {
                                Some(LPAREN) => {
                                    paren_depth += 1;
                                    self.bump();
                                }
                                Some(RPAREN) => {
                                    paren_depth -= 1;
                                    if paren_depth > 0 {
                                        self.bump();
                                    } else {
                                        self.bump(); // Consume final )
                                    }
                                }
                                _ => self.bump(),
                            }
                        }
                    } else {
                        self.error("expected ( after $ in variable reference".into());
                    }
                }
                _ => {
                    self.error("expected rule target".into());
                }
            }
            
            // Skip whitespace and look for colon
            self.skip_ws();
            if self.current() == Some(OPERATOR) && self.tokens.last().unwrap().1 == ":" {
                self.bump(); // Consume :
            } else {
                // Test if the colon is somewhere in the token stream
                let has_colon = self.tokens.iter().rev().any(|(kind, text)| *kind == OPERATOR && text == ":");
                
                if has_colon {
                    // Continue processing, expecting to find the colon later
                    while self.current().is_some() 
                        && (self.current() != Some(OPERATOR) || self.tokens.last().unwrap().1 != ":") {
                        self.bump();
                    }
                    if self.current() == Some(OPERATOR) && self.tokens.last().unwrap().1 == ":" {
                        self.bump(); // Consume :
                    } else {
                        self.error("expected ':'".into());
                    }
                } else {
                    self.error("expected ':'".into());
                }
            }
            
            self.skip_ws();
            
            // Parse dependencies (the rest of the line)
            self.builder.start_node(EXPR.into());
            while self.current().is_some() && self.current() != Some(NEWLINE) {
                self.bump();
            }
            self.builder.finish_node();
            
            self.expect_eol();
            
            // Parse recipe lines (indented commands)
            loop {
                match self.current() {
                    Some(INDENT) => {
                        self.parse_recipe_line();
                    }
                    Some(NEWLINE) => {
                        self.bump();
                        break;
                    }
                    _ => {
                        break;
                    }
                }
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
            self.bump(); // Consume $
            if self.current() == Some(LPAREN) {
                self.bump(); // Consume (
                let mut paren_depth = 1;
                while paren_depth > 0 && self.current().is_some() {
                    match self.current() {
                        Some(LPAREN) => {
                            paren_depth += 1;
                            self.bump();
                        }
                        Some(RPAREN) => {
                            paren_depth -= 1;
                            self.bump();
                        }
                        Some(_) => self.bump(),
                        None => {
                            self.error("unclosed variable reference".into());
                            break;
                        }
                    }
                }
            } else {
                self.error("expected ( after $ in variable reference".into());
            }
        }

        fn parse_conditional(&mut self) {
            self.builder.start_node(CONDITIONAL.into());
            
            // Consume the conditional token (ifdef, ifndef, etc.)
            let token = self.tokens.last().unwrap().1.clone();
            self.bump();
            
            // Skip any whitespace after the conditional keyword
            self.skip_ws();
            
            // Process the condition part
            if token == "ifdef" || token == "ifndef" {
                // Simple variable name for ifdef/ifndef
                if self.current() == Some(IDENTIFIER) {
                    self.builder.start_node(EXPR.into());
                    self.bump();
                    self.builder.finish_node();
                } else {
                    self.error("expected variable name".into());
                }
                self.expect_eol();
            } else if token == "ifeq" || token == "ifneq" {
                // Parse parenthesized expression for ifeq/ifneq
                self.parse_parenthesized_expr();
            } else {
                self.error(format!("unknown conditional directive: {}", token));
                self.skip_until_newline();
                self.builder.finish_node();
                return;
            }
            
            // Process the conditional body
            self.parse_conditional_body();
            
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
            
            let mut paren_count = 1;
            self.bump(); // Consume opening paren
            
            while paren_count > 0 && self.current().is_some() {
                match self.current() {
                    Some(LPAREN) => {
                        paren_count += 1;
                        self.bump();
                    }
                    Some(RPAREN) => {
                        paren_count -= 1;
                        self.bump();
                    }
                    Some(_) => self.bump(),
                    None => {
                        self.error("unclosed parenthesis".into());
                        break;
                    }
                }
            }
            
            self.skip_ws();
            self.expect_eol();
            self.builder.finish_node();
        }

        // Helper method to parse conditional body (including nested conditionals)
        fn parse_conditional_body(&mut self) {
            let mut depth = 1;
            
            while depth > 0 && self.current().is_some() {
                match self.current() {
                    None => {
                        self.error("unterminated conditional (missing endif)".into());
                        break;
                    }
                    Some(IDENTIFIER) => {
                        let token = self.tokens.last().unwrap().1.clone();
                        match token.as_str() {
                            "endif" => {
                                depth -= 1;
                                self.bump();
                                self.skip_ws();
                                self.expect_eol();
                                continue;
                            }
                            "else" | "elif" if depth == 1 => {
                                self.bump();
                                if token == "elif" {
                                    self.skip_ws();
                                    match self.current() {
                                        Some(IDENTIFIER) => {
                                            self.builder.start_node(EXPR.into());
                                            self.bump();
                                            self.builder.finish_node();
                                        }
                                        Some(LPAREN) => self.parse_parenthesized_expr(),
                                        _ => self.error("expected condition after elif".into()),
                                    }
                                }
                                self.skip_ws();
                                self.expect_eol();
                                continue;
                            }
                            s if s.starts_with("if") => {
                                self.parse_conditional();
                                continue;
                            }
                            _ => self.parse_normal_content(),
                        }
                    }
                    Some(INDENT) => self.parse_recipe_line(),
                    Some(WHITESPACE) => self.bump(),
                    Some(COMMENT) => self.parse_comment(),
                    Some(NEWLINE) => self.bump(),
                    Some(DOLLAR) => self.parse_normal_content(),
                    Some(_) => {
                        self.error(format!("unexpected token in conditional block: {:?}", self.current()));
                        self.bump();
                    }
                }
            }
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
            
            // Consume 'include' keyword
            if self.current() != Some(IDENTIFIER) || self.tokens.last().unwrap().1 != "include" {
                self.error("expected 'include' keyword".into());
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

        fn parse(mut self) -> Parse {
            self.builder.start_node(ROOT.into());
            loop {
                // Skip whitespace at the beginning of the loop
                self.skip_ws();
                
                // Check if we're at EOF
                if self.current().is_none() {
                    break;
                }
                
                match self.current() {
                    // Special case for pattern rules (%.o: %.c)
                    Some(IDENTIFIER) if self.tokens.last().unwrap().1.starts_with("%") => {
                        self.parse_rule();
                    }
                    // Handle conditional directives (ifeq, ifneq, etc.)
                    Some(IDENTIFIER) if self.tokens.last().unwrap().1.starts_with("if") => {
                        self.parse_conditional();
                    }
                    // Handle include directives
                    Some(IDENTIFIER) if self.tokens.last().unwrap().1 == "include" => {
                        self.parse_include();
                    }
                    // Handle rules or variable assignments
                    Some(IDENTIFIER) => {
                        // Try to determine if it's an assignment or a rule
                        let is_assignment = self.is_assignment_line();
                        
                        if is_assignment {
                            self.parse_assignment();
                        } else {
                            self.parse_rule();
                        }
                    }
                    // Handle variable rule reference: $(VAR): ...
                    Some(DOLLAR) => {
                        // Try to determine if it's an assignment or a rule
                        let is_assignment = self.is_assignment_line();
                        
                        if is_assignment {
                            self.parse_assignment();
                        } else {
                            self.parse_rule();
                        }
                    }
                    // Handle comments, whitespace and other tokens
                    Some(NEWLINE) => {
                        self.bump();
                    }
                    Some(COMMENT) => {
                        self.parse_comment();
                    }
                    Some(INDENT) => {
                        self.error("indented line not part of a rule".into());
                        self.bump();
                    }
                    _ => {
                        // Skip any other tokens
                        self.error(format!("unexpected token {:?}", self.current()));
                        self.bump();
                    }
                }
            }
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
                    OPERATOR if assignment_ops.contains(&text.as_str()) => return seen_identifier || seen_export,
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
            Err(Error::Parse(ParseError { errors: parsed.errors }))
        } else {
            Ok(parsed.root())
        }
    }
}

impl FromStr for Rule {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parsed = parse(s);
        
        if !parsed.errors.is_empty() {
            return Err(ParseError { errors: parsed.errors });
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
                }]
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
            Err(ParseError { errors: parsed.errors })
        }
    }
}

impl Rule {
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
        let mut tokens = self.syntax()
            .children_with_tokens()
            .take_while(|it| it.as_token().map_or(true, |t| t.kind() != OPERATOR))
            .peekable();
        
        while let Some(token) = tokens.next() {
            if let Some(t) = token.as_token() {
                if t.kind() == DOLLAR {
                    // Start of a variable reference - collect all tokens until )
                    let mut var_ref = String::new();
                    var_ref.push_str(t.text());
                    
                    while let Some(next_token) = tokens.next() {
                        if let Some(nt) = next_token.as_token() {
                            var_ref.push_str(nt.text());
                            if nt.kind() == RPAREN {
                                break;
                            }
                        }
                    }
                    result.push(var_ref);
                } else if t.kind() == IDENTIFIER {
                    result.push(t.text().to_string());
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
        self.syntax()
            .children()
            .find(|it| it.kind() == EXPR)
            .into_iter()
            .flat_map(|it| {
                let mut tokens = it.children_with_tokens().peekable();
                let mut result = Vec::new();
                
                while let Some(token) = tokens.next() {
                    if let Some(t) = token.as_token() {
                        if t.kind() == DOLLAR {
                            // Start of a variable reference - collect all tokens until )
                            let mut var_ref = String::new();
                            var_ref.push_str(t.text());
                            
                            while let Some(next_token) = tokens.next() {
                                if let Some(nt) = next_token.as_token() {
                                    var_ref.push_str(nt.text());
                                    if nt.kind() == RPAREN {
                                        break;
                                    }
                                }
                            }
                            result.push(var_ref);
                        } else if t.kind() == IDENTIFIER {
                            result.push(t.text().to_string());
                        }
                    }
                }
                result.into_iter()
            })
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

        assert_eq!(makefile.to_string(), "rule:\n\tcommand\n");

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
        let makefile = Makefile::from_reader("rule: dependency\n\tcommand\n#comment".as_bytes()).unwrap();
        assert_eq!(makefile.rules().count(), 1);
    }

    #[test]
    fn test_parse_with_variable_rule() {
        let makefile = Makefile::from_reader("RULE := rule\n$(RULE): dependency\n\tcommand".as_bytes()).unwrap();
        
        // Check variable definition
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].name(), Some("RULE".to_string()));
        assert_eq!(vars[0].raw_value(), Some("rule".to_string()));
        
        // Check rule
        let rules = makefile.rules().collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["$(RULE)"]);
        assert_eq!(rules[0].prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
        assert_eq!(rules[0].recipes().collect::<Vec<_>>(), vec!["command"]);
    }

    #[test]
    fn test_parse_with_variable_dependency() {
        let makefile = Makefile::from_reader("DEP := dependency\nrule: $(DEP)\n\tcommand".as_bytes()).unwrap();
        
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
        let makefile = Makefile::from_reader("COM := command\nrule: dependency\n\t$(COM)".as_bytes()).unwrap();
        
        // Check variable definition
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].name(), Some("COM".to_string()));
        assert_eq!(vars[0].raw_value(), Some("command".to_string()));
        
        // Check rule
        let rules = makefile.rules().collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].targets().collect::<Vec<_>>(), vec!["rule"]);
        assert_eq!(rules[0].prerequisites().collect::<Vec<_>>(), vec!["dependency"]);
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
            Err(err) => {
                match err {
                    self::Error::Parse(parse_err) => parse_err,
                    _ => panic!("Expected Parse error"),
                }
            }
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
            println!("Line {}: {:?}", i+1, line);
            if line.starts_with('\t') {
                println!("Found tab on line {}", i+1);
            }
        }
        
        let reader_error = match Makefile::from_reader(input.as_bytes()) {
            Ok(_) => panic!("Expected error"),
            Err(err) => {
                match err {
                    self::Error::Parse(error) => {
                        println!("Error: {:?}", error);
                        println!("Error line: {}", error.errors[0].line);
                        println!("Error context: {:?}", error.errors[0].context);
                        error
                    },
                    _ => panic!("Expected Parse error"),
                }
            }
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
            }]
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
                Err(err) => err  // err is already a ParseError
            };
            
            println!("Error message: {}", parsed.errors[0].message);
            println!("Error line: {}, expected: {}", parsed.errors[0].line, expected_line);
            println!("Error context: {:?}", parsed.errors[0].context);
            
            assert_eq!(parsed.errors[0].line, expected_line);
            assert!(parsed.errors[0].context.starts_with('\t'), 
                    "Context should include the tab character");
        }
    }

    #[test]
    fn test_parse_small_makefile() {
        const SMALL: &str = r#"
# tool macros
CXX := g++
CXXFLAGS :=
DBGFLAGS := -g
CCOBJFLAGS := $(CXXFLAGS) -c

# path macros
BIN_PATH := bin
OBJ_PATH := obj
SRC_PATH := src
DBG_PATH := debug

project_name := makefile-template

# compile macros
TARGET_NAME := main
ifeq ($(OS),Windows_NT)
	TARGET_NAME := $(addsuffix .exe,$(TARGET_NAME))
endif
TARGET := $(BIN_PATH)/$(TARGET_NAME)
TARGET_DEBUG := $(DBG_PATH)/$(TARGET_NAME)

# src files & obj files
SRC := $(foreach x, $(SRC_PATH), $(wildcard $(addprefix $(x)/*,.c*)))
OBJ := $(addprefix $(OBJ_PATH)/, $(addsuffix .o, $(notdir $(basename $(SRC)))))
OBJ_DEBUG := $(addprefix $(DBG_PATH)/, $(addsuffix .o, $(notdir $(basename $(SRC)))))

# clean files list
DISTCLEAN_LIST := $(OBJ) \
                  $(OBJ_DEBUG)
CLEAN_LIST := $(TARGET) \
			  $(TARGET_DEBUG) \
			  $(DISTCLEAN_LIST)

# default rule
default: makedir all

builder-build :
	docker build -f builder.Dockerfile -t $(project_name)-builder:latest .

builder-run :
	docker run \
		--rm \
		-it \
		--platform linux/amd64 \
		--workdir /builder/mnt \
		-v ${PWD}:/builder/mnt \
		$(project_name)-builder:latest \
		/bin/bash


# non-phony targets
$(TARGET): $(OBJ)
	$(CXX) $(CXXFLAGS) -o $@ $(OBJ)

$(OBJ_PATH)/%.o: $(SRC_PATH)/%.c*
	$(CXX) $(CCOBJFLAGS) -o $@ $<

$(DBG_PATH)/%.o: $(SRC_PATH)/%.c*
	$(CXX) $(CCOBJFLAGS) $(DBGFLAGS) -o $@ $<

$(TARGET_DEBUG): $(OBJ_DEBUG)
	$(CXX) $(CXXFLAGS) $(DBGFLAGS) $(OBJ_DEBUG) -o $@

# phony rules
.PHONY: makedir
makedir:
	@mkdir -p $(BIN_PATH) $(OBJ_PATH) $(DBG_PATH)

.PHONY: all
all: $(TARGET)

.PHONY: debug
debug: $(TARGET_DEBUG)

.PHONY: clean
clean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -f $(CLEAN_LIST)

.PHONY: distclean
distclean:
	@echo CLEAN $(CLEAN_LIST)
	@rm -f $(DISTCLEAN_LIST)
"#;
        let parsed = parse(SMALL);
        if !parsed.errors.is_empty() {
            println!("Found {} errors in small makefile test:", parsed.errors.len());
            for (i, err) in parsed.errors.iter().enumerate() {
                println!("Error {}: line {} - {}", i+1, err.line, err.message);
                println!("Context: {}", err.context);
            }
        }
        assert!(parsed.errors.is_empty());
    }

    #[test]
    fn test_parse_medium_makefile() {
        const SMALL: &str = r#"
# target macros
TARGET := medium.exe
MAIN_SRC := main.cpp

# compile macros
DIRS := src1 src2 src3
OBJS := main.o

# intermedia compile macros
ALL_OBJS := $(OBJS)
CLEAN_FILES := $(TARGET) $(OBJS)
DIST_CLEAN_FILES := $(OBJS)

# recursive wildcard
rwildcard=$(foreach d,$(wildcard $(addsuffix *,$(1))),$(call rwildcard,$(d)/,$(2))$(filter $(subst *,%,$(2)),$(d)))

# default target
default: show-info all

# non-phony targets
$(TARGET): build-subdirs $(OBJS) find-all-objs
	@echo -e "\t" CXX $(CXXFLAGS) $(ALL_OBJS) -o $@
	@$(CXX) $(CXXFLAGS) $(ALL_OBJS) -o $@

# phony targets
.PHONY: all
all: $(TARGET)

.PHONY: clean
clean: clean-subdirs
	@echo CLEAN $(CLEAN_FILES)
	@rm -f $(CLEAN_FILES)

.PHONY: distclean
distclean: clean-subdirs
	@echo CLEAN $(DIST_CLEAN_FILES)
	@rm -f $(DIST_CLEAN_FILES)

# phony funcs
.PHONY: find-all-objs
find-all-objs:
	$(eval ALL_OBJS += $(call rwildcard,$(DIRS),*.o))

.PHONY: show-info
show-info:
	@echo Building Project

# need to be placed at the end of the file
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
export PROJECT_PATH := $(patsubst %/,%,$(dir $(mkfile_path)))
export MAKE_INCLUDE=$(PROJECT_PATH)/config/make.global
export SUB_MAKE_INCLUDE=$(PROJECT_PATH)/config/submake.global
include $(MAKE_INCLUDE)
"#;
        let parsed = parse(SMALL);
        assert!(parsed.errors.is_empty());

    }

    #[test]
    fn test_parse_sphinx_makefile() {
        const SMALL: &str = r#"
# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = sphinx-build
SOURCEDIR     = docs
BUILDDIR      = build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
"#;
        let parsed = parse(SMALL);
        assert!(parsed.errors.is_empty());
    }

    #[test]
    fn test_parse_ohmyzsh_makefile() {
        const SMALL: &str = r#"
NAME=zsh-navigation-tools

INSTALL?=install -c
PREFIX?=/usr/local
SHARE_DIR?=$(DESTDIR)$(PREFIX)/share/$(NAME)
DOC_DIR?=$(DESTDIR)$(PREFIX)/share/doc/$(NAME)

all:

install:
	$(INSTALL) -d $(SHARE_DIR)
	$(INSTALL) -d $(SHARE_DIR)/.config
	$(INSTALL) -d $(SHARE_DIR)/.config/znt
	$(INSTALL) -d $(DOC_DIR)
	cp zsh-navigation-tools.plugin.zsh _n-kill doc/znt-tmux.zsh $(SHARE_DIR)
	cp README.md NEWS LICENSE doc/img/n-history2.png $(DOC_DIR)
	if [ x"true" = x"`git rev-parse --is-inside-work-tree 2>/dev/null`" ]; then \
		git rev-parse HEAD; \
	else \
		cat .revision-hash; \
	fi > $(SHARE_DIR)/.revision-hash
	:
	for fname in n-*; do cp "$$fname" $(SHARE_DIR); done; \
	for fname in znt-*; do cp "$$fname" $(SHARE_DIR); done; \
	for fname in .config/znt/n-*; do cp "$$fname" $(SHARE_DIR)/.config/znt; done;

uninstall:
	rm -f $(SHARE_DIR)/.revision-hash $(SHARE_DIR)/_* $(SHARE_DIR)/zsh-* $(SHARE_DIR)/n-* $(SHARE_DIR)/znt-*
	[ -d $(SHARE_DIR)/.config/znt ] && rmdir $(SHARE_DIR)/.config/znt || true
	[ -d $(SHARE_DIR)/.config ] && rmdir $(SHARE_DIR)/.config || true
	[ -d $(SHARE_DIR) ] && rmdir $(SHARE_DIR) || true
	rm -f $(DOC_DIR)/README.md $(DOC_DIR)/LICENSE $(DOC_DIR)/n-history2.png 
	[ -d $(DOC_DIR) ] && rmdir $(DOC_DIR) || true

.PHONY: all install uninstall
"#;
        let parsed = parse(SMALL);
        assert!(parsed.errors.is_empty());
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
        let parsed = parse("ifeq ($(OS),Windows_NT)\n    RESULT := windows\nelse\n    RESULT := unix\nendif\n");
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
    fn test_export_variables() {
        let parsed = parse("export SHELL := /bin/bash\n");
        assert!(parsed.errors.is_empty());
        let makefile = parsed.root();
        let vars = makefile.variable_definitions().collect::<Vec<_>>();
        assert_eq!(vars.len(), 1);
        let shell_var = vars.iter().find(|v| v.name() == Some("SHELL".to_string())).unwrap();
        assert!(shell_var.raw_value().unwrap().contains("bin/bash"));
    }
    
    #[test]
    fn test_variable_scopes() {
        let parsed = parse("SIMPLE = value\nIMMEDIATE := value\nCONDITIONAL ?= value\nAPPEND += value\n");
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
}
