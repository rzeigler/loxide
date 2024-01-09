use std::fmt::Display;
use std::io::Write;
use std::string::ParseError;

use crate::scanner::Keyword;
use crate::scanner::Pos;
use crate::scanner::Scanner;
use crate::scanner::Symbol;
use crate::scanner::Token;
use crate::scanner::TokenType;
use bumpalo::collections::Vec;
use bumpalo::Bump;
use ordered_float::OrderedFloat;
use thiserror::Error;

#[derive(Debug, PartialEq, Eq)]
pub struct Program<'a>(pub Vec<'a, &'a Stmt<'a>>);

#[derive(Debug, PartialEq, Eq)]
pub enum Stmt<'a> {
    VarDecl {
        identifier: &'a str,
        init: Option<&'a Expr<'a>>,
    },
    Expr(&'a Expr<'a>),
    Print(&'a Expr<'a>),
    Block(Vec<'a, &'a Stmt<'a>>),
    If {
        test: &'a Expr<'a>,
        if_true: &'a Stmt<'a>,
        if_false: Option<&'a Stmt<'a>>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expr<'a> {
    Ternary {
        test: &'a Expr<'a>,
        if_true: &'a Expr<'a>,
        if_false: &'a Expr<'a>,
    },
    Binary {
        left: &'a Expr<'a>,
        op: BinaryOp,
        right: &'a Expr<'a>,
    },
    Unary {
        op: UnaryOp,
        expr: &'a Expr<'a>,
    },
    Group(&'a Expr<'a>),
    Literal(Literal<'a>),
    Identifier(&'a str),
    Assignment {
        target: &'a str,
        expr: &'a Expr<'a>,
    },
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Literal(lit) => write!(f, "{}", lit),
            Expr::Group(expr) => write!(f, "(group {})", expr),
            Expr::Unary { op, expr } => write!(f, "({} {})", op, expr),
            Expr::Binary { left, op, right } => write!(f, "({} {} {})", op, left, right),
            Expr::Ternary {
                test,
                if_true,
                if_false,
            } => write!(f, "(? {} : {} {})", test, if_true, if_false),
            Expr::Identifier(id) => write!(f, "(ident {})", id),
            Expr::Assignment { target, expr } => write!(f, "(= {} {})", target, expr),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Equal,
    NotEqual,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOp::Equal => f.write_str("=="),
            BinaryOp::NotEqual => f.write_str("!="),
            BinaryOp::LessThan => f.write_str("<"),
            BinaryOp::LessThanEqual => f.write_str("<="),
            BinaryOp::GreaterThan => f.write_str(">"),
            BinaryOp::GreaterThanEqual => f.write_str(">="),
            BinaryOp::Add => f.write_str("+"),
            BinaryOp::Subtract => f.write_str("-"),
            BinaryOp::Multiply => f.write_str("*"),
            BinaryOp::Divide => f.write_str("/"),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Negative,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOp::Not => f.write_str("!"),
            UnaryOp::Negative => f.write_str("-"),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Literal<'a> {
    Number(OrderedFloat<f64>),
    String(&'a str),
    Boolean(bool),
    Nil,
}

impl<'a> Display for Literal<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Number(OrderedFloat(dbl)) => write!(f, "{}", dbl),
            Literal::String(s) => f.write_str(s),
            Literal::Boolean(b) => write!(f, "{}", b),
            Literal::Nil => f.write_str("nil"),
        }
    }
}

// Public error type that is returned from the API
#[derive(Error, Debug)]
#[error("parse error")]
pub struct Error {}

// For unwinding, we don't actually care that much about the internal cause which is reported through the reporter
#[derive(Error, Debug)]
#[error("internal parse error")]
struct ParsePanic {}

pub trait ErrorReporter {
    fn report(&mut self, pos: Pos, message: &str);
}

pub struct WriteErrorReporter<'w, W>
where
    W: Write,
{
    // Store this as a mut reference so we can't accidentally lose something like stderr().lock() inside the reporter
    // that doesn't go out of scope and cause a deadlock
    write: &'w mut W,
}

impl<'w, W> WriteErrorReporter<'w, W>
where
    W: Write,
{
    pub fn new(write: &'w mut W) -> WriteErrorReporter<'w, W> {
        WriteErrorReporter { write }
    }
}

impl<'w, W> ErrorReporter for WriteErrorReporter<'w, W>
where
    W: Write,
{
    fn report(&mut self, pos: Pos, message: &str) {
        // If w ecan't write to our output: 🤷🏻‍♂️
        _ = write!(self.write, "error at {}: {}\n", pos, message);
    }
}

/// Track whether or not an error actually occurred and delegate to another error reporter
/// This is only meant to be used internally so that parse can piggy back on whether an error actually occurred
struct StateTrackingReporter<'a, Reporter> {
    reporter: &'a mut Reporter,
    errored: bool,
}

impl<'a, Reporter> ErrorReporter for StateTrackingReporter<'a, Reporter>
where
    Reporter: ErrorReporter,
{
    fn report(&mut self, pos: Pos, message: &str) {
        self.errored = true;
        self.reporter.report(pos, message);
    }
}

pub fn parse<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    mut scanner: Scanner<'src>,
) -> Result<Program<'arena>, Error>
where
    Reporter: ErrorReporter,
{
    let mut reporter = StateTrackingReporter {
        reporter,
        errored: false,
    };
    if let Ok(program) = program(arena, &mut reporter, &mut scanner) {
        expect_eof(&mut reporter, &mut scanner);
        if reporter.errored {
            Err(Error {})
        } else {
            Ok(program)
        }
    } else {
        Err(Error {})
    }
}

fn expect_eof<'src, Reporter>(reporter: &mut Reporter, scanner: &mut Scanner<'src>)
where
    Reporter: ErrorReporter,
{
    match scanner.next() {
        // This is the success case so do nothing
        Ok(Token {
            data: TokenType::Eof,
            pos: _,
        }) => {}
        Ok(Token { data: _, pos }) => {
            reporter.report(pos, "expected eof");
        }
        Err(err) => {
            reporter.report(err.pos, "expected eof");
        }
    }
}

fn program<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Program<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let mut stmts = Vec::<&'arena Stmt<'arena>>::new_in(arena);
    while !scanner.is_at_eof() {
        match declaration(arena, reporter, scanner) {
            Ok(stmt) => stmts.push(stmt),
            Err(_) => synchronize(scanner),
        }
    }
    Ok(Program(stmts))
}

fn synchronize(scanner: &mut Scanner) {
    // Consume tokens until we have consumed a ';'
    // Avoid consuming EOF since we can abort there
    loop {
        let next = scanner.peek();
        match next {
            Ok(token) if token.data == Symbol::Semicolon => {
                _ = scanner.next().unwrap();
                break;
            }
            Ok(token) if token.data == TokenType::Eof => {
                // Leave the EOF inplace
                break;
            }
            _ => {
                // Consume the token we saw
                let _ = scanner.next().unwrap();
            }
        }
    }
}

fn declaration<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Stmt<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if scanner.next_if(|data| *data == Keyword::Var).is_some() {
        let identifier = {
            match scanner.next() {
                Ok(Token {
                    data: TokenType::Identifier(identifier),
                    pos: _,
                }) => arena.alloc_str(identifier), // Copy into the AST arena
                Ok(token) => {
                    reporter.report(token.pos, "expected an identifier");
                    return Err(ParsePanic {});
                }
                Err(err) => {
                    reporter.report(err.pos, "expected an identifier");
                    return Err(ParsePanic {});
                }
            }
        };
        let initializer = if scanner.next_if(|next| *next == Symbol::Equal).is_some() {
            Some(expr(arena, reporter, scanner)?)
        } else {
            // Generate a synthetic initializer as the constant null
            None
        };
        if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
            reporter.report(pos, "expected ';' after an expression");
            return Err(ParsePanic {});
        }
        Ok(arena.alloc(Stmt::VarDecl {
            identifier,
            init: initializer,
        }))
    } else {
        statement(arena, reporter, scanner)
    }
}

fn statement<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Stmt<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if scanner.next_if(|next| *next == Keyword::If).is_some() {
        if_stmt(arena, reporter, scanner)
    } else if scanner.next_if(|next| *next == Keyword::Print).is_some() {
        print_stmt(arena, reporter, scanner)
    } else if scanner.next_if(|next| *next == Symbol::LeftBrace).is_some() {
        block(arena, reporter, scanner)
    } else {
        expr_stmt(arena, reporter, scanner)
    }
}

fn block<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Stmt<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let mut stmts: Vec<'arena, &'arena Stmt<'arena>> = Vec::new_in(arena);
    while !scanner.is_at_eof() && !peek_matches(scanner, Symbol::RightBrace) {
        let stmt = declaration(arena, reporter, scanner)?;
        stmts.push(stmt);
    }
    if let Err(pos) = expect_next_symbol(scanner, Symbol::RightBrace) {
        reporter.report(pos, "Expected '}' after block");
        return Err(ParsePanic {});
    }
    Ok(arena.alloc(Stmt::Block(stmts)))
}

fn if_stmt<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Stmt<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if let Err(pos) = expect_next_symbol(scanner, Symbol::LeftParen) {
        reporter.report(pos, "expected '(' after if");
        return Err(ParsePanic {});
    }
    let test_expr = expr(arena, reporter, scanner)?;
    if let Err(pos) = expect_next_symbol(scanner, Symbol::RightParen) {
        reporter.report(pos, "expected ')' after if condition");
        return Err(ParsePanic {});
    }
    let then_branch = statement(arena, reporter, scanner)?;
    let else_branch = if scanner.next_if(|next| *next == Keyword::Else).is_some() {
        Some(statement(arena, reporter, scanner)?)
    } else {
        None
    };
    Ok(arena.alloc(Stmt::If {
        test: test_expr,
        if_true: then_branch,
        if_false: else_branch,
    }))
}

fn print_stmt<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Stmt<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let expr = expr(arena, reporter, scanner)?;
    if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
        reporter.report(pos, "expected ';' after an expression");
        return Err(ParsePanic {});
    }
    Ok(arena.alloc(Stmt::Print(expr)))
}

fn expr_stmt<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Stmt<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let expr = expr(arena, reporter, scanner)?;
    if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
        reporter.report(pos, "expected ';' after an expression");
        return Err(ParsePanic {});
    }
    Ok(arena.alloc(Stmt::Expr(expr)))
}

fn expr<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    assignment(arena, reporter, scanner)
}

fn assignment<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let expr = equality(arena, reporter, scanner)?;
    if let Some(eq) = scanner.next_if(|token| *token == Symbol::Equal) {
        let rhs = equality(arena, reporter, scanner)?;
        match expr {
            // A valid assignment target
            Expr::Identifier(name) => Ok(arena.alloc(Expr::Assignment {
                target: *name,
                expr: rhs,
            })),
            // Not a valid assignment target
            // Report the error to trigger top level error, but don't error out here so we continue parsing
            _ => {
                reporter.report(eq.pos, "Invalid assignment lhs");
                Ok(expr)
            }
        }
    } else {
        Ok(expr)
    }
}

// This encapsualtes the logic of the recursive parsing of levels of binary expression operators
// We define a set of matching symbols (and we have the symbol -> binary op) as well as a high precendence parser
// Observe
const EQUALITY_SYMBOLS: [Symbol; 2] = [Symbol::EqualEqual, Symbol::BangEqual];

const COMPARISON_SYMBOLS: [Symbol; 4] = [
    Symbol::Greater,
    Symbol::GreaterEqual,
    Symbol::Less,
    Symbol::LessEqual,
];

const TERM_SYMBOLS: [Symbol; 2] = [Symbol::Minus, Symbol::Plus];

const FACTOR_SYMBOLS: [Symbol; 2] = [Symbol::Star, Symbol::Slash];

// All binary symbols, This is used for error production in primary to recover when we see a binary symbol without a
// left hand operand
const BINARY_SYMBOLS: [Symbol; 10] = [
    Symbol::EqualEqual,
    Symbol::BangEqual,
    Symbol::Greater,
    Symbol::GreaterEqual,
    Symbol::Less,
    Symbol::LessEqual,
    Symbol::Minus,
    Symbol::Plus,
    Symbol::Star,
    Symbol::Slash,
];

fn equality<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(arena, reporter, scanner, &EQUALITY_SYMBOLS, ternary)
}

fn ternary<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let expr = comparison(arena, reporter, scanner)?;
    if scanner.next_if(|next| *next == Symbol::Question).is_none() {
        Ok(expr)
    } else {
        let if_true = comparison(arena, reporter, scanner)?;
        if let Err(pos) = expect_next_symbol(scanner, Symbol::Colon) {
            reporter.report(pos, "expected a ':' in ternary");
            return Err(ParsePanic {});
        }
        let if_false = comparison(arena, reporter, scanner)?;
        Ok(arena.alloc(Expr::Ternary {
            test: expr,
            if_true,
            if_false,
        }))
    }
}

fn comparison<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(arena, reporter, scanner, &COMPARISON_SYMBOLS, term)
}

fn term<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(arena, reporter, scanner, &TERM_SYMBOLS, factor)
}

fn factor<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(arena, reporter, scanner, &FACTOR_SYMBOLS, unary)
}

const UNARY_SYMBOLS: [Symbol; 2] = [Symbol::Minus, Symbol::Bang];

fn unary<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if let Some(symbol) = scanner.next_if_some(|next| match next {
        TokenType::Symbol(symbol) if UNARY_SYMBOLS.contains(&symbol) => Some(symbol),
        _ => None,
    }) {
        let operator = symbol_to_unary_op(symbol);
        let right = unary(arena, reporter, scanner)?;
        Ok(arena.alloc(Expr::Unary {
            op: operator,
            expr: right,
        }))
    } else {
        primary(arena, reporter, scanner)
    }
}

fn primary<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
{
    match scanner.next() {
        Ok(token) => {
            let expr = match token.data {
                TokenType::Keyword(Keyword::True) => {
                    arena.alloc(Expr::Literal(Literal::Boolean(true)))
                }
                TokenType::Keyword(Keyword::False) => {
                    arena.alloc(Expr::Literal(Literal::Boolean(false)))
                }
                TokenType::Keyword(Keyword::Nil) => arena.alloc(Expr::Literal(Literal::Nil)),
                TokenType::String(string) => {
                    let ast_string = arena.alloc_str(string);
                    arena.alloc(Expr::Literal(Literal::String(ast_string)))
                }
                TokenType::Number(number) => {
                    arena.alloc(Expr::Literal(Literal::Number(OrderedFloat(number))))
                }
                TokenType::Symbol(Symbol::LeftParen) => {
                    let inner = expr(arena, reporter, scanner)?;
                    match scanner.next() {
                        Ok(token) => {
                            match token.data {
                                TokenType::Symbol(Symbol::RightParen) => {
                                    // This is the happy path in that we have successfully matched the trailing group
                                    arena.alloc(Expr::Group(inner))
                                }
                                _ => {
                                    reporter.report(token.pos, "expected a ')'");
                                    return Err(ParsePanic {});
                                }
                            }
                        }
                        Err(scan_err) => {
                            reporter.report(scan_err.pos, scan_err.error.message());
                            return Err(ParsePanic {});
                        }
                    }
                }
                TokenType::Identifier(ident) => {
                    arena.alloc(Expr::Identifier(arena.alloc_str(ident)))
                }
                // An unexpected binary symbol so lets try and parse the rhs before raising the error
                // - should be trapped by unary
                TokenType::Symbol(symbol)
                    if BINARY_SYMBOLS.iter().find(|bin| **bin == symbol).is_some() =>
                {
                    // Should this report something different?
                    reporter.report(token.pos, "binary operator without a left-hand side");
                    // result is unimportant, we are bailing anyway
                    let _rhs = expr(arena, reporter, scanner);
                    return Err(ParsePanic {});
                }
                _ => {
                    reporter.report(
                        token.pos,
                        "unexpected token: expected true, false, nil, number, string or (",
                    );
                    return Err(ParsePanic {});
                }
            };
            Ok(expr)
        }
        Err(scan_err) => {
            reporter.report(scan_err.pos, scan_err.error.message());
            Err(ParsePanic {})
        }
    }
}

// It occurs to me it might be possible to do this a single recursive call that unfolds generically
// instead of encoding the recursion in separate helpers
fn left_recursive_binary_op<'arena, 'src, Reporter, F>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
    symbols: &[Symbol],
    higher_precedence: F,
) -> Result<&'arena Expr<'arena>, ParsePanic>
where
    Reporter: ErrorReporter,
    F: Fn(
        &'arena Bump,
        &mut Reporter,
        &mut Scanner<'src>,
    ) -> Result<&'arena Expr<'arena>, ParsePanic>,
{
    let mut expr = higher_precedence(arena, reporter, scanner)?;
    while let Some(symbol) = scanner.next_if_some(|next| match next {
        TokenType::Symbol(s) if symbols.contains(&s) => Some(s),
        _ => None,
    }) {
        let binary_op = symbol_to_binary_op(symbol);
        let right = higher_precedence(arena, reporter, scanner)?;
        expr = arena.alloc(Expr::Binary {
            left: expr,
            op: binary_op,
            right,
        })
    }
    Ok(expr)
}

fn symbol_to_binary_op(symbol: Symbol) -> BinaryOp {
    match symbol {
        Symbol::EqualEqual => BinaryOp::Equal,
        Symbol::BangEqual => BinaryOp::NotEqual,
        Symbol::Less => BinaryOp::LessThan,
        Symbol::LessEqual => BinaryOp::LessThanEqual,
        Symbol::Greater => BinaryOp::GreaterThan,
        Symbol::GreaterEqual => BinaryOp::GreaterThanEqual,
        Symbol::Plus => BinaryOp::Add,
        Symbol::Minus => BinaryOp::Subtract,
        Symbol::Star => BinaryOp::Multiply,
        Symbol::Slash => BinaryOp::Divide,
        s => panic!("symbol was not a valid binary operator: {}", s),
    }
}

fn symbol_to_unary_op(symbol: Symbol) -> UnaryOp {
    match symbol {
        Symbol::Bang => UnaryOp::Not,
        Symbol::Minus => UnaryOp::Negative,
        s => panic!("symbol was not a valid unary operator: {}", s),
    }
}

/// Expect that the next token from scanner is the given symbol
/// Returns the pos of the failed token (either due to error or mismatch) in Err
fn expect_next_symbol(scanner: &mut Scanner, symbol: Symbol) -> Result<(), Pos> {
    let next = scanner.next();
    match next {
        Ok(token) if token.data == symbol => Ok(()),
        Ok(token) => Err(token.pos),
        Err(err) => Err(err.pos),
    }
}

// Helper to determine if a scanner result matches a specific input
fn peek_matches<'code, A>(scanner: &mut Scanner<'code>, rhs: A) -> bool
where
    TokenType<'code>: PartialEq<A>,
{
    match scanner.peek() {
        Ok(token) => token.data == rhs,
        _ => false,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_pretty_print() {
        // (* (- 123) (group 45.67))
        let number_1 = Expr::Literal(Literal::Number(OrderedFloat(123f64)));
        let inner_1 = Expr::Unary {
            op: UnaryOp::Negative,
            expr: &number_1,
        };
        let number_2 = Expr::Literal(Literal::Number(OrderedFloat(45.67f64)));
        let inner_2 = Expr::Group(&number_2);
        let expr = Expr::Binary {
            left: &inner_1,
            op: BinaryOp::Multiply,
            right: &inner_2,
        };

        let mut result = String::new();
        std::fmt::write(&mut result, format_args!("{}", expr)).unwrap();
        assert_eq!("(* (- 123) (group 45.67))", result);
    }
}
