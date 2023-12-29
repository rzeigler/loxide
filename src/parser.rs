use std::fmt::Display;
use std::io::Write;
use std::iter::Peekable;

use crate::scanner::Data;
use crate::scanner::Keyword;
use crate::scanner::Pos;
use crate::scanner::Scanner;
use crate::scanner::Symbol;
use crate::scanner::Token;
use bumpalo::collections::Vec;
use bumpalo::Bump;
use ordered_float::OrderedFloat;
use thiserror::Error;

#[derive(Debug, PartialEq, Eq)]
pub struct Program<'a>(pub Vec<'a, &'a Stmt<'a>>);

#[derive(Debug, PartialEq, Eq)]
pub enum Stmt<'a> {
    Expr(&'a Expr<'a>),
    Print(&'a Expr<'a>),
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
pub struct ParseError {}

// For unwinding, we don't actually care that much about the internal cause which is reported through the reporter
#[derive(Error, Debug)]
#[error("internal parse error")]
struct InternalError {}

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
    scanner: Scanner<'src>,
) -> Result<Program<'arena>, ParseError>
where
    Reporter: ErrorReporter,
{
    let mut peekable = scanner.peekable();
    let mut reporter = StateTrackingReporter {
        reporter,
        errored: false,
    };
    if let Ok(program) = program(arena, &mut reporter, &mut peekable) {
        expect_eof(&mut reporter, &mut peekable);
        if reporter.errored {
            Err(ParseError {})
        } else {
            Ok(program)
        }
    } else {
        Err(ParseError {})
    }
}

fn expect_eof<'src, Reporter>(reporter: &mut Reporter, scanner: &mut Peekable<Scanner<'src>>)
where
    Reporter: ErrorReporter,
{
    // If we expect the eof to be at this position, but we have already exhausted the token stream that means we
    // already hit an eof unexpectedly which should have recorded an error there
    if let Some(next) = scanner.next() {
        match next {
            Ok(token) => {
                if token.data != Data::Eof {
                    reporter.report(token.pos, "expected eof");
                }
            }
            Err(e) => {
                reporter.report(e.pos, "expected eof");
            }
        }
    }
}

fn program<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<Program<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    let mut stmts = Vec::<&'arena Stmt<'arena>>::new_in(arena);
    while !is_at_eof(scanner) {
        stmts.push(stmt(arena, reporter, scanner)?);
    }
    Ok(Program(stmts))
}

fn stmt<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Stmt<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    if consume_next_keyword_eq(Keyword::Print, scanner) {
        print_stmt(arena, reporter, scanner)
    } else {
        expr_stmt(arena, reporter, scanner)
    }
}

fn print_stmt<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Stmt<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    let expr = expr(arena, reporter, scanner)?;
    consume_next_symbol_or_err(
        Symbol::Semicolon,
        "expected ';' after an expression",
        reporter,
        scanner,
    )?;
    Ok(arena.alloc(Stmt::Print(expr)))
}

fn expr_stmt<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Stmt<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    let expr = expr(arena, reporter, scanner)?;
    consume_next_symbol_or_err(
        Symbol::Semicolon,
        "expected ';' after an expression",
        reporter,
        scanner,
    )?;
    Ok(arena.alloc(Stmt::Expr(expr)))
}

fn expr<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    equality(arena, reporter, scanner)
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
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(arena, reporter, scanner, &EQUALITY_SYMBOLS, ternary)
}

fn ternary<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    let expr = comparison(arena, reporter, scanner)?;
    if consume_next_symbol_eq(Symbol::Question, scanner).is_none() {
        Ok(expr)
    } else {
        let if_true = comparison(arena, reporter, scanner)?;
        consume_next_symbol_or_err(Symbol::Colon, "expected a ':'", reporter, scanner)?;
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
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(arena, reporter, scanner, &COMPARISON_SYMBOLS, term)
}

fn term<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(arena, reporter, scanner, &TERM_SYMBOLS, factor)
}

fn factor<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(arena, reporter, scanner, &FACTOR_SYMBOLS, unary)
}

const UNARY_SYMBOLS: [Symbol; 2] = [Symbol::Minus, Symbol::Bang];

fn unary<'arena, 'src, Reporter>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    if let Some(symbol) = consume_next_symbol_from_set(&UNARY_SYMBOLS, scanner) {
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
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
{
    if let Some(result) = scanner.next() {
        match result {
            Ok(token) => {
                let expr = match token.data {
                    Data::Keyword(Keyword::True) => {
                        arena.alloc(Expr::Literal(Literal::Boolean(true)))
                    }
                    Data::Keyword(Keyword::False) => {
                        arena.alloc(Expr::Literal(Literal::Boolean(false)))
                    }
                    Data::Keyword(Keyword::Nil) => arena.alloc(Expr::Literal(Literal::Nil)),
                    Data::String(string) => {
                        let ast_string = arena.alloc_str(string);
                        arena.alloc(Expr::Literal(Literal::String(ast_string)))
                    }
                    Data::Number(number) => {
                        arena.alloc(Expr::Literal(Literal::Number(OrderedFloat(number))))
                    }
                    Data::Symbol(Symbol::LeftParen) => {
                        let inner = expr(arena, reporter, scanner)?;
                        let next_token = scanner.next();
                        if let Some(result) = next_token {
                            match result {
                                Ok(token) => {
                                    match token.data {
                                        Data::Symbol(Symbol::RightParen) => {
                                            // This is the happy path in that we have successfully matched the trailing group
                                            arena.alloc(Expr::Group(inner))
                                        }
                                        _ => {
                                            reporter.report(token.pos, "expected a ')'");
                                            return Err(InternalError {});
                                        }
                                    }
                                }
                                Err(scan_err) => {
                                    reporter.report(scan_err.pos, scan_err.error.message());
                                    return Err(InternalError {});
                                }
                            }
                        } else {
                            unreachable!("scanned past eof");
                        }
                    }
                    // An unexpected binary symbol so lets try and parse the rhs before raising the error
                    // - should be trapped by unary
                    Data::Symbol(symbol)
                        if BINARY_SYMBOLS.iter().find(|bin| **bin == symbol).is_some() =>
                    {
                        // Should this report something different?
                        reporter.report(token.pos, "binary operator without a left-hand side");
                        // result is unimportant, we are bailing anyway
                        let _rhs = expr(arena, reporter, scanner);
                        return Err(InternalError {});
                    }
                    _ => {
                        reporter.report(
                            token.pos,
                            "unexpected token: expected true, false, nil, number, string or (",
                        );
                        return Err(InternalError {});
                    }
                };
                Ok(expr)
            }
            Err(scan_err) => {
                reporter.report(scan_err.pos, scan_err.error.message());
                Err(InternalError {})
            }
        }
    } else {
        unreachable!("scanned past eof");
    }
}

// It occurs to me it might be possible to do this a single recursive call that unfolds generically
// instead of encoding the recursion in separate helpers
fn left_recursive_binary_op<'arena, 'src, Reporter, F>(
    arena: &'arena Bump,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'src>>,
    symbols: &[Symbol],
    higher_precedence: F,
) -> Result<&'arena Expr<'arena>, InternalError>
where
    Reporter: ErrorReporter,
    F: Fn(
        &'arena Bump,
        &mut Reporter,
        &mut Peekable<Scanner<'src>>,
    ) -> Result<&'arena Expr<'arena>, InternalError>,
{
    let mut expr = higher_precedence(arena, reporter, scanner)?;
    while let Some(symbol) = consume_next_symbol_from_set(symbols, scanner) {
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

// Consume and return the next token from the scanner if it is a symbol from the provided set
fn consume_next_symbol_from_set(
    set: &[Symbol],
    scanner: &mut Peekable<Scanner<'_>>,
) -> Option<Symbol> {
    let result = if let Some(token) = scanner.peek() {
        match token {
            Ok(Token {
                data: Data::Symbol(symbol),
                pos: _,
            }) if set.contains(symbol) => Some(*symbol),
            _ => None,
        }
    } else {
        unreachable!("scanned past eof")
    };
    // Consume the symbol that we peeked previously
    if result.is_some() {
        _ = scanner.next().unwrap();
    }
    result
}

// Consume and return the next token from the scanner if matches the given symbol
fn consume_next_symbol_eq(
    required_next: Symbol,
    scanner: &mut Peekable<Scanner<'_>>,
) -> Option<Symbol> {
    // TODO: Change to -> bool to align with consume_next_keyword_eq
    let result = if let Some(token) = scanner.peek() {
        match token {
            Ok(Token {
                data: Data::Symbol(symbol),
                pos: _,
            }) if required_next == *symbol => Some(*symbol),
            _ => None,
        }
    } else {
        unreachable!("scanned past eof")
    };
    // Consume the symbol that we peeked previously
    if result.is_some() {
        _ = scanner.next().unwrap();
    }
    result
}

// Consume the next token from the scanner. Error if it does not match the given input
fn consume_next_symbol_or_err<Reporter>(
    required_next: Symbol,
    err_msg: &str,
    reporter: &mut Reporter,
    scanner: &mut Peekable<Scanner<'_>>,
) -> Result<(), InternalError>
where
    Reporter: ErrorReporter,
{
    if let Some(next) = scanner.next() {
        match next {
            Ok(token) => {
                if token.data == required_next {
                    Ok(())
                } else {
                    reporter.report(token.pos, err_msg);
                    Err(InternalError {})
                }
            }
            Err(scan_err) => {
                reporter.report(scan_err.pos, scan_err.error.message());
                Err(InternalError {})
            }
        }
    } else {
        unreachable!("scanned past eof");
    }
}

fn consume_next_keyword_eq(required_next: Keyword, scanner: &mut Peekable<Scanner<'_>>) -> bool {
    scanner
        .next_if(|item| match item {
            Ok(Token { data, pos: _ }) => *data == required_next,
            _ => false,
        })
        // We only accept on the Ok branch
        .is_some()
}

fn is_at_eof(scanner: &mut Peekable<Scanner>) -> bool {
    if let Some(next) = scanner.peek() {
        match next {
            Ok(token) => token.data == Data::Eof,
            Err(_) => false,
        }
    } else {
        unreachable!("scanned past eof");
    }
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
