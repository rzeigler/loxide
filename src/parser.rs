use std::fmt::Display;
use std::iter::Peekable;

use crate::scanner::Data;
use crate::scanner::Keyword;
use crate::scanner::ScanError;
use crate::scanner::Scanner;
use crate::scanner::Symbol;
use crate::scanner::Token;
use bumpalo::Bump;
use ordered_float::OrderedFloat;
use thiserror::Error;

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

#[derive(Debug, PartialEq, Eq)]
pub enum Expr<'a> {
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
    // Maybe making this explicit will help for pretty printing
    // Grouping {  }
    Literal(Literal<'a>),
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Literal(lit) => write!(f, "{}", lit),
            Expr::Group(expr) => write!(f, "(group {})", expr),
            Expr::Unary { op, expr } => write!(f, "({} {})", op, expr),
            Expr::Binary { left, op, right } => write!(f, "({} {} {})", op, left, right),
        }
    }
}

#[derive(Error, Debug)]
#[error("parse error: {0}")]
pub struct ParseError(String);

#[derive(Error, Debug)]
enum InternalError<'code> {
    #[error("scan error: {0}")]
    ScanError(#[from] ScanError),
    #[error("token mismatch: expected {expected:?}, found {found:?}")]
    TokenMismatch {
        expected: Vec<&'static str>,
        found: Option<Token<'code>>,
    },
}

pub fn parse<'arena, 'src>(
    arena: &'arena Bump,
    scanner: Scanner<'src>,
) -> Result<&'arena Expr<'arena>, ParseError> {
    let mut peekable = scanner.peekable();
    let result = expr(arena, &mut peekable).map_err(|err| ParseError(format!("{}", err)))?;
    // Test for EOF
    if let Some(_) = peekable.next() {
        // TODO: This should provide some details about the token we hit
        return Err(ParseError(format!("expected EOF")));
    }
    Ok(result)
}

fn expr<'arena, 'src>(
    arena: &'arena Bump,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError<'src>> {
    equality(arena, scanner)
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

fn equality<'arena, 'src>(
    arena: &'arena Bump,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError<'src>> {
    left_recursive_binary_op(arena, scanner, &EQUALITY_SYMBOLS, comparison)
}

fn comparison<'arena, 'src>(
    arena: &'arena Bump,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError<'src>> {
    left_recursive_binary_op(arena, scanner, &COMPARISON_SYMBOLS, term)
}

fn term<'arena, 'src>(
    arena: &'arena Bump,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError<'src>> {
    left_recursive_binary_op(arena, scanner, &TERM_SYMBOLS, factor)
}

fn factor<'arena, 'src>(
    arena: &'arena Bump,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError<'src>> {
    left_recursive_binary_op(arena, scanner, &FACTOR_SYMBOLS, unary)
}

const UNARY_SYMBOLS: [Symbol; 2] = [Symbol::Minus, Symbol::Bang];

fn unary<'arena, 'src>(
    arena: &'arena Bump,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError<'src>> {
    if let Some(symbol) = symbol_from_set(&UNARY_SYMBOLS, scanner) {
        let operator = symbol_to_unary_op(symbol);
        let right = unary(arena, scanner)?;
        Ok(arena.alloc(Expr::Unary {
            op: operator,
            expr: right,
        }))
    } else {
        primary(arena, scanner)
    }
}

fn primary<'arena, 'src>(
    arena: &'arena Bump,
    scanner: &mut Peekable<Scanner<'src>>,
) -> Result<&'arena Expr<'arena>, InternalError<'src>> {
    // TODO: How to deal with the mismatch?
    if let Some(result) = scanner.next() {
        let token = result?;
        let expr = match token.data {
            Data::Keyword {
                keyword: Keyword::True,
            } => arena.alloc(Expr::Literal(Literal::Boolean(true))),
            Data::Keyword {
                keyword: Keyword::False,
            } => arena.alloc(Expr::Literal(Literal::Boolean(false))),
            Data::Keyword {
                keyword: Keyword::Nil,
            } => arena.alloc(Expr::Literal(Literal::Nil)),
            Data::String { string } => {
                let ast_string = arena.alloc_str(string);
                arena.alloc(Expr::Literal(Literal::String(ast_string)))
            }
            Data::Number { number } => {
                arena.alloc(Expr::Literal(Literal::Number(OrderedFloat(number))))
            }
            Data::Symbol {
                symbol: Symbol::LeftParen,
            } => {
                let inner = expr(arena, scanner)?;
                let next_token = scanner.next();
                if let Some(result) = next_token {
                    let token = result?;
                    match token.data {
                        Data::Symbol {
                            symbol: Symbol::RightParen,
                        } => {
                            // This is the happy path in that we have successfully matched the trailing group
                            arena.alloc(Expr::Group(inner))
                        }
                        _ => {
                            return Err(InternalError::TokenMismatch {
                                expected: vec![")"],
                                found: Some(token),
                            })
                        }
                    }
                } else {
                    return Err(InternalError::TokenMismatch {
                        expected: vec![")"],
                        found: None,
                    });
                }
            }
            _ => {
                return Err(InternalError::TokenMismatch {
                    // TODO: These shouldn't be strings
                    expected: vec!["true", "false", "nil", "<number>", "<string>", "("],
                    found: Some(token),
                });
            }
        };
        Ok(expr)
    } else {
        Err(InternalError::TokenMismatch {
            expected: vec!["true", "false", "nil", "<number>", "<string>", "("],
            found: None,
        })
    }
}

// It occurs to me it might be possible to do this a single recursive call that unfolds generically
// instead of encoding the recursion in separate helpers
fn left_recursive_binary_op<'arena, 'src, F>(
    arena: &'arena Bump,
    scanner: &mut Peekable<Scanner<'src>>,
    symbols: &[Symbol],
    higher_precedence: F,
) -> Result<&'arena Expr<'arena>, InternalError<'src>>
where
    F: Fn(
        &'arena Bump,
        &mut Peekable<Scanner<'src>>,
    ) -> Result<&'arena Expr<'arena>, InternalError<'src>>,
{
    let mut expr = higher_precedence(arena, scanner)?;
    while let Some(symbol) = symbol_from_set(symbols, scanner) {
        let binary_op = symbol_to_binary_op(symbol);
        let right = higher_precedence(arena, scanner)?;
        expr = arena.alloc(Expr::Binary {
            left: expr,
            op: binary_op,
            right,
        })
    }
    Ok(expr)
}

fn symbol_from_set(set: &[Symbol], scanner: &mut Peekable<Scanner<'_>>) -> Option<Symbol> {
    let result = if let Some(token) = scanner.peek() {
        match token {
            Ok(Token {
                data: Data::Symbol { symbol },
                pos: _,
            }) if set.contains(symbol) => Some(*symbol),
            _ => None,
        }
    } else {
        None
    };
    // Consume the symbol that we peeked previously
    if result.is_some() {
        _ = scanner.next().unwrap();
    }
    result
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
