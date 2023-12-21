use std::fmt::Display;

use super::scanner::Scanner;
use bumpalo::Bump;
use ordered_float::OrderedFloat;

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

pub struct Parser<'arena, 'code> {
    scanner: Scanner<'code>,
    arena: &'arena Bump,
}

impl<'arena, 'code> Parser<'arena, 'code> {
    pub fn new(arena: &'arena Bump, scanner: Scanner<'code>) -> Parser<'arena, 'code> {
        Parser { arena, scanner }
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
