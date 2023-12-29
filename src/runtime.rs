use std::{
    convert::From,
    fmt::Display,
    ops::{Add, Div, Mul, Sub},
    rc::Rc,
};

use thiserror::Error;

use crate::parser::{BinaryOp, Expr, Literal, Program, Stmt, UnaryOp};

#[derive(Error, Debug)]
pub enum RuntimeError {
    #[error("divide by zero")]
    DivideByZero,
    #[error("type error")]
    TypeError,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    String(Rc<String>),
    Number(f64),
    Bool(bool),
    Nil,
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "'{}'", s),
            Value::Number(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Nil => f.write_str("nil"),
        }
    }
}

const NAN: Value = Value::Number(f64::NAN);

// Starting here are convenience implementations to make the interpret loop easier
impl Add for Value {
    type Output = Result<Value, RuntimeError>;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l + r)),
            (Value::String(l), r) => {
                let mut new = l.as_ref().to_owned();
                new.push_str(&r.to_string());
                Ok(Value::String(Rc::new(new)))
            }
            (l, Value::String(r)) => {
                let mut new = l.to_string();
                new.push_str(r.as_str());
                Ok(Value::String(Rc::new(new)))
            }
            _ => Ok(NAN),
        }
    }
}

impl Mul for Value {
    type Output = Result<Value, RuntimeError>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l * r)),
            // TODO: Allow multiplication of strings
            _ => Ok(NAN),
        }
    }
}

impl Div for Value {
    type Output = Result<Value, RuntimeError>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => {
                if r == 0f64 {
                    Err(RuntimeError::DivideByZero)
                } else {
                    Ok(Value::Number(l / r))
                }
            }
            _ => Ok(NAN),
        }
    }
}

impl Sub for Value {
    type Output = Result<Value, RuntimeError>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l - r)),
            _ => Ok(NAN),
        }
    }
}

impl From<Value> for bool {
    fn from(value: Value) -> Self {
        match value {
            Value::Bool(b) => b,
            Value::Nil => false,
            _ => true,
        }
    }
}

pub fn interpret(expr: Program) -> Result<(), RuntimeError> {
    for stmt in expr.0 {
        execute(stmt)?;
    }
    Ok(())
}

fn execute(stmt: &Stmt) -> Result<(), RuntimeError> {
    match stmt {
        Stmt::Print(expr) => println!("{}", eval(expr)?),
        Stmt::Expr(expr) => _ = eval(expr)?,
    }
    Ok(())
}

fn eval(expr: &Expr) -> Result<Value, RuntimeError> {
    match expr {
        Expr::Ternary {
            test,
            if_true,
            if_false,
        } => {
            if eval(test)?.into() {
                eval(if_true)
            } else {
                eval(if_false)
            }
        }
        Expr::Binary { left, op, right } => {
            let lhs = eval(left)?;
            let rhs = eval(right)?;
            match op {
                BinaryOp::Equal => Ok(Value::Bool(eq(lhs, rhs))),
                BinaryOp::NotEqual => Ok(Value::Bool(!eq(lhs, rhs))),
                BinaryOp::LessThan => Ok(Value::Bool(lt(lhs, rhs))),
                // TODO: Lazy impls that clone and re-use lt and eq
                BinaryOp::LessThanEqual => {
                    Ok(Value::Bool(lt(lhs.clone(), rhs.clone()) || eq(lhs, rhs)))
                }
                BinaryOp::GreaterThan => {
                    Ok(Value::Bool(!lt(lhs.clone(), rhs.clone()) && !eq(lhs, rhs)))
                }
                BinaryOp::GreaterThanEqual => Ok(Value::Bool(!lt(lhs, rhs))),
                BinaryOp::Add => lhs + rhs,
                BinaryOp::Multiply => lhs * rhs,
                BinaryOp::Subtract => lhs - rhs,
                BinaryOp::Divide => lhs / rhs,
            }
        }
        Expr::Unary { op, expr } => {
            let val = eval(expr)?;
            match op {
                UnaryOp::Not => Ok(Value::Bool(!bool::from(val))),
                UnaryOp::Negative => Value::Number(-1f64) * val,
            }
        }
        Expr::Group(expr) => eval(expr),
        Expr::Literal(Literal::Number(f)) => Ok(Value::Number(**f)),
        Expr::Literal(Literal::String(s)) => Ok(Value::String(Rc::new(s.to_string()))),
        Expr::Literal(Literal::Boolean(b)) => Ok(Value::Bool(*b)),
        Expr::Literal(Literal::Nil) => Ok(Value::Nil),
    }
}

fn eq(lhs: Value, rhs: Value) -> bool {
    // Compare equality avoiding the NaN things
    match (lhs, rhs) {
        (Value::String(l), Value::String(r)) => l == r,
        (Value::Number(l), Value::Number(r)) => l == r,
        (Value::Bool(l), Value::Bool(r)) => l == r,
        (Value::Nil, Value::Nil) => true,
        // All type mismatches not equal
        _ => false,
    }
}

fn lt(lhs: Value, rhs: Value) -> bool {
    match (lhs, rhs) {
        (Value::String(l), Value::String(r)) => l < r,
        (Value::Number(l), Value::Number(r)) => l < r,
        _ => false,
    }
}
