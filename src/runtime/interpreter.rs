use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    io::{self},
    num::ParseFloatError,
    ops::{Add, Div, Mul, Sub},
    rc::Rc,
};

use thiserror::Error;

use super::callable::Callable;
use crate::parser::{BinaryOp, Expr, Literal, LogicalOp, Program, Stmt, UnaryOp};

#[derive(Error, Debug)]
pub enum RuntimeError {
    #[error("divide by zero")]
    DivideByZero,
    #[error("type error")]
    TypeError,
    #[error("undefined variable: {0}")]
    UnboundVariable(String),
    #[error("uninitialized variable: {0}")]
    UninitializedVariable(String),
    #[error("break outside of a loop")]
    InvalidBreak,
    #[error("not callable: {0}")]
    NotCallable(String),
    #[error("arity mismatch: {0}")]
    ArityMismatch(String),
    #[error("number format error: {0}")]
    NumberFormat(#[from] ParseFloatError),
    #[error("io error: {0}")]
    IOError(#[from] io::Error),
}

pub enum UnwindCause {
    Error(RuntimeError),
    Break,
}

#[derive(Clone)]
pub enum Value {
    String(Rc<String>),
    Number(f64),
    Bool(bool),
    Callable(Rc<dyn Callable>),
    Nil,
}

impl Value {
    fn to_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Nil => false,
            _ => true,
        }
    }

    fn to_callable(&self) -> Option<&dyn Callable> {
        match self {
            Self::Callable(callable) => Some(callable.as_ref()),
            _ => None,
        }
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "Value::String('{}')", s),
            Value::Number(n) => write!(f, "Value::Number({})", n),
            Value::Bool(b) => write!(f, "Value::Bool({})", b),
            Value::Nil => f.write_str("Value::Nil"),
            Value::Callable(func) => write!(f, "Value::Callable({})", func.name()),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "'{}'", s),
            Value::Number(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Nil => f.write_str("nil"),
            Value::Callable(func) => write!(f, "{}", func.name()),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::String(left), Self::String(right)) => left == right,
            (Self::Number(left), Self::Number(right)) => left == right,
            (Self::Bool(left), Self::Bool(right)) => left == right,
            (Self::Nil, Self::Nil) => true,
            // Maybe these should check or something
            (Self::Callable(_), Self::Callable(_)) => false,
            _ => false,
        }
    }
}

const NAN: Value = Value::Number(f64::NAN);

// Starting here are convenience implementations to make the interpret loop easier
impl Add for Value {
    type Output = Result<Value, UnwindCause>;

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
    type Output = Result<Value, UnwindCause>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l * r)),
            // TODO: Allow multiplication of strings
            _ => Ok(NAN),
        }
    }
}

impl Div for Value {
    type Output = Result<Value, UnwindCause>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => {
                if r == 0f64 {
                    Err(UnwindCause::Error(RuntimeError::DivideByZero))
                } else {
                    Ok(Value::Number(l / r))
                }
            }
            _ => Ok(NAN),
        }
    }
}

impl Sub for Value {
    type Output = Result<Value, UnwindCause>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l - r)),
            _ => Ok(NAN),
        }
    }
}

type Environment = HashMap<String, Option<Value>>;

pub struct Interpreter {
    // None indicates that the variable is defined by not yet initialized
    global_env: Environment,
    context_envs: Vec<Environment>,
}

impl Interpreter {
    pub fn new_with_global(global_env: Environment) -> Interpreter {
        Interpreter {
            global_env,
            context_envs: Vec::new(),
        }
    }

    pub fn interpret(&mut self, expr: Program) -> Result<(), RuntimeError> {
        for stmt in expr.0 {
            self.execute(stmt).map_err(|err| match err {
                UnwindCause::Break => RuntimeError::InvalidBreak,
                UnwindCause::Error(err) => err,
            })?;
        }
        Ok(())
    }

    pub fn interpret_one(&mut self, stmt: &Stmt) -> Result<Value, RuntimeError> {
        self.execute(stmt).map_err(|err| match err {
            UnwindCause::Break => RuntimeError::InvalidBreak,
            UnwindCause::Error(err) => err,
        })
    }

    fn execute(&mut self, stmt: &Stmt) -> Result<Value, UnwindCause> {
        match stmt {
            Stmt::VarDecl { identifier, init } => {
                if let Some(expr) = init {
                    let v = self.eval(expr)?;
                    if let Some(top) = self.context_envs.last_mut() {
                        top.insert(identifier.to_string(), Some(v.clone()));
                    } else {
                        self.global_env
                            .insert(identifier.to_string(), Some(v.clone()));
                    }
                    Ok(v)
                } else {
                    if let Some(top) = self.context_envs.last_mut() {
                        top.insert(identifier.to_string(), None);
                    } else {
                        self.global_env.insert(identifier.to_string(), None);
                    }
                    Ok(Value::Nil)
                }
            }
            Stmt::Print(expr) => {
                println!("{}", self.eval(expr)?);
                Ok(Value::Nil)
            }
            Stmt::Expr(expr) => self.eval(expr),
            Stmt::Block(stmts) => {
                self.context_envs.push(HashMap::new());
                let result = self.execute_block(stmts);
                self.context_envs.pop();
                if let Err(e) = result {
                    return Err(e);
                }
                Ok(Value::Nil)
            }
            Stmt::If {
                expr: test,
                then: if_true,
                or_else: if_false,
            } => {
                let if_value = self.eval(test)?;
                match if_value {
                    Value::Bool(true) => {
                        self.execute(&if_true)?;
                        Ok(Value::Nil)
                    }
                    Value::Bool(false) => {
                        if let Some(false_stmt) = if_false {
                            self.execute(false_stmt)?;
                            Ok(Value::Nil)
                        } else {
                            Ok(Value::Nil)
                        }
                    }
                    _ => Err(UnwindCause::Error(RuntimeError::TypeError)),
                }
            }
            Stmt::Loop { expr, body } => {
                while self.eval(expr)?.to_bool() {
                    match self.execute(&body) {
                        Err(UnwindCause::Break) => {
                            break;
                        }
                        Err(e) => return Err(e),
                        _ => {}
                    }
                }
                Ok(Value::Nil)
            }
            Stmt::Break => Err(UnwindCause::Break),
            Stmt::FunDecl {
                name,
                parameters,
                body,
            } => todo!(),
        }
    }

    fn execute_block(
        &mut self,
        stmts: &bumpalo::collections::Vec<&Stmt>,
    ) -> Result<(), UnwindCause> {
        for stmt in stmts {
            self.execute(stmt)?;
        }
        Ok(())
    }

    fn eval(&mut self, expr: &Expr) -> Result<Value, UnwindCause> {
        match expr {
            Expr::Ternary {
                test,
                if_true,
                if_false,
            } => {
                if self.eval(test)?.to_bool() {
                    self.eval(if_true)
                } else {
                    self.eval(if_false)
                }
            }
            Expr::Binary { left, op, right } => {
                let lhs = self.eval(left)?;
                let rhs = self.eval(right)?;
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
                let val = self.eval(expr)?;
                match op {
                    UnaryOp::Not => Ok(Value::Bool(!val.to_bool())),
                    UnaryOp::Negative => Value::Number(-1f64) * val,
                }
            }
            Expr::Group(expr) => self.eval(expr),
            Expr::Literal(Literal::Number(f)) => Ok(Value::Number(**f)),
            Expr::Literal(Literal::String(s)) => Ok(Value::String(Rc::new(s.to_string()))),
            Expr::Literal(Literal::Boolean(b)) => Ok(Value::Bool(*b)),
            Expr::Literal(Literal::Nil) => Ok(Value::Nil),
            Expr::Identifier(ident) => self.lookup_value(ident),
            Expr::Assignment { target, expr } => {
                let value = self.eval(expr)?;
                self.assign_value(target, value.clone())?;
                Ok(value)
            }
            // We do this to support coallescing like behavior such as javascript has i.e. false || "a" should eval to "a"
            Expr::Logical {
                left,
                op: LogicalOp::And,
                right,
            } => {
                let left_val = self.eval(left)?;
                if left_val.to_bool() {
                    self.eval(right)
                } else {
                    Ok(left_val)
                }
            }
            Expr::Logical {
                left,
                op: LogicalOp::Or,
                right,
            } => {
                let left_val = self.eval(left)?;
                if left_val.to_bool() {
                    Ok(left_val)
                } else {
                    self.eval(right)
                }
            }
            Expr::Call { callee, arguments } => {
                let callee = self.eval(callee)?;
                let args = arguments
                    .iter()
                    .map(|expr| self.eval(expr))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(callable) = callee.to_callable() {
                    if args.len() != callable.arity().into() {
                        Err(UnwindCause::Error(RuntimeError::ArityMismatch(
                            callee.to_string(),
                        )))
                    } else {
                        callable.call(self, args).map_err(|e| UnwindCause::Error(e))
                    }
                } else {
                    return Err(UnwindCause::Error(RuntimeError::NotCallable(
                        callee.to_string(),
                    )));
                }
            }
        }
    }

    fn lookup_value(&self, identifier: &str) -> Result<Value, UnwindCause> {
        for context in self.context_envs.iter().rev() {
            if let Some(value) = context.get(identifier) {
                let v = value.clone().ok_or(UnwindCause::Error(
                    RuntimeError::UninitializedVariable(identifier.to_string()),
                ))?;
                return Ok(v);
            }
        }
        self.global_env
            .get(identifier)
            .cloned()
            .ok_or(UnwindCause::Error(RuntimeError::UnboundVariable(
                identifier.to_string(),
            )))
            .and_then(|inner| {
                inner.ok_or(UnwindCause::Error(RuntimeError::UninitializedVariable(
                    identifier.to_string(),
                )))
            })
    }

    fn assign_value(&mut self, target: &str, value: Value) -> Result<(), UnwindCause> {
        for context in self.context_envs.iter_mut().rev() {
            if let Some(lvalue) = context.get_mut(target) {
                *lvalue = Some(value);
                return Ok(());
            }
        }

        let lvalue = self.global_env.get_mut(target).ok_or(UnwindCause::Error(
            RuntimeError::UnboundVariable(target.to_string()),
        ))?;
        *lvalue = Some(value);
        Ok(())
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
