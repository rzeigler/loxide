use std::{
    collections::HashMap,
    fmt::Display,
    ops::{Add, Div, Mul, Sub},
    rc::Rc,
};

use thiserror::Error;

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
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    String(Rc<String>),
    Number(f64),
    Bool(bool),
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

type Environment = HashMap<String, Option<Value>>;

pub struct Interpreter {
    // None indicates that the variable is defined by not yet initialized
    global_memory: Environment,
}

impl Interpreter {
    pub fn new() -> Interpreter {
        Interpreter {
            global_memory: Environment::new(),
        }
    }

    pub fn interpret(&mut self, expr: Program) -> Result<(), RuntimeError> {
        let mut context_stack = Vec::<Environment>::new();
        for stmt in expr.0 {
            self.execute(&mut context_stack, stmt)?;
        }
        Ok(())
    }

    pub fn interpret_one(&mut self, stmt: &Stmt) -> Result<Value, RuntimeError> {
        let mut context_stack = Vec::<Environment>::new();
        self.execute(&mut context_stack, stmt)
    }

    fn execute(
        &mut self,
        context_stack: &mut Vec<Environment>,
        stmt: &Stmt,
    ) -> Result<Value, RuntimeError> {
        match stmt {
            Stmt::VarDecl { identifier, init } => {
                if let Some(expr) = init {
                    let v = self.eval(context_stack, expr)?;
                    if let Some(top) = context_stack.last_mut() {
                        top.insert(identifier.to_string(), Some(v.clone()));
                    } else {
                        self.global_memory
                            .insert(identifier.to_string(), Some(v.clone()));
                    }
                    Ok(v)
                } else {
                    if let Some(top) = context_stack.last_mut() {
                        top.insert(identifier.to_string(), None);
                    } else {
                        self.global_memory.insert(identifier.to_string(), None);
                    }
                    Ok(Value::Nil)
                }
            }
            Stmt::Print(expr) => {
                println!("{}", self.eval(context_stack, expr)?);
                Ok(Value::Nil)
            }
            Stmt::Expr(expr) => self.eval(context_stack, expr),
            Stmt::Block(stmts) => {
                context_stack.push(HashMap::new());
                let result = self.execute_block(context_stack, stmts);
                context_stack.pop();
                if let Err(e) = result {
                    return Err(e);
                }
                Ok(Value::Nil)
            }
            Stmt::If {
                test,
                if_true,
                if_false,
            } => {
                let if_value = self.eval(context_stack, test)?;
                match if_value {
                    Value::Bool(true) => {
                        self.execute(context_stack, &if_true)?;
                        Ok(Value::Nil)
                    }
                    Value::Bool(false) => {
                        if let Some(false_stmt) = if_false {
                            self.execute(context_stack, false_stmt)?;
                            Ok(Value::Nil)
                        } else {
                            Ok(Value::Nil)
                        }
                    }
                    _ => Err(RuntimeError::TypeError),
                }
            }
        }
    }

    fn execute_block(
        &mut self,
        context_stack: &mut Vec<Environment>,
        stmts: &bumpalo::collections::Vec<&Stmt>,
    ) -> Result<(), RuntimeError> {
        for stmt in stmts {
            self.execute(context_stack, stmt)?;
        }
        Ok(())
    }

    fn eval(
        &mut self,
        context_stack: &mut Vec<Environment>,
        expr: &Expr,
    ) -> Result<Value, RuntimeError> {
        match expr {
            Expr::Ternary {
                test,
                if_true,
                if_false,
            } => {
                if self.eval(context_stack, test)?.to_bool() {
                    self.eval(context_stack, if_true)
                } else {
                    self.eval(context_stack, if_false)
                }
            }
            Expr::Binary { left, op, right } => {
                let lhs = self.eval(context_stack, left)?;
                let rhs = self.eval(context_stack, right)?;
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
                let val = self.eval(context_stack, expr)?;
                match op {
                    UnaryOp::Not => Ok(Value::Bool(!val.to_bool())),
                    UnaryOp::Negative => Value::Number(-1f64) * val,
                }
            }
            Expr::Group(expr) => self.eval(context_stack, expr),
            Expr::Literal(Literal::Number(f)) => Ok(Value::Number(**f)),
            Expr::Literal(Literal::String(s)) => Ok(Value::String(Rc::new(s.to_string()))),
            Expr::Literal(Literal::Boolean(b)) => Ok(Value::Bool(*b)),
            Expr::Literal(Literal::Nil) => Ok(Value::Nil),
            Expr::Identifier(ident) => self.lookup_value(context_stack, ident),
            Expr::Assignment { target, expr } => {
                let value = self.eval(context_stack, expr)?;
                self.assign_value(context_stack, target, value.clone())?;
                Ok(value)
            }
            // We do this to support coallescing like behavior such as javascript has i.e. false || "a" should eval to "a"
            Expr::Logical {
                left,
                op: LogicalOp::And,
                right,
            } => {
                let left_val = self.eval(context_stack, left)?;
                if left_val.to_bool() {
                    self.eval(context_stack, right)
                } else {
                    Ok(left_val)
                }
            }
            Expr::Logical {
                left,
                op: LogicalOp::Or,
                right,
            } => {
                let left_val = self.eval(context_stack, left)?;
                if left_val.to_bool() {
                    Ok(left_val)
                } else {
                    self.eval(context_stack, right)
                }
            }
        }
    }

    fn lookup_value(
        &self,
        context_stack: &mut Vec<Environment>,
        identifier: &str,
    ) -> Result<Value, RuntimeError> {
        for context in context_stack.iter().rev() {
            if let Some(value) = context.get(identifier) {
                let v = value
                    .clone()
                    .ok_or(RuntimeError::UninitializedVariable(identifier.to_string()))?;
                return Ok(v);
            }
        }
        self.global_memory
            .get(identifier)
            .cloned()
            .ok_or(RuntimeError::UnboundVariable(identifier.to_string()))
            .and_then(|inner| {
                inner.ok_or(RuntimeError::UninitializedVariable(identifier.to_string()))
            })
    }

    fn assign_value(
        &mut self,
        context_stack: &mut Vec<Environment>,
        target: &str,
        value: Value,
    ) -> Result<(), RuntimeError> {
        for context in context_stack.iter_mut().rev() {
            if let Some(lvalue) = context.get_mut(target) {
                *lvalue = Some(value);
                return Ok(());
            }
        }

        let lvalue = self
            .global_memory
            .get_mut(target)
            .ok_or(RuntimeError::UnboundVariable(target.to_string()))?;
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
