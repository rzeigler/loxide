use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    io::{self},
    num::ParseFloatError,
    ops::{Add, Div, Mul, Sub},
    rc::Rc,
};

use thiserror::Error;

use super::{
    callable::{Func, LoxFunc},
    class::{Class, Instance, INIT_METHOD_NAME},
};
use crate::{
    ast::{BinaryOp, Expr, FunDecl, Literal, LogicalOp, Program, Stmt, UnaryOp},
    scanner::{SUPER_LITERAL, THIS_LITERAL},
};

#[derive(Error, Debug)]
pub enum RuntimeError {
    #[error("divide by zero")]
    DivideByZero,
    #[error("type error: {0}")]
    TypeError(&'static str),
    #[error("undefined variable: {0}")]
    UndefinedVariable(String),
    #[error("uninitialized variable: {0}")]
    UninitializedVariable(String),
    #[error("break outside of a loop")]
    InvalidBreak,
    #[error("invalid return")]
    InvalidReturn,
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
    Return(Value),
    Break,
}

#[derive(Clone)]
pub enum Value {
    String(Rc<String>),
    Number(f64),
    Bool(bool),
    Callable(Rc<dyn Func>),
    Class(Class),
    Instance(Instance),
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

    // fn to_callable(&self) -> Option<&dyn Func> {
    //     match self {
    //         Self::Callable {
    //             callable,
    //             members: _,
    //         } => Some(callable.as_ref()),
    //         _ => None,
    //     }
    // }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "Value::String('{}')", s),
            Value::Number(n) => write!(f, "Value::Number({})", n),
            Value::Bool(b) => write!(f, "Value::Bool({})", b),
            Value::Nil => f.write_str("Value::Nil"),
            Value::Callable(func) => write!(f, "Value::Callable({})", func.name()),
            Value::Class(class) => write!(f, "Value::Class({})", class.name()),
            Value::Instance(Instance { fields: _, class }) => {
                write!(f, "Value::Instance({})", class.inner.name)
            }
        }
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::String(s) => s.to_owned().as_ref().to_string(),
            Value::Number(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Nil => "nil".to_owned(),
            Value::Callable(func) => format!("{}", func.name()),
            Value::Class(class) => format!("{}", class.name()),
            Value::Instance(Instance { fields: _, class }) => {
                format!("{} instance", class.inner.name)
            }
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

#[derive(Debug)]
pub struct Environment {
    bindings: RefCell<HashMap<String, Option<Value>>>, // None indicates name defined but unbound
    parent: Option<Rc<Environment>>,
}

impl Environment {
    pub fn new_global() -> Environment {
        Environment {
            bindings: RefCell::new(HashMap::new()),
            parent: None,
        }
    }
}

impl Environment {
    pub fn bind(&self, name: &str, value: Option<Value>) {
        self.bindings.borrow_mut().insert(name.to_string(), value);
    }

    /// Lookup a value
    /// The outer Option indicates whether or not the name exists
    /// The inner Option indicates whether the value has been bound
    pub fn lookup(&self, name: &str, scope_distance: u32) -> Option<Value> {
        if scope_distance > 0 {
            self.parent
                .as_ref()
                .expect("variable resolution is broken")
                .lookup(name, scope_distance - 1)
        } else {
            self.bindings
                .borrow()
                .get(name)
                .expect("variable resolution is broken")
                .clone()
        }
    }

    pub fn assign(&self, name: &str, value: Value, scope_distance: u32) {
        if scope_distance > 0 {
            self.parent
                .as_ref()
                .expect("variable resolution is broken")
                .assign(name, value, scope_distance - 1);
        } else {
            self.bindings
                .borrow_mut()
                .insert(name.to_string(), Some(value));
        }
    }

    pub fn open_scope(self: Rc<Environment>) -> Rc<Environment> {
        Rc::new(Environment {
            bindings: RefCell::new(HashMap::new()),
            parent: Some(self),
        })
    }

    pub fn close_scope(self: Rc<Environment>) -> Rc<Environment> {
        self.parent.as_ref().unwrap().clone()
    }
}

pub struct Interpreter {
    // None indicates that the variable is defined by not yet initialized
    environment: Rc<Environment>,
}

impl Interpreter {
    pub fn new_from_global(global: Environment) -> Interpreter {
        Interpreter::new_from_closure(Rc::new(global))
    }

    pub fn new_from_closure(closure: Rc<Environment>) -> Interpreter {
        Interpreter {
            environment: closure,
        }
    }

    pub fn interpret(&mut self, mut program: Program) -> Result<(), RuntimeError> {
        let mut resolver = Resolver::new();

        let global = self.environment.bindings.borrow();
        resolver.define_all(global.keys());
        resolver.resolve_program(&mut program)?;
        drop(global);

        for stmt in program.0 {
            match self.execute(&stmt) {
                Ok(_) => {}
                Err(UnwindCause::Break) => return Err(RuntimeError::InvalidBreak),
                Err(UnwindCause::Error(err)) => return Err(err),
                Err(UnwindCause::Return(_)) => return Ok(()),
            };
        }
        Ok(())
    }

    pub fn interpret_one(&mut self, mut stmt: Stmt) -> Result<Value, RuntimeError> {
        let mut resolver = Resolver::new();

        let global = self.environment.bindings.borrow();
        resolver.define_all(global.keys());
        resolver.resolve_stmt(&mut stmt)?;
        drop(global);

        match self.execute(&stmt) {
            Ok(v) => Ok(v),
            Err(UnwindCause::Break) => Err(RuntimeError::InvalidBreak),
            Err(UnwindCause::Return(v)) => Ok(v),
            Err(UnwindCause::Error(err)) => Err(err),
        }
    }

    pub fn begin_scope(&mut self) {
        self.environment = self.environment.clone().open_scope();
    }

    pub fn end_scope(&mut self) {
        self.environment = self.environment.clone().close_scope();
    }

    pub fn current_env(&self) -> &Environment {
        &self.environment
    }

    pub fn current_env_closure(&self) -> Rc<Environment> {
        self.environment.clone()
    }

    pub fn execute(&mut self, stmt: &Stmt) -> Result<Value, UnwindCause> {
        match stmt {
            Stmt::VarDecl {
                name: identifier,
                init,
            } => {
                if let Some(expr) = init {
                    let value = self.eval(expr)?;
                    self.environment.bind(&identifier, Some(value.clone()));
                    Ok(value)
                } else {
                    self.environment.bind(&identifier, None);
                    Ok(Value::Nil)
                }
            }
            Stmt::Print(expr) => {
                println!("{}", self.eval(expr)?.to_string());
                Ok(Value::Nil)
            }
            Stmt::Expr(expr) => self.eval(expr),
            Stmt::Block(stmts) => {
                self.begin_scope();
                let result = self.execute_block(stmts);
                self.end_scope();
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
                if self.eval(test)?.to_bool() {
                    self.execute(&if_true)?;
                    Ok(Value::Nil)
                } else {
                    if let Some(false_stmt) = if_false {
                        self.execute(false_stmt)?;
                        Ok(Value::Nil)
                    } else {
                        Ok(Value::Nil)
                    }
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
            Stmt::FunDecl(FunDecl {
                name,
                parameters,
                body,
            }) => {
                let func = LoxFunc {
                    name: name.clone(),
                    parameters: parameters.clone(),
                    body: body.as_ref().clone(),
                    closure: self.current_env_closure(),
                    is_init: false,
                };
                self.environment
                    .bind(name, Some(Value::Callable(Rc::new(func))));
                Ok(Value::Nil)
            }
            Stmt::Return(expr) => {
                let v = if let Some(expr) = expr {
                    self.eval(expr)?
                } else {
                    Value::Nil
                };
                return Err(UnwindCause::Return(v));
            }
            Stmt::ClassDecl { name, parent, body } => {
                let mut closure = self.current_env_closure();

                let parent_class = if let Some(parent_expr) = parent {
                    if let Value::Class(parent_class) = self.eval(parent_expr)? {
                        closure = closure.open_scope();
                        closure.bind(SUPER_LITERAL, Some(Value::Class(parent_class.clone())));
                        Some(parent_class)
                    } else {
                        return Err(UnwindCause::Error(RuntimeError::TypeError(
                            "parent is not a class",
                        )));
                    }
                } else {
                    None
                };

                let class = Class::new(name, body, parent_class, closure);
                self.environment.bind(&name, Some(Value::Class(class)));

                Ok(Value::Nil)
            }
        }
    }

    fn execute_block(&mut self, stmts: &[Stmt]) -> Result<(), UnwindCause> {
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
            Expr::Variable {
                name,
                scope_distance,
            } => self
                .environment
                .lookup(
                    name,
                    // Should be defined if resolution ran correctly
                    scope_distance.unwrap(),
                )
                // If the name was defined, but there is not currently a value, the inner option is None
                .ok_or(RuntimeError::UninitializedVariable(name.to_owned()))
                .map_err(|err| UnwindCause::Error(err)),
            Expr::This { scope_distance } => {
                let this = self
                    .environment
                    .lookup(THIS_LITERAL, scope_distance.unwrap())
                    // The resolution should prevent this from failing
                    .unwrap();
                Ok(this)
            }
            Expr::Super {
                method,
                scope_distance,
            } => {
                // We assume that this is always in the scope above super
                // We need a this instance to bind
                if let Value::Instance(this) = self
                    .environment
                    .lookup(THIS_LITERAL, scope_distance.unwrap() - 1)
                    .unwrap()
                {
                    // We need to bind the this as well
                    if let Value::Class(superclass) = self
                        .environment
                        .lookup(SUPER_LITERAL, scope_distance.unwrap())
                        .unwrap()
                    {
                        if let Some(method) = superclass.get_method(method) {
                            Ok(Value::Callable(Rc::new(method.bind(this))))
                        } else {
                            Err(UnwindCause::Error(RuntimeError::UndefinedVariable(
                                format!("undefined function: {}", method),
                            )))
                        }
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!();
                }
            }
            Expr::Assignment {
                target,
                scope_distance,
                expr,
            } => {
                let value = self.eval(expr)?;
                self.environment.assign(
                    target,
                    value.clone(),
                    // Should be defined if resolution ran correctly
                    scope_distance.unwrap(),
                );
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
                match callee {
                    Value::Callable(func) => {
                        if usize::from(func.arity()) != arguments.len() {
                            return Err(UnwindCause::Error(RuntimeError::ArityMismatch(format!(
                                "function {} takes {} args",
                                func.name(),
                                func.arity()
                            ))));
                        }
                        let args = arguments
                            .iter()
                            .map(|expr| self.eval(expr))
                            .collect::<Result<Vec<_>, _>>()?;
                        func.call(self, args).map_err(|e| UnwindCause::Error(e))
                    }
                    Value::Class(class) => {
                        if usize::from(class.arity()) != arguments.len() {
                            return Err(UnwindCause::Error(RuntimeError::ArityMismatch(format!(
                                "class init {} takes {} args",
                                class.name(),
                                class.arity()
                            ))));
                        }
                        let args = arguments
                            .iter()
                            .map(|expr| self.eval(expr))
                            .collect::<Result<Vec<_>, _>>()?;
                        class
                            .construct(self, args)
                            .map_err(|e| UnwindCause::Error(e))
                    }
                    _ => Err(UnwindCause::Error(RuntimeError::NotCallable(
                        callee.to_string(),
                    ))),
                }
            }
            Expr::Get { object, property } => match self.eval(object)? {
                Value::Instance(instance) => {
                    if let Some(value) = instance.fields.borrow().get(property) {
                        Ok(value.clone())
                    } else if let Some(method) = instance.class.get_method(property) {
                        Ok(Value::Callable(Rc::new(method.bind(instance.clone()))))
                    } else {
                        Err(UnwindCause::Error(RuntimeError::UndefinedVariable(
                            format!("undefined property: {}", property),
                        )))
                    }
                }
                Value::Class(class) => {
                    if let Some(func) = class.inner.class_methods.get(property) {
                        Ok(Value::Callable(func.clone()))
                    } else {
                        Err(UnwindCause::Error(RuntimeError::UndefinedVariable(
                            format!("undefined property: {}", property),
                        )))
                    }
                }
                _ => Err(UnwindCause::Error(RuntimeError::TypeError(
                    "only instances and classes have properties",
                ))),
            },
            Expr::Set {
                object,
                property,
                value,
            } => match self.eval(object)? {
                Value::Instance(instance) => {
                    let value = self.eval(value)?;
                    instance
                        .fields
                        .borrow_mut()
                        .insert(property.clone(), value.clone());
                    Ok(value)
                }
                _ => Err(UnwindCause::Error(RuntimeError::TypeError(
                    "only instances may be assigned to properties",
                ))),
            },
        }
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ResolveState {
    Declared,
    Defined,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CurrentClass {
    None,
    Class,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FunctionType {
    Initializer,
    Method,
    Function,
}

struct Resolver {
    // The resolver is kind of weird, we should probably not be a class and instead pass it by arguments
    scopes: Vec<HashMap<String, ResolveState>>,
    current_class: CurrentClass,
    current_function: Option<FunctionType>,
}

impl Resolver {
    pub fn new() -> Resolver {
        Resolver {
            scopes: vec![HashMap::new()],
            current_class: CurrentClass::None,
            current_function: None,
        }
    }

    /// Add the following bindings to the topmost scope
    /// This is intended to inform the resolver about platform provided globals
    pub fn define_all<S>(&mut self, bindings: impl Iterator<Item = S>)
    where
        S: AsRef<str>,
    {
        for binding in bindings {
            self.define(binding.as_ref());
        }
    }

    pub fn resolve_program(&mut self, program: &mut Program) -> Result<(), RuntimeError> {
        for stmt in program.0.iter_mut() {
            self.resolve_stmt(stmt)?;
        }
        Ok(())
    }

    pub fn resolve_stmt(&mut self, stmt: &mut Stmt) -> Result<(), RuntimeError> {
        match stmt {
            Stmt::Block(stmts) => {
                self.begin_scope();
                for stmt in stmts {
                    self.resolve_stmt(stmt)?;
                }
                self.end_scope();
                Ok(())
            }
            Stmt::Break => Ok(()),
            Stmt::Expr(expr) => self.resolve_expr(expr),
            Stmt::FunDecl(FunDecl {
                name,
                parameters,
                body,
            }) => {
                self.current_function = Some(FunctionType::Function);
                self.define(name);
                self.begin_scope();
                for param in parameters.iter() {
                    self.define(param);
                }
                self.resolve_stmt(body)?;
                self.end_scope();
                Ok(())
            }
            Stmt::If {
                expr,
                then,
                or_else,
            } => {
                self.resolve_expr(expr)?;
                self.resolve_stmt(then)?;
                if let Some(then) = or_else {
                    self.resolve_stmt(then)?;
                }
                Ok(())
            }
            Stmt::Loop { expr, body } => {
                self.resolve_expr(expr)?;
                self.resolve_stmt(body)
            }
            Stmt::Print(expr) => self.resolve_expr(expr),
            Stmt::Return(expr) => {
                // Returns must be in a function, if its an initializer, we disallow setting an expr
                if self.current_function == None
                    || (self.current_function == Some(FunctionType::Initializer) && expr.is_some())
                {
                    return Err(RuntimeError::InvalidReturn);
                }
                if let Some(ret) = expr {
                    self.resolve_expr(ret)?;
                }
                Ok(())
            }
            Stmt::VarDecl {
                name: identifier,
                init,
            } => {
                self.declare(&identifier);
                if let Some(init) = init {
                    self.resolve_expr(init)?;
                }
                self.define(&identifier);
                Ok(())
            }
            Stmt::ClassDecl { name, parent, body } => {
                self.define(&name);

                for method in body.class_methods.iter_mut() {
                    self.define(&method.name);
                    self.current_function = Some(FunctionType::Function);

                    self.begin_scope();
                    for param in method.parameters.iter() {
                        self.define(param);
                    }
                    self.resolve_stmt(&mut method.body)?;
                    self.end_scope();
                }

                if let Some(parent) = parent {
                    self.resolve_expr(parent)?;
                    self.begin_scope();
                    self.define(SUPER_LITERAL);
                }
                // The class body introduces an implicit scope ...
                self.begin_scope();
                // ... which contains this
                self.define(THIS_LITERAL);

                // Is there a problem with the cleanup logic, do we need some kind of guard?
                self.current_class = CurrentClass::Class;

                for method in body.methods.iter_mut() {
                    self.define(&method.name);
                    self.current_function = if method.name == INIT_METHOD_NAME {
                        Some(FunctionType::Initializer)
                    } else {
                        Some(FunctionType::Method)
                    };
                    self.begin_scope();
                    for param in method.parameters.iter() {
                        self.define(param);
                    }
                    self.resolve_stmt(&mut method.body)?;
                    self.end_scope();
                }

                self.current_class = CurrentClass::None;

                self.end_scope();

                if parent.is_some() {
                    self.end_scope();
                }
                Ok(())
            }
        }
    }

    fn resolve_expr(&mut self, expr: &mut Expr) -> Result<(), RuntimeError> {
        match expr {
            Expr::Assignment {
                target,
                expr,
                scope_distance,
            } => {
                *scope_distance = Some(self.resolve_identifier(target)?);
                self.resolve_expr(expr)
            }
            Expr::Binary { left, op: _, right } => {
                self.resolve_expr(left)?;
                self.resolve_expr(right)
            }
            Expr::Call { callee, arguments } => {
                self.resolve_expr(callee)?;
                for arg in arguments.iter_mut() {
                    self.resolve_expr(arg)?;
                }
                Ok(())
            }
            Expr::Group(expr) => self.resolve_expr(expr),
            Expr::Variable {
                name,
                scope_distance,
            } => {
                *scope_distance = Some(self.resolve_identifier(name)?);
                Ok(())
            }
            Expr::This { scope_distance } => {
                if self.current_class == CurrentClass::None {
                    Err(RuntimeError::UndefinedVariable(
                        "this (outside of class)".to_string(),
                    ))
                } else {
                    *scope_distance = Some(self.resolve_identifier(THIS_LITERAL)?);
                    Ok(())
                }
            }
            Expr::Super {
                method: _,
                scope_distance,
            } => {
                if self.current_class == CurrentClass::None {
                    Err(RuntimeError::UndefinedVariable(
                        "this (outside of class)".to_string(),
                    ))
                } else {
                    *scope_distance = Some(self.resolve_identifier(SUPER_LITERAL)?);
                    Ok(())
                }
            }
            Expr::Ternary {
                test,
                if_true,
                if_false,
            } => {
                self.resolve_expr(test)?;
                self.resolve_expr(if_true)?;
                self.resolve_expr(if_false)
            }
            Expr::Unary { op: _, expr } => self.resolve_expr(expr),
            Expr::Literal(_) => Ok(()),
            Expr::Logical { left, op: _, right } => {
                self.resolve_expr(left)?;
                self.resolve_expr(right)
            }
            Expr::Get {
                object,
                property: _,
            } => self.resolve_expr(object),
            Expr::Set {
                object,
                property: _,
                value,
            } => {
                self.resolve_expr(object)?;
                self.resolve_expr(value)
            }
        }
    }

    fn resolve_identifier(&self, name: &str) -> Result<u32, RuntimeError> {
        for (i, scope) in self.scopes.iter().rev().enumerate() {
            if let Some(state) = scope.get(name) {
                if *state == ResolveState::Defined {
                    return Ok(i.try_into().unwrap());
                }
            }
        }
        Err(RuntimeError::UndefinedVariable(name.to_string()))
    }

    fn declare(&mut self, name: &str) {
        self.scopes
            .last_mut()
            // Per new there should always be at least 1
            .unwrap()
            .insert(name.to_string(), ResolveState::Declared);
    }

    fn define(&mut self, name: &str) {
        // Define just inserts the value, this allows us to directly define things
        self.scopes
            .last_mut()
            // Per new there should always be at least 1
            .unwrap()
            .insert(name.to_string(), ResolveState::Defined);
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }
}
