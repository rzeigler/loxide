use super::interpreter::{Interpreter, RuntimeError, UnwindCause, Value};
use crate::parser::Stmt;

pub trait Callable {
    fn name(&self) -> &str;
    fn arity(&self) -> u8;
    fn call(&self, interpreter: &mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError>;
}

#[derive(Debug, Clone, PartialEq)]
pub struct PlatformFunc {
    pub name: &'static str,
    pub arity: u8,
    pub call: fn(&mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError>,
}

impl Callable for PlatformFunc {
    fn name(&self) -> &str {
        self.name
    }

    fn arity(&self) -> u8 {
        self.arity
    }

    fn call(&self, interperter: &mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError> {
        (self.call)(interperter, args)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct HostedFunc {
    pub name: String,
    pub parameters: Vec<String>,
    pub body: Stmt,
}

impl Callable for HostedFunc {
    fn name(&self) -> &str {
        &self.name
    }

    fn arity(&self) -> u8 {
        self.parameters.len().try_into().unwrap()
    }

    fn call(&self, interpreter: &mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError> {
        assert_eq!(self.parameters.len(), args.len());
        interpreter.begin_scope();
        for (parameter, value) in self.parameters.iter().zip(args.into_iter()) {
            interpreter.define_in_current_scope(&parameter, Some(value));
        }
        let result = interpreter.execute(&self.body);
        interpreter.end_scope();
        match result {
            Ok(_) => Ok(Value::Nil),
            Err(UnwindCause::Return(v)) => Ok(v),
            Err(UnwindCause::Break) => Err(RuntimeError::InvalidBreak),
            Err(UnwindCause::Error(error)) => Err(error),
        }
    }
}
