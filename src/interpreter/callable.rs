use std::rc::Rc;

use super::{
    class::Instance,
    runtime::{Environment, Interpreter, RuntimeError, UnwindCause, Value},
};
use crate::{ast::Stmt, scanner::THIS_LITERAL};

pub trait Func {
    fn name(&self) -> &str;
    fn arity(&self) -> u8;
    fn call(&self, interpreter: &mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError>;
}

#[derive(Debug, Clone, PartialEq)]
pub struct RustFunc {
    pub name: &'static str,
    pub arity: u8,
    pub call: fn(&mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError>,
}

impl Func for RustFunc {
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

#[derive(Clone)]
pub struct LoxFunc {
    pub name: String,
    pub parameters: Vec<String>,
    pub body: Stmt,
    pub is_init: bool,
    pub closure: Rc<Environment>,
}

impl LoxFunc {
    // The actual implementation of call_fun, we don't the interpreter, because we can construct a new
    // one from the closure
    pub fn call_fun(&self, args: Vec<Value>) -> Result<Value, RuntimeError> {
        let mut interpreter = Interpreter::new_from_closure(self.closure.clone());
        interpreter.begin_scope();
        for (parameter, value) in self.parameters.iter().zip(args.into_iter()) {
            interpreter.current_env().bind(&parameter, Some(value));
        }
        let result = interpreter.execute(&self.body);
        interpreter.end_scope();
        match result {
            Ok(value) => {
                if self.is_init {
                    Ok(interpreter.current_env().lookup(THIS_LITERAL, 0).unwrap())
                } else {
                    Ok(value)
                }
            }
            Err(UnwindCause::Return(v)) => Ok(v),
            Err(UnwindCause::Break) => Err(RuntimeError::InvalidBreak),
            Err(UnwindCause::Error(error)) => Err(error),
        }
    }

    pub fn bind(&self, this: Instance) -> LoxFunc {
        let env = self.closure.clone().open_scope();
        env.bind(THIS_LITERAL, Some(Value::Instance(this)));
        LoxFunc {
            name: self.name.clone(),
            parameters: self.parameters.clone(),
            body: self.body.clone(),
            is_init: self.is_init,
            closure: env,
        }
    }
}

impl Func for LoxFunc {
    fn name(&self) -> &str {
        &self.name
    }

    fn arity(&self) -> u8 {
        self.parameters.len().try_into().unwrap()
    }

    fn call(
        &self,
        _interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        self.call_fun(args)
    }
}
