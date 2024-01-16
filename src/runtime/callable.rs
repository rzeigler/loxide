use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::interpreter::{Environment, Interpreter, RuntimeError, UnwindCause, Value};
use crate::ast::{ClassBody, Stmt};

pub trait Callable {
    fn name(&self) -> &str;
    fn arity(&self) -> u8;
    fn call(&self, interpreter: &mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError>;
}

#[derive(Debug, Clone, PartialEq)]
pub struct BuiltinFunc {
    pub name: &'static str,
    pub arity: u8,
    pub call: fn(&mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError>,
}

impl Callable for BuiltinFunc {
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
pub struct HostedFunc {
    pub name: String,
    pub parameters: Vec<String>,
    pub body: Stmt,
    pub closure: Rc<Environment>,
}

impl HostedFunc {
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
            Ok(_) => Ok(Value::Nil),
            Err(UnwindCause::Return(v)) => Ok(v),
            Err(UnwindCause::Break) => Err(RuntimeError::InvalidBreak),
            Err(UnwindCause::Error(error)) => Err(error),
        }
    }
}

impl Callable for HostedFunc {
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

// We split the class from ClassInner so that the instances can hold a reference to inner for member lookup but
// the Class can implement callable
pub struct Class {
    pub inner: Rc<ClassInner>,
}

pub struct ClassInner {
    pub name: String,
    pub body: ClassBody,
}

impl Callable for Class {
    fn name(&self) -> &str {
        &self.inner.name
    }

    fn arity(&self) -> u8 {
        0
    }

    fn call(
        &self,
        interpreter: &mut Interpreter,
        _args: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        // First, lets take all the methods off the class instance and stuff them into the closure
        let members = Rc::new(RefCell::new(HashMap::new()));

        // Similar to resolver, introduce closure containing the this
        let closure = interpreter.current_env_closure().open_scope();
        let instance = Value::Instance {
            members: members.clone(),
            class: self.inner.clone(),
        };
        closure.bind("this", Some(instance.clone()));

        for method in self.inner.body.methods.iter() {
            members.as_ref().borrow_mut().insert(
                method.name.clone(),
                Value::Callable(Rc::new(HostedFunc {
                    name: method.name.clone(),
                    parameters: method.parameters.clone(),
                    body: method.body.as_ref().clone(),
                    closure: closure.clone(),
                })),
            );
        }

        Ok(instance)
    }
}
