use anyhow::Result;
use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

use crate::bytecode::Chunk;

#[derive(Debug, Clone)]
#[repr(C, u8)]
pub enum Object {
    String(Rc<String>), // Pretend static
    Function(Rc<Function>),
    NativeFunction(&'static str, NativeFunction),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionType {
    Script,
    Function,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub arity: u8,
    pub chunk: Chunk,
    pub fun_type: FunctionType,
}

impl Function {
    pub fn new_script() -> Function {
        Function {
            name: "<script>".to_string(),
            arity: 0,
            chunk: Chunk::new(),
            fun_type: FunctionType::Script,
        }
    }

    pub fn new(name: &str) -> Function {
        Function {
            name: name.to_string(),
            arity: 0,
            chunk: Chunk::new(),
            fun_type: FunctionType::Function,
        }
    }

    pub fn disassemble(&self) {
        self.chunk.disassemble(&self.name);
    }
}

pub type NativeFunction = fn(&[Value]) -> Result<Value>;

impl Object {
    pub fn is_string(&self) -> bool {
        match self {
            Object::String(_) => true,
            _ => false,
        }
    }

    pub fn string_slice(&self) -> &str {
        match self {
            Object::String(s) => s,
            _ => panic!("not a string"),
        }
    }
}

#[derive(Clone)]
pub enum Value {
    Bool(bool),
    Nil,
    Number(f64),
    Object(Object), // Wee... pointer casts
}

impl Value {
    pub fn to_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Nil => false,
            _ => true,
        }
    }

    // Create the string representation
    // This will return a Value::Object(Object::String(..))
    // If self is already one, it will return a cloned reference
    pub fn create_string(&self) -> Object {
        match self {
            Value::Object(obj) => {
                match obj {
                    // Already a string
                    Object::String(str) => Object::String(str.clone()),
                    Object::Function(fun) => Object::String(Rc::new(fun.name.clone())),
                    Object::NativeFunction(name, _) => Object::String(Rc::new(name.to_string())),
                }
            }
            Value::Nil => Object::String(Rc::new("nil".to_owned())),
            Value::Number(n) => Object::String(Rc::new(format!("{}", n))),
            Value::Bool(b) => Object::String(Rc::new(format!("{}", b))),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bool(l), Self::Bool(r)) => l == r,
            (Self::Number(l), Self::Number(r)) => l == r,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl Eq for Value {}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Value::Bool(value)
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Value::Number(value)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::Nil => f.write_str("nil"),
            Value::Number(n) => write!(f, "{}", n),
            Value::Object(obj) => {
                match obj {
                    Object::String(string) => {
                        // We don't allow construct non-utf8 string representations
                        write!(f, "\"{}\"", string)
                    }
                    Object::Function(fun) => {
                        write!(f, "<fn {}>", fun.name)
                    }
                    Object::NativeFunction(name, _) => {
                        write!(f, "<native {}>", name)
                    }
                }
            }
        }
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}
