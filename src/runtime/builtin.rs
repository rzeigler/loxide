use std::collections::HashMap;
use std::io::prelude::*;
use std::io::stdin;
use std::rc::Rc;
use std::time::SystemTime;

use super::callable::BuiltinFunc;
use super::interpreter::Environment;
use super::interpreter::{Interpreter, RuntimeError, Value};

fn clock_impl(_interperter: &mut Interpreter, _args: Vec<Value>) -> Result<Value, RuntimeError> {
    let duration = SystemTime::UNIX_EPOCH.elapsed().unwrap();
    Ok(Value::Number(duration.as_secs_f64()))
}

fn read_stdin_impl(
    _interperter: &mut Interpreter,
    _args: Vec<Value>,
) -> Result<Value, RuntimeError> {
    let mut result = String::new();
    _ = stdin().read_to_string(&mut result)?;
    Ok(Value::String(Rc::new(result)))
}

fn parse_num_impl(_interperter: &mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError> {
    match &args[0] {
        Value::String(str) => {
            let f = str.parse::<f64>()?;
            Ok(Value::Number(f))
        }
        _ => Err(RuntimeError::TypeError("not a number")),
    }
}

pub fn populate_builtin(global_env: &mut Environment) {
    global_env.bind(
        "clock",
        Some(Value::Callable {
            callable: Rc::new(BuiltinFunc {
                name: "clock",
                arity: 0,
                call: clock_impl,
            }),
            members: HashMap::new(),
        }),
    );

    global_env.bind(
        "read_stdin",
        Some(Value::Callable {
            callable: Rc::new(BuiltinFunc {
                name: "read_stdin",
                arity: 0,
                call: read_stdin_impl,
            }),
            members: HashMap::new(),
        }),
    );

    global_env.bind(
        "parse_num",
        Some(Value::Callable {
            callable: Rc::new(BuiltinFunc {
                name: "parse_num",
                arity: 1,
                call: parse_num_impl,
            }),
            members: HashMap::new(),
        }),
    );
}
