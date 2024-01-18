use std::rc::Rc;
use std::time::SystemTime;

use super::callable::RustFunc;
use super::runtime::Environment;
use super::runtime::{Interpreter, RuntimeError, Value};

fn system_time(_interperter: &mut Interpreter, _args: Vec<Value>) -> Result<Value, RuntimeError> {
    let duration = SystemTime::UNIX_EPOCH.elapsed().unwrap();
    Ok(Value::Number(duration.as_secs_f64()))
}

pub fn populate_builtin(global_env: &mut Environment) {
    global_env.bind(
        "system_time",
        Some(Value::Callable(Rc::new(RustFunc {
            name: "system_time",
            arity: 0,
            call: system_time,
        }))),
    );
}
