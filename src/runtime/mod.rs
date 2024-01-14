mod builtin;
mod callable;
mod interpreter;

use std::collections::HashMap;

pub use builtin::populate_builtin;
pub use interpreter::{Interpreter, Value};

pub fn stock_interpreter() -> Interpreter {
    let mut global_env = HashMap::<String, Option<Value>>::new();
    populate_builtin(&mut global_env);
    Interpreter::new_with_global(global_env)
}
