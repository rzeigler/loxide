mod builtin;
mod callable;
mod interpreter;

pub use builtin::populate_builtin;
pub use interpreter::{Interpreter, Value};

use self::interpreter::Environment;

pub fn stock_interpreter() -> Interpreter {
    let mut global_env = Environment::new_global();
    populate_builtin(&mut global_env);
    Interpreter::new_from_global(global_env)
}
