mod builtin;
mod callable;
mod class;
mod runtime;
mod stdlib;

pub use builtin::populate_builtin;
pub use runtime::{Interpreter, Value};

use self::runtime::Environment;

pub fn stock_interpreter() -> Interpreter {
    let mut global_env = Environment::new_global();
    populate_builtin(&mut global_env);
    Interpreter::new_from_global(global_env)
}
