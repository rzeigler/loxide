mod builtin;
mod callable;
mod class;
mod runtime;
mod stdlib;

use anyhow::Result;

pub use builtin::populate_builtin;
pub use runtime::{Interpreter, Value};

use self::{runtime::Environment, stdlib::load_stdlib};

pub fn stock_interpreter() -> Result<Interpreter> {
    let mut global_env = Environment::new_global();
    populate_builtin(&mut global_env);
    let mut interpreter = Interpreter::new_from_global(global_env);
    load_stdlib(&mut interpreter)?;
    Ok(interpreter)
}
