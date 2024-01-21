mod bytecode;
mod vm;

pub use bytecode::{BinaryOp, Chunk};
pub use vm::VM;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("compile error")]
    Compile,
    #[error("internal error")]
    Internal,
    #[error("runtime error")]
    Runtime,
}
