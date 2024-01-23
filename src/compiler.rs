use anyhow::Result;

use crate::scanner::{Pos, Scanner};

use super::Chunk;

pub struct Error {}

pub fn compile<Reporter>(source: &str, reporter: &mut Reporter) -> Result<Chunk> {
    let mut scanner = Scanner::new(source);

    let mut chunk = Chunk::new();

    Ok(chunk)
}
