use anyhow::Result;

use crate::{
    parser::{parse, ErrorReporter},
    scanner::Scanner,
};

use super::Chunk;

// pub fn compile<Reporter>(source: &str, reporter: &mut Reporter) -> Result<Chunk>
// where
//     Reporter: ErrorReporter,
// {
//     let mut scanner = Scanner::new(source);
//     let program = parse(reporter, scanner)?;

//     let mut chunk = Chunk::new();
// }
