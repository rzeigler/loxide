use std::io::Write;

use crate::scanner::Pos;

pub trait Reporter {
    fn report(&mut self, pos: Pos, msg: &str);
}

// A reporter that renders error messages to the output
pub struct WriteReporter<W> {
    writer: W,
}

impl<W> WriteReporter<W> {
    pub fn new(writer: W) -> WriteReporter<W> {
        WriteReporter { writer }
    }
}

impl<W> Reporter for WriteReporter<W>
where
    W: Write,
{
    fn report(&mut self, pos: Pos, msg: &str) {
        // If the write fails, we don't care
        _ = writeln!(self.writer, "E {}: {}", pos, msg);
    }
}

pub struct NoopReporter {}

impl Reporter for NoopReporter {
    fn report(&mut self, _pos: Pos, _msg: &str) {}
}
