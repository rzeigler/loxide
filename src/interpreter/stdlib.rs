use std::{
    env::{self, VarError},
    fs::{read_dir, File},
    io::Read,
    path::{Path, PathBuf},
};

use anyhow::{anyhow, Context, Result};

use crate::{
    parser::{parse, WriteErrorReporter},
    scanner::Scanner,
};

use super::Interpreter;

pub fn load_stdlib(interpreter: &mut Interpreter) -> Result<()> {
    let libdir = if let Some(libdir) = std::env::var_os("LOXIDE_LIBDIR") {
        libdir
    } else {
        let current_exe = env::current_exe().context("installation broken: no interpreter path")?;

        let dir = current_exe
            .parent()
            .ok_or(anyhow!("installation broken: resolving lib directory"))?;

        let mut libdir = PathBuf::new();
        libdir.push(dir);

        libdir.push("lib");
        libdir.push("loxide");

        libdir.as_os_str().to_owned()
    };

    for path_result in read_dir(libdir)? {
        let mut stderr = std::io::stderr().lock();
        let mut reporter = WriteErrorReporter::new(&mut stderr);
        let path = path_result?;
        if let Some(extension) = path.path().extension() {
            if extension == ".lox" {
                let mut file = File::open(path.path()).context("Unable to open stdlib path")?;
                let mut script = String::new();
                file.read_to_string(&mut script)
                    .context("Unable to read stdlib path")?;
                // TODO: More diagnostics
                let program = parse(&mut reporter, Scanner::new(&script))
                    .context("Unable to parse stdlib path")?;
                interpreter
                    .interpret(program)
                    .context("Unable to load stdlib")?;
            }
        }
    }

    Ok(())
}
