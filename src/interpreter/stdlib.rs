use std::{
    env::{self, VarError},
    fs::read_dir,
    path::{Path, PathBuf},
};

use anyhow::{anyhow, Context, Result};

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
        let path = path_result?;
        if let Some(extension) = path.path().extension() {
            if extension == ".lox" {}
        }
    }

    Ok(())
}
