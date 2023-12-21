mod parser;
mod scanner;

use std::env::args;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use anyhow::{Context, Result};

use scanner::Scanner;

fn main() -> Result<()> {
    let args = args();
    if args.len() > 2 {
        let mut stderr = std::io::stderr().lock();
        stderr
            .write_all("Usage: loxide [script]".as_bytes())
            .unwrap();
        std::process::exit(64);
    } else if args.len() == 2 {
        // Size is validated
        let script_path = args.skip(1).next().unwrap();
        let mut file = File::open(script_path).context("Unable to open script file")?;
        let mut script = String::new();
        file.read_to_string(&mut script)
            .context("Unable to read script file")?;
        run(&script)?;
    } else {
        run_prompt()?;
    }
    Ok(())
}

fn run_prompt() -> Result<()> {
    let mut stdout = std::io::stdout().lock();
    let stdin = std::io::stdin().lock();
    let mut reader = BufReader::new(stdin);
    let mut line = String::new();

    loop {
        stdout.write("> ".as_bytes())?;
        stdout.flush()?;
        let n = reader.read_line(&mut line)?;
        if n == 0 {
            break;
        }
        run(&line)?;
        // Don't keep appending code until the next time
        line.clear();
        stdout.write("<\n".as_bytes())?;
    }
    Ok(())
}

fn run(code: &str) -> Result<()> {
    for token_result in Scanner::new(code) {
        let token = token_result?;
        println!("{:?}", token);
    }
    Ok(())
}
