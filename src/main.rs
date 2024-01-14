mod parser;
mod runtime;
mod scanner;

use std::env::args;
use std::fs::File;
use std::io::prelude::*;
use std::io::stdout;
use std::io::BufReader;

use anyhow::{Context, Result};

use bumpalo::Bump;
use parser::parse;
use runtime::stock_interpreter;
use runtime::Interpreter;
use runtime::Value;
use scanner::Scanner;

use crate::parser::WriteErrorReporter;

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
        run(&mut stock_interpreter(), &script, false);
    } else {
        run_prompt()?;
    }
    Ok(())
}

fn run_prompt() -> Result<()> {
    let stdin = std::io::stdin().lock();
    let mut reader = BufReader::new(stdin);
    let mut line = String::new();
    let mut interpreter = stock_interpreter();
    loop {
        {
            let mut stdout = stdout().lock();
            stdout.write_all("> ".as_bytes()).unwrap();
            stdout.flush()?;
        }
        let n = reader.read_line(&mut line)?;
        if n == 0 {
            break;
        }
        run(&mut interpreter, &line, true);
        // Don't keep appending code until the next time
        line.clear();
        {
            let mut stdout = stdout().lock();
            stdout.write_all("<\n".as_bytes()).unwrap();
            stdout.flush().unwrap();
        }
    }
    Ok(())
}

fn run(interpreter: &mut Interpreter, code: &str, in_repl: bool) {
    let bump = Bump::new();
    let mut stderr = std::io::stderr().lock();
    let mut reporter = WriteErrorReporter::new(&mut stderr);

    match parse(&bump, &mut reporter, Scanner::new(code)) {
        Ok(program) => {
            if in_repl && program.0.len() == 1 {
                match interpreter.interpret_one(program.0[0]) {
                    Ok(Value::Nil) => {}
                    Ok(v) => println!("{}", v),
                    Err(e) => eprintln!("{}", e),
                }
            } else {
                if let Err(e) = interpreter.interpret(program) {
                    eprintln!("{}", e);
                }
            }
        }
        Err(error) => {
            eprintln!("{}", error)
        }
    };
}
