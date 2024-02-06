#![feature(alloc_layout_extra, let_chains)]

mod bytecode;
mod compiler;
mod heap;
mod reporter;
mod scanner;
mod vm;

use std::env::args;
use std::fs::File;
use std::io::prelude::*;
use std::io::stderr;
use std::io::stdout;
use std::io::BufReader;

use anyhow::bail;
use anyhow::{Context, Result};

use bytecode::Chunk;
use compiler::compile;
use heap::Heap;
use reporter::WriteReporter;
use vm::VM;

fn main() -> Result<()> {
    let args = args().collect::<Vec<_>>();
    if args.len() == 2 {
        run::<false>(&args[1])?;
    } else if args.len() == 1 {
        run_prompt::<false>()?;
    } else {
        eprintln!("Usage: loxide <script>");
        bail!("issue");
    }

    Ok(())
}

fn run<const DEBUG: bool>(path: &str) -> Result<()> {
    let mut file = File::open(&path).context("failed to open the file")?;
    let mut data = String::new();
    _ = file.read_to_string(&mut data)?;

    let mut heap = Heap::new();
    let mut vm: VM<DEBUG> = VM::new(heap.clone());
    let mut reporter = WriteReporter::new(stderr().lock());

    match compile(&data, &mut reporter, &mut heap) {
        Ok(chunk) => {
            chunk.disassemble(path);
            if let Err(e) = vm.interpret(&chunk) {
                eprintln!("{}", e);
            }
        }
        Err(err) => {
            eprintln!("{}", err);
        }
    };

    Ok(())
}

fn run_prompt<const DEBUG: bool>() -> Result<()> {
    let stdin = std::io::stdin().lock();
    let mut heap = Heap::new();
    let mut vm: VM<DEBUG> = VM::new(heap.clone());

    let mut reader = BufReader::new(stdin);
    let mut line = String::new();
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

        let mut reporter = WriteReporter::new(stderr().lock());
        match compile(&line, &mut reporter, &mut heap) {
            Ok(chunk) => {
                chunk.disassemble("prompt line");
                if let Err(e) = vm.interpret(&chunk) {
                    eprintln!("{}", e);
                }
            }
            Err(err) => {
                eprintln!("{}", err);
            }
        };

        line.clear();
        {
            let mut stdout = stdout().lock();
            stdout.write_all("<\n".as_bytes()).unwrap();
            stdout.flush().unwrap();
        }
    }
    Ok(())
}

// fn run(interpreter: &mut Interpreter, code: &str, in_repl: bool) {
//     let mut stderr = std::io::stderr().lock();
//     let mut reporter = WriteErrorReporter::new(&mut stderr);

//     match parse(&mut reporter, Scanner::new(code)) {
//         Ok(program) => {
//             if in_repl && program.0.len() == 1 {
//                 let first = program.0.into_iter().next().unwrap();
//                 match interpreter.interpret_one(first) {
//                     Ok(Value::Nil) => {}
//                     Ok(v) => println!("{}", v.to_string()),
//                     Err(e) => eprintln!("{}", e),
//                 }
//             } else {
//                 if let Err(e) = interpreter.interpret(program) {
//                     eprintln!("{}", e);
//                 }
//             }
//         }
//         Err(error) => {
//             eprintln!("{}", error)
//         }
//     };
// }
