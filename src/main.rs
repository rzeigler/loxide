mod bytecode;
mod compiler;
mod reporter;
mod scanner;
mod vm;

use std::env::args;
use std::fs::File;
use std::io::prelude::*;
use std::io::stderr;
use std::io::stdout;
use std::io::BufReader;

use anyhow::{Context, Result};

use bytecode::Chunk;
use compiler::compile;
use reporter::WriteReporter;
use scanner::Scanner;
use vm::VM;

fn main() -> Result<()> {
    // let mut chunk = Chunk::new();
    // chunk.emit_constant(1.2, 1);
    // chunk.emit_negate(2);
    // chunk.emit_constant(9.0, 3);
    // chunk.emit_binary_op(bytecode::BinaryOp::Add, 3);
    // chunk.emit_return(2);

    // let mut vm: VM<true> = VM::new();
    // vm.interpret(&chunk)?;
    run_prompt()?;

    Ok(())
}

fn run_prompt() -> Result<()> {
    let stdin = std::io::stdin().lock();

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

        let mut stderr = stderr().lock();
        let mut reporter = WriteReporter::new(&mut stderr);
        let chunk = compile(&line, &mut reporter)?;
        chunk.disassemble("prompt");

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
