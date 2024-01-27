use std::{fmt::Debug, mem::MaybeUninit};

use anyhow::{anyhow, bail, Context, Result};

use crate::bytecode::{Chunk, OpCode, Value};

pub struct Stack<const LIMIT: usize = 256> {
    stack: [MaybeUninit<Value>; LIMIT],
    top: usize,
}

impl<const LIMIT: usize> Stack<LIMIT> {
    pub fn new() -> Stack<LIMIT> {
        Stack {
            stack: [MaybeUninit::uninit(); LIMIT],
            top: 0,
        }
    }

    pub fn push(&mut self, v: Value) -> Result<()> {
        if self.top == LIMIT {
            bail!("stack limit exceeded");
        } else {
            self.stack[self.top].write(v);
            self.top += 1;
            Ok(())
        }
    }

    pub fn pop(&mut self) -> Result<Value> {
        if self.top == 0 {
            bail!("stack empty");
        } else {
            let v = unsafe { self.stack[self.top - 1].assume_init() };
            self.top -= 1;
            Ok(v)
        }
    }
}

impl<const LIMIT: usize> Debug for Stack<LIMIT> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();

        for i in 0..self.top {
            list.entry(unsafe { &self.stack[i].assume_init() });
        }

        list.finish()
    }
}

pub struct VM<const TRACE_EXEC: bool = false> {}

impl<const TRACE_EXEC: bool> VM<TRACE_EXEC> {
    pub fn new() -> VM<TRACE_EXEC> {
        VM {}
    }

    pub fn interpret(&mut self, chunk: &Chunk) -> Result<()> {
        // Diverging from the book because I'm not going to attempt to juggle pointers
        let mut ip: usize = 0;
        let mut stack: Stack<256> = Stack::new();
        self.run(chunk, &mut ip, &mut stack)
    }

    fn read_inst(&mut self, chunk: &Chunk, ip: &mut usize) -> Result<OpCode> {
        let instruction = read_code_at_ip(chunk, *ip)?;
        *ip += 1;
        if let Some(op) = OpCode::decode(instruction) {
            Ok(op)
        } else {
            bail!("unrecognized instrution");
        }
    }

    fn read_constant(&mut self, chunk: &Chunk, ip: &mut usize) -> Result<Value> {
        let offset = read_code_at_ip(chunk, *ip)?;
        *ip += 1;
        read_constant(chunk, offset)
    }

    fn run<const STACK: usize>(
        &mut self,
        chunk: &Chunk,
        ip: &mut usize,
        stack: &mut Stack<STACK>,
    ) -> Result<()> {
        loop {
            if TRACE_EXEC {
                let mut result = String::new();
                chunk.disassemble_inst(&mut result, *ip);
                eprintln!("{} \t\tstack: {:?}", result, stack);
            }
            match self.read_inst(chunk, ip)? {
                OpCode::Return => {
                    eprintln!("\treturn={:?}", stack.pop()?);
                    return Ok(());
                }
                OpCode::Constant => {
                    let constant = self.read_constant(chunk, ip)?;
                    stack.push(constant)?;
                }
                OpCode::Negate => {
                    let v = stack.pop()?;
                    stack.push(-v)?;
                }
                OpCode::Add => {
                    let (l, r) = self.pop_binary_operands(stack)?;
                    stack.push(l + r)?;
                }
                OpCode::Subtract => {
                    let (l, r) = self.pop_binary_operands(stack)?;
                    stack.push(l - r)?;
                }
                OpCode::Multiply => {
                    let (l, r) = self.pop_binary_operands(stack)?;
                    stack.push(l * r)?;
                }
                OpCode::Divide => {
                    let (l, r) = self.pop_binary_operands(stack)?;
                    if r == 0f64 {
                        bail!("divide by zero");
                    }
                    stack.push(l / r)?;
                }
                _ => unreachable!(),
            }
        }
    }

    fn pop_binary_operands<const STACK: usize>(
        &mut self,
        stack: &mut Stack<STACK>,
    ) -> Result<(Value, Value)> {
        let r = stack.pop()?;
        let l = stack.pop()?;
        Ok((l, r))
    }
}

fn read_code_at_ip(chunk: &Chunk, ip: usize) -> Result<u8> {
    chunk
        .code()
        .get(ip)
        .context("out of bound instruction access")
        .cloned()
}

fn read_constant(chunk: &Chunk, offset: u8) -> Result<Value> {
    chunk
        .constants()
        .get(usize::from(offset))
        .context("out of bound constant access")
        .cloned()
}