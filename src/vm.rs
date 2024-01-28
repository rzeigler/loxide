use std::{fmt::Debug, mem::MaybeUninit};

use anyhow::{anyhow, bail, Context, Result};

use crate::{
    bytecode::{Chunk, OpCode},
    heap::{Heap, Object, Value},
};

pub struct Stack<const LIMIT: usize = 256> {
    stack: [MaybeUninit<Value>; LIMIT],
    top: usize,
}

impl<'heap, const LIMIT: usize> Stack<LIMIT> {
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

impl<'heap, const LIMIT: usize> Debug for Stack<LIMIT> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();

        for i in 0..self.top {
            list.entry(unsafe { &self.stack[i].assume_init() });
        }

        list.finish()
    }
}

pub struct VM<const TRACE_EXEC: bool = false> {
    heap: Heap,
}

impl<const TRACE_EXEC: bool> VM<TRACE_EXEC> {
    pub fn new(heap: Heap) -> VM<TRACE_EXEC> {
        VM { heap }
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
        eprintln!("==== EXEC ====");
        loop {
            if TRACE_EXEC {
                let mut result = String::new();
                chunk.disassemble_inst(&mut result, *ip);
                eprintln!("{} \t\tstack: {:?}", result, stack);
            }
            // Store this since read_inst will mutate the ip and we don't want to backtrack
            let last_ip = *ip;
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
                    if let Value::Number(n) = stack.pop()? {
                        stack.push(Value::Number(-n))?;
                    } else {
                        return Err(raise_error(
                            chunk,
                            "type error: cannot negate operand",
                            last_ip,
                        ));
                    }
                }
                OpCode::Add => match self.pop_binary_operands(stack)? {
                    (Value::Number(l), Value::Number(r)) => {
                        stack.push(Value::Number(l + r))?;
                    }
                    (Value::Object(l), Value::Object(r)) => unsafe { todo!() },
                    _ => {
                        return Err(raise_error(
                            chunk,
                            "type error: cannot add operands",
                            last_ip,
                        ))
                    }
                },
                OpCode::Subtract => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Number(l - r))?;
                    } else {
                        return Err(raise_error(
                            chunk,
                            "type error: cannot subtract operands",
                            last_ip,
                        ));
                    }
                }
                OpCode::Multiply => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Number(l * r))?;
                    } else {
                        return Err(raise_error(
                            chunk,
                            "type error: cannot multiply operands",
                            last_ip,
                        ));
                    }
                }
                OpCode::Divide => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        if r == 0f64 {
                            return Err(raise_error(chunk, "divide by zero", last_ip));
                        }
                        stack.push(Value::Number(l / r))?;
                    } else {
                        return Err(raise_error(
                            chunk,
                            "type error: cannot divide operands",
                            last_ip,
                        ));
                    }
                }
                OpCode::True => {
                    stack.push(Value::Bool(true))?;
                }
                OpCode::False => {
                    stack.push(Value::Bool(false))?;
                }
                OpCode::Nil => {
                    stack.push(Value::Nil)?;
                }
                OpCode::Not => {
                    let v = stack.pop()?.to_bool();
                    stack.push(Value::Bool(!v))?;
                }
                OpCode::Equal => {
                    let (l, r) = self.pop_binary_operands(stack)?;
                    stack.push(Value::Bool(l == r))?;
                }
                OpCode::Greater => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Bool(l > r))?;
                    } else {
                        return Err(raise_error(
                            chunk,
                            "type error: > requires numeric operands",
                            last_ip,
                        ));
                    }
                }
                OpCode::Less => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Bool(l > r))?;
                    } else {
                        return Err(raise_error(
                            chunk,
                            "type error: < requires numeric operands",
                            last_ip,
                        ));
                    }
                }
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

fn raise_error(chunk: &Chunk, msg: &str, ip: usize) -> anyhow::Error {
    anyhow!("error: {} at {}", msg, chunk.lines()[ip])
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
