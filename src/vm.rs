use core::slice;
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

pub struct VM<const TRACE_EXEC: bool = false> {
    heap: Heap,
    globals: Vec<Value>,
}

impl<const TRACE_EXEC: bool> VM<TRACE_EXEC> {
    pub fn new(heap: Heap) -> VM<TRACE_EXEC> {
        VM {
            heap,
            globals: Vec::new(),
        }
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

    fn read_stack_slot(&mut self, chunk: &Chunk, ip: &mut usize) -> Result<usize> {
        let offset = read_code_at_ip(chunk, *ip)?;
        *ip += 1;
        Ok(offset.into())
    }

    fn read_jump_len(&mut self, chunk: &Chunk, ip: &mut usize) -> Result<usize> {
        let high_byte = read_code_at_ip(chunk, *ip)?;
        let low_byte = read_code_at_ip(chunk, *ip + 1)?;
        *ip += 2;

        let count = ((high_byte as u16) << 8) | (low_byte as u16);
        Ok(count.into())
    }

    fn run<const STACK: usize>(
        &mut self,
        chunk: &Chunk,
        ip: &mut usize,
        stack: &mut Stack<STACK>,
    ) -> Result<()> {
        if TRACE_EXEC {
            eprintln!("==== EXEC ====");
        }
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
                    (Value::Object(l), Value::Object(r)) => unsafe {
                        if (&*l).is_string() || (&*r).is_string() {
                            stack.push(self.concat_strings(Value::Object(l), Value::Object(r)))?;
                        } else {
                            return Err(raise_error(
                                chunk,
                                "type error: cannot add operands",
                                last_ip,
                            ));
                        }
                    },
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
                OpCode::Print => {
                    let v = stack.pop()?;
                    println!("{}", v);
                }
                OpCode::Pop => {
                    stack.pop()?;
                }
                OpCode::DefineGlobal => {
                    let global_slot = self.read_stack_slot(chunk, ip)?;
                    let value = stack.pop()?;
                    if self.globals.len() == global_slot {
                        self.globals.push(value);
                    } else if self.globals.len() > global_slot {
                        self.globals[global_slot] = value;
                    } else {
                        // global_slot definition out of order
                        panic!("global definition out of order bug");
                    }
                }
                OpCode::GetGlobal => {
                    let global_slot = self.read_stack_slot(chunk, ip)?;
                    let value = self.globals[global_slot];
                    stack.push(value)?;
                }
                OpCode::SetGlobal => {
                    let global_slot = self.read_stack_slot(chunk, ip)?;
                    let value = stack.pop()?;
                    self.globals[global_slot] = value;
                }
                OpCode::GetLocal => {
                    let stack_slot = self.read_stack_slot(chunk, ip)?;
                    let value = unsafe { stack.stack[stack_slot].assume_init() };
                    stack.push(value)?;
                }
                OpCode::SetLocal => {
                    let stack_slot = self.read_stack_slot(chunk, ip)?;
                    let value = stack.pop()?;
                    stack.stack[stack_slot].write(value);
                }
                OpCode::JumpIfFalse => {
                    let jump_len = self.read_jump_len(chunk, ip)?;
                    let value = stack.pop()?;
                    if !value.to_bool() {
                        *ip += jump_len;
                    }
                }
                OpCode::Jump => {
                    let jump_len = self.read_jump_len(chunk, ip)?;
                    *ip += jump_len
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

    // String concatenation
    // Assumes that at least 1 of the Values is a string
    fn concat_strings(&self, left: Value, right: Value) -> Value {
        // One of them should be a string but allocate a string out of the other
        let left_str = left.create_string(&self.heap);
        let right_str = right.create_string(&self.heap);
        unsafe {
            let left_slice = (&*left_str).string_slice();
            let right_slice = (&*right_str).string_slice();

            let len = left_slice.len() + right_slice.len();
            let buf_ptr = self.heap.alloc_string_buf(len);

            let slice = slice::from_raw_parts_mut(buf_ptr, len);

            slice[..left_slice.len()].copy_from_slice(left_slice);
            slice[left_slice.len()..].copy_from_slice(right_slice);

            // Recreate an immutable slice
            let slice: &'static [u8] = std::mem::transmute(slice);

            let obj_ptr = self.heap.alloc_object();
            obj_ptr.write(Object::String(slice));
            Value::Object(obj_ptr)
        }
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

// Used during variable definition when we know the structure
fn value_to_string(v: Value) -> Option<String> {
    if let Value::Object(obj_ptr) = v {
        unsafe {
            match &*obj_ptr {
                Object::String(bs) => Some(std::str::from_utf8_unchecked(bs).to_string()),
            }
        }
    } else {
        None
    }
}
