use std::{fmt::Debug, rc::Rc};

use anyhow::{anyhow, bail, Context, Result};

use crate::{
    bytecode::{Chunk, OpCode},
    heap::{Function, Heap, Object, Value},
};

pub struct Stack<V, const LIMIT: usize = 256> {
    stack: Vec<V>,
}

impl<V, const LIMIT: usize> Stack<V, LIMIT>
where
    V: Clone,
{
    pub fn new() -> Stack<V, LIMIT> {
        Stack {
            stack: Vec::with_capacity(LIMIT),
        }
    }

    pub fn push(&mut self, v: V) -> Result<()> {
        if self.stack.len() == LIMIT {
            bail!("stack limit exceeded");
        } else {
            self.stack.push(v);
            Ok(())
        }
    }

    pub fn pop(&mut self) -> Result<V> {
        self.stack.pop().ok_or_else(|| anyhow!("stack is empty"))
    }

    pub fn peek(&self) -> Result<V> {
        self.stack
            .last()
            .ok_or_else(|| anyhow!("stack is empty"))
            .cloned()
    }

    pub fn peek_mut(&mut self) -> Result<&mut V> {
        self.stack
            .last_mut()
            .ok_or_else(|| anyhow!("stack is empty"))
    }
}

impl<V, const LIMIT: usize> Debug for Stack<V, LIMIT>
where
    V: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();

        for v in self.stack.iter() {
            list.entry(v);
        }

        list.finish()
    }
}

#[derive(Debug, Clone)]
struct CallFrame {
    // Comparable to Value* slots in the book
    function: Rc<Function>,
    ip: usize,
    stack_slot_start: usize,
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

    pub fn interpret(&mut self, function: Function) -> Result<()> {
        // Diverging from the book because I'm not going to attempt to juggle pointers
        const FRAMES_MAX: usize = 64;
        const STACK_MAX: usize = FRAMES_MAX * 256;

        let mut stack: Stack<Value, STACK_MAX> = Stack::new();
        let mut frames: Stack<CallFrame, FRAMES_MAX> = Stack::new();

        frames
            .push(CallFrame {
                function: Rc::new(function),
                ip: 0,
                stack_slot_start: 0,
            })
            .unwrap(); // Its empty, shrug

        self.run(&mut stack, &mut frames)
    }

    fn run<const STACK_SIZE: usize, const FRAME_SIZE: usize>(
        &mut self,
        stack: &mut Stack<Value, STACK_SIZE>,
        frames: &mut Stack<CallFrame, FRAME_SIZE>,
    ) -> Result<()> {
        if TRACE_EXEC {
            eprintln!("==== EXEC ====");
        }
        loop {
            let frame = frames.peek_mut().unwrap();

            if TRACE_EXEC {
                let mut result = String::new();
                frame.function.chunk.disassemble_inst(&mut result, frame.ip);
                eprintln!("{} \t\tstack: {:?}", result, stack);
            }
            // Store this since read_inst will mutate the ip and we don't want to backtrack
            let last_ip = frame.ip;
            match self.read_inst(&frame.function.chunk, &mut frame.ip)? {
                OpCode::Return => {
                    return Ok(());
                }
                OpCode::Constant => {
                    let constant = self.read_constant(&frame.function.chunk, &mut frame.ip)?;
                    stack.push(constant)?;
                }
                OpCode::Negate => {
                    if let Value::Number(n) = stack.pop()? {
                        stack.push(Value::Number(-n))?;
                    } else {
                        return Err(raise_error(
                            &frame.function.chunk,
                            "type error: cannot negate operand",
                            last_ip,
                        ));
                    }
                }
                OpCode::Add => match self.pop_binary_operands(stack)? {
                    (Value::Number(l), Value::Number(r)) => {
                        stack.push(Value::Number(l + r))?;
                    }
                    (Value::Object(l), Value::Object(r)) => {
                        if l.is_string() || r.is_string() {
                            stack.push(self.concat_strings(Value::Object(l), Value::Object(r)))?;
                        } else {
                            return Err(raise_error(
                                &frame.function.chunk,
                                "type error: cannot add operands",
                                last_ip,
                            ));
                        }
                    }
                    _ => {
                        return Err(raise_error(
                            &frame.function.chunk,
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
                            &frame.function.chunk,
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
                            &frame.function.chunk,
                            "type error: cannot multiply operands",
                            last_ip,
                        ));
                    }
                }
                OpCode::Divide => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        if r == 0f64 {
                            return Err(raise_error(
                                &frame.function.chunk,
                                "divide by zero",
                                last_ip,
                            ));
                        }
                        stack.push(Value::Number(l / r))?;
                    } else {
                        return Err(raise_error(
                            &frame.function.chunk,
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
                    let (r, l) = self.pop_binary_operands(stack)?;
                    stack.push(Value::Bool(l == r))?;
                }
                OpCode::Greater => {
                    if let (Value::Number(r), Value::Number(l)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Bool(l > r))?;
                    } else {
                        return Err(raise_error(
                            &frame.function.chunk,
                            "type error: > requires numeric operands",
                            last_ip,
                        ));
                    }
                }
                OpCode::Less => {
                    if let (Value::Number(r), Value::Number(l)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Bool(l > r))?;
                    } else {
                        return Err(raise_error(
                            &frame.function.chunk,
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
                    let global_slot = self.read_stack_slot(&frame.function.chunk, &mut frame.ip)?;
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
                    let global_slot = self.read_stack_slot(&frame.function.chunk, &mut frame.ip)?;
                    let value = self.globals[global_slot].clone();
                    stack.push(value)?;
                }
                OpCode::SetGlobal => {
                    let global_slot = self.read_stack_slot(&frame.function.chunk, &mut frame.ip)?;
                    let value = stack.peek()?;
                    self.globals[global_slot] = value;
                }
                OpCode::GetLocal => {
                    let stack_slot = self.read_stack_slot(&frame.function.chunk, &mut frame.ip)?;
                    let value = stack.stack[frame.stack_slot_start + stack_slot].clone();
                    stack.push(value)?;
                }
                OpCode::SetLocal => {
                    let stack_slot = self.read_stack_slot(&frame.function.chunk, &mut frame.ip)?;
                    let value = stack.peek()?;
                    stack.stack[frame.stack_slot_start + stack_slot] = value;
                }
                OpCode::JumpIfFalse => {
                    let jump_len = self.read_jump_len(&frame.function.chunk, &mut frame.ip)?;
                    let value = stack.peek()?;
                    if !value.to_bool() {
                        frame.ip += jump_len;
                    }
                }
                OpCode::Jump => {
                    let jump_len = self.read_jump_len(&frame.function.chunk, &mut frame.ip)?;
                    frame.ip += jump_len;
                }
                OpCode::Loop => {
                    let jump_len = self.read_jump_len(&frame.function.chunk, &mut frame.ip)?;
                    frame.ip -= jump_len;
                }
            }
        }
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

    fn pop_binary_operands<const STACK: usize>(
        &mut self,
        stack: &mut Stack<Value, STACK>,
    ) -> Result<(Value, Value)> {
        let r = stack.pop()?;
        let l = stack.pop()?;
        Ok((l, r))
    }

    // String concatenation
    // Assumes that at least 1 of the Values is a string
    fn concat_strings(&self, left: Value, right: Value) -> Value {
        // One of them should be a string but allocate a string out of the other
        let left_str = left.create_string();
        let right_str = right.create_string();
        let mut result = left_str.string_slice().to_owned();
        result.push_str(right_str.string_slice());
        Value::Object(Object::String(Rc::new(result)))
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
