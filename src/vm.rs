use std::{collections::HashMap, fmt::Debug, rc::Rc};

use anyhow::{anyhow, bail, Context, Error, Result};

use crate::{
    bytecode::{Chunk, OpCode},
    value::{Function, NativeFunction, Object, Value},
};

struct Stack<V, const LIMIT: usize = 256> {
    stack: Vec<V>,
}

impl<V, const LIMIT: usize> Stack<V, LIMIT>
where
    V: Clone,
{
    fn new() -> Stack<V, LIMIT> {
        Stack {
            stack: Vec::with_capacity(LIMIT),
        }
    }

    fn push(&mut self, v: V) -> Result<()> {
        if self.stack.len() == LIMIT {
            bail!("stack limit exceeded");
        } else {
            self.stack.push(v);
            Ok(())
        }
    }

    fn pop(&mut self) -> V {
        self.stack.pop().expect("stack is empty")
    }

    fn peek(&self) -> &V {
        self.stack.last().expect("stack is empty")
    }

    fn peek_n(&self, skip: usize) -> &V {
        self.stack
            .iter()
            .rev()
            .skip(skip)
            .next()
            .expect("stack is not that high")
    }

    fn peek_mut(&mut self) -> &mut V {
        self.stack.last_mut().expect("stack is empty")
    }

    fn len(&self) -> usize {
        self.stack.len()
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
    globals: HashMap<String, Value>,
}

impl<const TRACE_EXEC: bool> VM<TRACE_EXEC> {
    pub fn new() -> VM<TRACE_EXEC> {
        VM {
            globals: HashMap::new(),
        }
    }

    pub fn define_native(&mut self, name: &'static str, function: NativeFunction) {
        self.globals.insert(
            name.to_string(),
            Value::Object(Object::NativeFunction(name, function)),
        );
    }

    pub fn interpret(&mut self, function: Function) -> Result<()> {
        let init_fn = Rc::new(function);

        // Diverging from the book because I'm not going to attempt to juggle pointers
        const FRAMES_MAX: usize = 64;
        const STACK_MAX: usize = FRAMES_MAX * 256;

        let mut stack: Stack<Value, STACK_MAX> = Stack::new();
        // per http://craftinginterpreters.com/calls-and-functions.html#creating-functions-at-compile-time
        // push a dummy value to align for intermediate testing
        // I'm assuming this is the ret slot
        stack
            .push(Value::Object(Object::Function(init_fn.clone())))
            .unwrap();

        let mut frames: Stack<CallFrame, FRAMES_MAX> = Stack::new();

        frames
            .push(CallFrame {
                function: init_fn,
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
            let frame = frames.peek_mut();

            if TRACE_EXEC {
                let mut result = String::new();
                frame.function.chunk.disassemble_inst(&mut result, frame.ip);
                eprintln!("{} \t\tstack: {:?}", result, stack);
            }
            // Store this since read_inst will mutate the ip and we don't want to backtrack
            match self.read_inst(&frame.function.chunk, &mut frame.ip)? {
                OpCode::Return => {
                    let ret = stack.pop();
                    let frame = frames.pop();
                    if frames.stack.is_empty() {
                        // At this point, we have popped the script, so we can assert the stack is empty
                        // to verify nothing went wrong
                        assert!(stack.stack.is_empty());
                        return Ok(());
                    } else {
                        stack.stack.drain(frame.stack_slot_start..);
                        stack.push(ret)?; // should be infallible, follows a pop
                    }
                }
                OpCode::Constant => {
                    let constant = self.read_constant(&frame.function.chunk, &mut frame.ip)?;
                    stack.push(constant)?;
                }
                OpCode::Negate => {
                    if let Value::Number(n) = stack.pop() {
                        stack.push(Value::Number(-n))?;
                    } else {
                        return Err(raise_error(
                            &frames.stack[..],
                            "type error: cannot negate operand",
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
                                &frames.stack[..],
                                "type error: cannot add operands",
                            ));
                        }
                    }
                    _ => {
                        return Err(raise_error(
                            &frames.stack[..],
                            "type error: cannot add operands",
                        ))
                    }
                },
                OpCode::Subtract => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Number(l - r))?;
                    } else {
                        return Err(raise_error(
                            &frames.stack[..],
                            "type error: cannot subtract operands",
                        ));
                    }
                }
                OpCode::Multiply => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Number(l * r))?;
                    } else {
                        return Err(raise_error(
                            &frames.stack[..],
                            "type error: cannot multiply operands",
                        ));
                    }
                }
                OpCode::Divide => {
                    if let (Value::Number(l), Value::Number(r)) = self.pop_binary_operands(stack)? {
                        if r == 0f64 {
                            return Err(raise_error(&frames.stack[..], "divide by zero"));
                        }
                        stack.push(Value::Number(l / r))?;
                    } else {
                        return Err(raise_error(
                            &frames.stack[..],
                            "type error: cannot divide operands",
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
                    let v = stack.pop().to_bool();
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
                            &frames.stack[..],
                            "type error: > requires numeric operands",
                        ));
                    }
                }
                OpCode::Less => {
                    if let (Value::Number(r), Value::Number(l)) = self.pop_binary_operands(stack)? {
                        stack.push(Value::Bool(l > r))?;
                    } else {
                        return Err(raise_error(
                            &frames.stack[..],
                            "type error: < requires numeric operands",
                        ));
                    }
                }
                OpCode::Print => {
                    let v = stack.pop();
                    println!("{}", v);
                }
                OpCode::Pop => {
                    stack.pop();
                }
                OpCode::DefineGlobal => {
                    if let Value::Object(Object::String(s)) =
                        self.read_constant(&frame.function.chunk, &mut frame.ip)?
                    {
                        let value = stack.pop();
                        self.globals.insert(s.as_ref().to_owned(), value);
                    } else {
                        panic!("miscompilation: global constant was not a string")
                    }
                }
                OpCode::GetGlobal => {
                    if let Value::Object(Object::String(s)) =
                        self.read_constant(&frame.function.chunk, &mut frame.ip)?
                    {
                        match self.globals.get(s.as_ref()).clone() {
                            Some(value) => {
                                stack.push(value.clone())?;
                            }
                            None => {
                                return Err(raise_error(
                                    &frames.stack[..],
                                    &format!("unknown global {}", s),
                                ))
                            }
                        }
                    } else {
                        panic!("miscompilation: global constant was not a string")
                    }
                }
                OpCode::SetGlobal => {
                    if let Value::Object(Object::String(s)) =
                        self.read_constant(&frame.function.chunk, &mut frame.ip)?
                    {
                        if let Some(global) = self.globals.get_mut(s.as_ref()) {
                            *global = stack.peek().clone();
                        } else {
                            return Err(raise_error(
                                &frames.stack[..],
                                &format!("unknown global {}", s),
                            ));
                        }
                    } else {
                        panic!("miscompilation: global constant was not a string")
                    }
                }
                OpCode::GetLocal => {
                    let stack_slot = self.read_u8(&frame.function.chunk, &mut frame.ip)?;
                    let value =
                        stack.stack[frame.stack_slot_start + usize::from(stack_slot)].clone();
                    stack.push(value)?;
                }
                OpCode::SetLocal => {
                    let stack_slot = self.read_u8(&frame.function.chunk, &mut frame.ip)?;
                    let value = stack.peek();
                    stack.stack[frame.stack_slot_start + usize::from(stack_slot)] = value.clone();
                }
                OpCode::JumpIfFalse => {
                    let jump_len = self.read_u16(&frame.function.chunk, &mut frame.ip)?;
                    let value = stack.peek();
                    if !value.to_bool() {
                        frame.ip += usize::from(jump_len);
                    }
                }
                OpCode::Jump => {
                    let jump_len = self.read_u16(&frame.function.chunk, &mut frame.ip)?;
                    frame.ip += usize::from(jump_len);
                }
                OpCode::Loop => {
                    let jump_len = self.read_u16(&frame.function.chunk, &mut frame.ip)?;
                    frame.ip -= usize::from(jump_len);
                }
                OpCode::Call => {
                    let args = usize::from(self.read_u8(&frame.function.chunk, &mut frame.ip)?);
                    match stack.peek_n(args) {
                        Value::Object(Object::Function(fun)) => {
                            if usize::from(fun.arity) != args {
                                return Err(raise_error(
                                    &frames.stack[..],
                                    "incorrect number of arguments",
                                ));
                            }
                            frames.push(CallFrame {
                                function: fun.clone(),
                                ip: 0,
                                stack_slot_start: stack.len() - args - 1,
                            })?;
                        }
                        Value::Object(Object::NativeFunction(_, fun)) => {
                            let first_arg_slot = stack.len() - args;
                            let result = match fun(&stack.stack[first_arg_slot..]) {
                                Ok(o) => o,
                                Err(e) => {
                                    return Err(raise_error(&frames.stack[..], &e.to_string()))
                                }
                            };
                            stack.stack.drain(first_arg_slot - 1..);
                            stack.push(result)?;
                        }
                        _ => return Err(raise_error(&frames.stack[..], "not a callable")),
                    }
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

    fn read_u8(&mut self, chunk: &Chunk, ip: &mut usize) -> Result<u8> {
        let offset = read_code_at_ip(chunk, *ip)?;
        *ip += 1;
        Ok(offset.into())
    }

    fn read_u16(&mut self, chunk: &Chunk, ip: &mut usize) -> Result<u16> {
        let high_byte = read_code_at_ip(chunk, *ip)?;
        let low_byte = read_code_at_ip(chunk, *ip + 1)?;
        *ip += 2;

        let count = ((high_byte as u16) << 8) | (low_byte as u16);
        Ok(count)
    }

    fn pop_binary_operands<const STACK: usize>(
        &mut self,
        stack: &mut Stack<Value, STACK>,
    ) -> Result<(Value, Value)> {
        let r = stack.pop();
        let l = stack.pop();
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

fn raise_error(frames: &[CallFrame], msg: &str) -> Error {
    eprintln!("stack trace");
    for frame in frames.iter().rev() {
        eprintln!(
            "[line {}] in {}",
            frame.function.chunk.lines()[frame.ip - 1],
            frame.function.name
        )
    }
    anyhow!(msg.to_owned())
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
