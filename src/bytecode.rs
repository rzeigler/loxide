use crate::heap::Value;

#[derive(Debug)]
#[repr(u8)]
pub enum OpCode {
    Constant,
    Nil,
    True,
    False,
    Negate,
    Equal,
    Greater,
    Less,
    Not,
    Add,
    Subtract,
    Multiply,
    Divide,
    Print,
    Pop,
    DefineGlobal,
    GetGlobal,
    SetGlobal,
    GetLocal,
    SetLocal,
    JumpIfFalse,
    Jump,
    Loop,
    Return, // Return goes last as the sentinel for maximum opcode
}

impl OpCode {
    pub fn decode(op: u8) -> Option<OpCode> {
        if op <= OpCode::Return as u8 {
            // SAFETY: repr(u8) and InvalidSentinel is the last value
            Some(unsafe { std::mem::transmute(op) })
        } else {
            None
        }
    }
}

impl From<BinaryOp> for OpCode {
    fn from(value: BinaryOp) -> Self {
        match value {
            BinaryOp::Add => OpCode::Add,
            BinaryOp::Subtract => OpCode::Subtract,
            BinaryOp::Multiply => OpCode::Multiply,
            BinaryOp::Divide => OpCode::Divide,
            BinaryOp::Equal => OpCode::Equal,
            BinaryOp::Less => OpCode::Less,
            BinaryOp::Greater => OpCode::Greater,
        }
    }
}

pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
    Greater,
    Less,
}

#[derive(Debug, Clone)]
pub struct Chunk {
    code: Vec<u8>,
    constants: Vec<Value>,
    lines: Vec<usize>,
}

impl Chunk {
    pub fn new() -> Chunk {
        Chunk {
            code: Vec::new(),
            constants: Vec::new(),
            lines: Vec::new(),
        }
    }

    pub fn current_marker(&self) -> usize {
        self.code.len()
    }

    pub fn code(&self) -> &[u8] {
        &self.code
    }

    pub fn constants(&self) -> &[Value] {
        &self.constants
    }

    pub fn lines(&self) -> &[usize] {
        &self.lines
    }

    pub fn emit_return(&mut self, line: usize) {
        self.code.push(OpCode::Return as u8);
        self.lines.push(line);
    }

    pub fn emit_binary_op(&mut self, op: BinaryOp, line: usize) {
        self.code.push(OpCode::from(op) as u8);
        self.lines.push(line);
    }

    pub fn emit_constant(&mut self, constant: Value, line: usize) {
        let cindex = self.add_constant(constant);

        self.code.push(OpCode::Constant as u8);
        self.lines.push(line);

        self.code.push(cindex);
        self.lines.push(line);
    }

    pub fn emit_bool(&mut self, value: bool, line: usize) {
        self.code
            .push(if value { OpCode::True } else { OpCode::False } as u8);
        self.lines.push(line);
    }

    pub fn emit_nil(&mut self, line: usize) {
        self.code.push(OpCode::Nil as u8);
        self.lines.push(line);
    }

    pub fn emit_negate(&mut self, line: usize) {
        self.code.push(OpCode::Negate as u8);
        self.lines.push(line);
    }

    pub fn emit_not(&mut self, line: usize) {
        self.code.push(OpCode::Not as u8);
        self.lines.push(line);
    }

    pub fn emit_print(&mut self, line: usize) {
        self.code.push(OpCode::Print as u8);
        self.lines.push(line);
    }

    pub fn emit_pop(&mut self, line: usize) {
        self.code.push(OpCode::Pop as u8);
        self.lines.push(line);
    }

    pub fn emit_define_global(&mut self, global: u8, line: usize) {
        self.code.push(OpCode::DefineGlobal as u8);
        self.code.push(global);

        self.lines.push(line);
        self.lines.push(line);
    }

    pub fn emit_get_global(&mut self, global: u8, line: usize) {
        self.code.push(OpCode::GetGlobal as u8);
        self.code.push(global);

        self.lines.push(line);
        self.lines.push(line);
    }

    pub fn emit_set_global(&mut self, global: u8, line: usize) {
        self.code.push(OpCode::SetGlobal as u8);
        self.code.push(global);

        self.lines.push(line);
        self.lines.push(line);
    }

    pub fn emit_get_local(&mut self, local: u8, line: usize) {
        self.code.push(OpCode::GetLocal as u8);
        self.code.push(local);

        self.lines.push(line);
        self.lines.push(line);
    }

    pub fn emit_set_local(&mut self, local: u8, line: usize) {
        self.code.push(OpCode::SetLocal as u8);
        self.code.push(local);

        self.lines.push(line);
        self.lines.push(line);
    }

    pub fn emit_jump_if_false(&mut self, line: usize) -> usize {
        self.code.push(OpCode::JumpIfFalse as u8);
        self.code.push(u8::MAX);
        self.code.push(u8::MAX);

        self.lines.push(line);
        self.lines.push(line);
        self.lines.push(line);

        self.code.len() - 2
    }

    pub fn emit_jump(&mut self, line: usize) -> usize {
        self.code.push(OpCode::Jump as u8);
        self.code.push(u8::MAX);
        self.code.push(u8::MAX);

        self.lines.push(line);
        self.lines.push(line);
        self.lines.push(line);

        self.code.len() - 2
    }

    #[must_use]
    pub fn patch_jump(&mut self, jump_offset: usize) -> bool {
        let distance = self.code.len() - jump_offset - 2;
        if distance > u16::MAX.into() {
            false
        } else {
            // little endian
            let high_byte = (distance >> 8) as u8;
            let low_byte = distance as u8;

            self.code[jump_offset] = high_byte;
            self.code[jump_offset + 1] = low_byte;
            true
        }
    }

    #[must_use]
    pub fn emit_loop(&mut self, loop_start: usize, line: usize) -> bool {
        self.code.push(OpCode::Loop as u8);
        self.lines.push(line);

        let distance = self.code.len() - loop_start + 2;
        if distance > u16::MAX.into() {
            false
        } else {
            let high_byte = (distance >> 8) as u8;
            let low_byte = distance as u8;

            self.code.push(high_byte);
            self.code.push(low_byte);

            self.lines.push(line);
            self.lines.push(line);
            true
        }
    }

    pub fn add_constant(&mut self, constant: Value) -> u8 {
        if self.constants.len() == u8::MAX.into() {
            panic!("constant pool exhausted");
        }
        self.constants.push(constant);
        (self.constants.len() - 1) as u8
    }

    pub fn disassemble(&self, name: &str) {
        println!("==== {} ====", name);

        let mut offset = 0usize;
        while offset < self.code.len() {
            let mut result = String::new();
            offset = self.disassemble_inst(&mut result, offset);
            eprintln!("{}", result);
        }
    }

    pub fn disassemble_inst(&self, result: &mut String, offset: usize) -> usize {
        if offset > 0 && self.lines[offset - 1] == self.lines[offset] {
            result.push_str(&format!("{:04}    | ", offset));
        } else {
            result.push_str(&format!("{:04} {:4} ", offset, self.lines[offset]));
        }

        let offset = if let Some(op) = OpCode::decode(self.code[offset]) {
            // Nicely pad the result string
            result.push_str(&format!("{:<10} ", &format!("{:?}", op)));
            match op {
                OpCode::Negate | OpCode::Not => self.zero_arg_inst(offset),
                OpCode::True | OpCode::False => self.zero_arg_inst(offset),
                OpCode::Nil => self.zero_arg_inst(offset),
                OpCode::Less | OpCode::Greater | OpCode::Equal => self.zero_arg_inst(offset),
                OpCode::Add | OpCode::Subtract | OpCode::Multiply | OpCode::Divide => {
                    self.zero_arg_inst(offset)
                }
                // The statement codes
                OpCode::Print | OpCode::Pop => self.zero_arg_inst(offset),
                OpCode::DefineGlobal | OpCode::GetGlobal | OpCode::SetGlobal => {
                    self.constant_inst(result, offset)
                }
                OpCode::SetLocal | OpCode::GetLocal => self.local_inst(result, offset),
                OpCode::Constant => self.constant_inst(result, offset),
                OpCode::JumpIfFalse | OpCode::Jump => self.jump_inst(result, 1, offset),
                OpCode::Loop => self.jump_inst(result, -1, offset),
                OpCode::Return => self.zero_arg_inst(offset),
            }
        } else {
            println!("INVALID");
            offset + 1
        };

        offset
    }

    // We just assume all these things aren't malformed
    fn zero_arg_inst(&self, offset: usize) -> usize {
        offset + 1
    }

    fn constant_inst(&self, target: &mut String, offset: usize) -> usize {
        target.push_str(&format!(
            "{} ",
            self.constants[self.code[offset + 1] as usize]
        ));
        offset + 2
    }

    fn jump_inst(&self, target: &mut String, sign: i8, offset: usize) -> usize {
        let high_byte = self.code[offset + 1];
        let low_byte = self.code[offset + 2];
        let jump_len = ((high_byte as u16) << 8) | low_byte as u16;
        let position = if sign > 0 {
            offset + 3 + usize::from(jump_len)
        } else {
            offset + 3 - usize::from(jump_len)
        };
        target.push_str(&format!("{} -> {} ", offset, position));
        offset + 3
    }

    fn local_inst(&self, target: &mut String, offset: usize) -> usize {
        target.push_str(&format!("{} ", self.code[offset + 1]));
        offset + 2
    }
}
