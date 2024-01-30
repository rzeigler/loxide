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
                OpCode::Negate | OpCode::Not => self.simple_inst(offset),
                OpCode::True | OpCode::False => self.simple_inst(offset),
                OpCode::Nil => self.simple_inst(offset),
                OpCode::Less | OpCode::Greater | OpCode::Equal => self.simple_inst(offset),
                OpCode::Add | OpCode::Subtract | OpCode::Multiply | OpCode::Divide => {
                    self.simple_inst(offset)
                }
                // The statement codes
                OpCode::Print | OpCode::Pop => self.simple_inst(offset),
                OpCode::DefineGlobal => self.constant_inst(result, offset),
                OpCode::Constant => self.constant_inst(result, offset),
                OpCode::Return => self.simple_inst(offset),
            }
        } else {
            println!("INVALID");
            offset + 1
        };

        offset
    }

    // We just assume all these things aren't malformed
    fn simple_inst(&self, offset: usize) -> usize {
        offset + 1
    }

    fn constant_inst(&self, target: &mut String, offset: usize) -> usize {
        target.push_str(&format!(
            "{} ",
            self.constants[self.code[offset + 1] as usize]
        ));
        offset + 2
    }
}
