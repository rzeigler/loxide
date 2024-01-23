#[derive(Debug)]
#[repr(u8)]
pub enum OpCode {
    Return,
    Constant,
    Negate,
    Add,
    Subtract,
    Multiply,
    Divide,
    // Goes last as sentinel for decoding
    InvalidSentinel,
}

impl OpCode {
    pub fn decode(op: u8) -> Option<OpCode> {
        if op < OpCode::InvalidSentinel as u8 {
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
        }
    }
}

pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
}

pub type Value = f64;

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

    pub fn write_return(&mut self, line: usize) {
        self.code.push(OpCode::Return as u8);
        self.lines.push(line);
    }

    pub fn write_binary_op(&mut self, op: BinaryOp, line: usize) {
        self.code.push(OpCode::from(op) as u8);
        self.lines.push(line);
    }

    pub fn write_constant(&mut self, constant: Value, line: usize) {
        let cindex = self.add_constant(constant);

        self.code.push(OpCode::Constant as u8);
        self.lines.push(line);

        self.code.push(cindex);
        self.lines.push(line);
    }

    pub fn write_negate(&mut self, line: usize) {
        self.code.push(OpCode::Negate as u8);
        self.lines.push(line);
    }

    fn add_constant(&mut self, constant: Value) -> u8 {
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
                OpCode::Return => self.simple_inst(offset),
                OpCode::Constant => self.constant_inst(result, offset),
                OpCode::Negate => self.simple_inst(offset),
                OpCode::Add | OpCode::Subtract | OpCode::Multiply | OpCode::Divide => {
                    self.simple_inst(offset)
                }
                OpCode::InvalidSentinel => {
                    unreachable!()
                }
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
