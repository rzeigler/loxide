use anyhow::{anyhow, bail, Result};

use crate::{
    bytecode::BinaryOp,
    heap::{Heap, Value},
    reporter::{self, Reporter},
    scanner::{self, Keyword, Pos, Scanner, Symbol, Token, TokenType},
};

use super::Chunk;

pub struct ErrorHandler<'r, R> {
    reporter: &'r mut R,
    has_errored: bool,
}

impl<'r, R> ErrorHandler<'r, R> {
    pub fn new(reporter: &'r mut R) -> ErrorHandler<'r, R> {
        ErrorHandler {
            reporter,
            has_errored: false,
        }
    }
}

impl<'r, R> ErrorHandler<'r, R>
where
    R: Reporter,
{
    pub fn report(&mut self, pos: Pos, msg: &str) -> Result<(), CompilePanic> {
        // Only report the error when
        self.reporter.report(pos, msg);
        self.has_errored = true;
        // Returns for convenience to minimize the clutter of panic
        Err(COMPILE_PANIC)
    }
}

pub fn compile<'heap, R>(source: &str, reporter: &mut R, heap: &'heap mut Heap) -> Result<Chunk>
where
    R: Reporter,
{
    let mut scanner = Scanner::new(source);
    let mut error = ErrorHandler::new(reporter);
    let mut compile_state = CompileState::new();
    let mut chunk = Chunk::new();

    if let Err(_) = compile_stream(
        &mut error,
        &mut compile_state,
        &mut chunk,
        &mut scanner,
        heap,
    ) {
        bail!("compiler error");
    }

    chunk.emit_return(0);

    if error.has_errored {
        Err(anyhow!("compile error"))
    } else {
        Ok(chunk)
    }
}

pub(crate) struct CompilePanic {}

const COMPILE_PANIC: CompilePanic = CompilePanic {};

struct CompileState {
    globals: Vec<String>,
    locals: Vec<Local>,
    scope_depth: usize,
}

impl CompileState {
    fn new() -> CompileState {
        CompileState {
            globals: Vec::new(),
            locals: Vec::new(),
            scope_depth: 0,
        }
    }

    fn begin_scope(&mut self) {
        self.scope_depth += 1;
    }

    fn end_scope(&mut self) -> usize {
        self.scope_depth -= 1;

        let mut pops = 0;
        while self
            .locals
            .last()
            .map_or(false, |l| l.depth > self.scope_depth)
        {
            pops += 1;
            self.locals.pop();
        }

        pops
    }

    fn define_local<R>(
        &mut self,
        var: String,
        pos: Pos,
        reporter: &mut ErrorHandler<R>,
    ) -> Result<(), CompilePanic>
    where
        R: Reporter,
    {
        if let Some(local) = self.locals.iter().rev().find(|local| local.name == var) {
            if local.depth == self.scope_depth {
                return reporter.report(pos, "redefining an existing variable");
            }
        }
        self.locals.push(Local {
            name: var,
            depth: self.scope_depth,
        });
        Ok(())
    }

    fn resolve_local(&self, name: &str) -> Option<usize> {
        self.locals
            .iter()
            .enumerate()
            .rev()
            .find(|(_, local)| local.name == name)
            .map(|(i, _)| i)
    }

    fn define_global(&mut self, var: &str) -> usize {
        if self.resolve_global(var).is_none() {
            self.globals.push(var.to_string());
        }
        self.resolve_global(var).unwrap()
    }

    fn resolve_global(&self, name: &str) -> Option<usize> {
        self.globals
            .iter()
            .enumerate()
            .find(|(_, global)| *global == name)
            .map(|(i, _)| i)
    }
}

struct Local {
    name: String,
    depth: usize,
}

fn compile_stream<'heap, R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &'heap mut Heap,
) -> Result<()>
where
    R: Reporter,
{
    while !scanner.at_eof() {
        declaration(error, compile_state, chunk, scanner, heap);
    }

    if error.has_errored {
        Err(anyhow!("compilation failed"))
    } else {
        Ok(())
    }
}

// Switch from unwind by CompileError to synchronization here
// Higher levels should inspect the ErrorHandler state to determine if an error happened
fn declaration<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &mut Heap,
) where
    R: Reporter,
{
    let result = if scanner
        .peek()
        .map(|token| token.0 == Keyword::Var)
        .unwrap_or(false)
    {
        scanner.eat();
        var_declaration(error, compile_state, chunk, scanner, heap)
    } else {
        statement(error, compile_state, chunk, scanner, heap)
    };

    match result {
        Ok(_) => {}
        Err(_) => synchronize(scanner),
    }
}

fn synchronize(scanner: &mut Scanner) {
    while !scanner.at_eof() {
        // Check if we think we have found a statement boundary
        // If the next token is a semi-colon we should consume it and return
        // If the next token starts a larget construct like a class, var, etc, then we should _not_ consume it and return
        if let Ok(Token(ttype, _)) = scanner.peek() {
            match ttype {
                TokenType::Symbol(Symbol::Semicolon) => {
                    // consume and break;
                    scanner.eat();
                    return;
                }
                TokenType::Keyword(Keyword::Class)
                | TokenType::Keyword(Keyword::Fun)
                | TokenType::Keyword(Keyword::Var)
                | TokenType::Keyword(Keyword::For)
                | TokenType::Keyword(Keyword::If)
                | TokenType::Keyword(Keyword::While)
                | TokenType::Keyword(Keyword::Print)
                | TokenType::Keyword(Keyword::Return) => {
                    // don't consume and break
                    return;
                }
                _ => scanner.eat(), // Keep consuming
            }
        } else {
            // Token was an error, so we should consume it
            _ = scanner.next();
        }
    }
}

fn var_declaration<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let (identifier, pos) = match scanner.next() {
        Ok(Token(TokenType::Identifier(ident), pos)) => (ident, pos),
        Ok(Token(_, pos)) => return error.report(pos, "expected identifier"),
        Err(err) => return error.report(err.pos, "unrecognized token"),
    };

    if let Token(TokenType::Symbol(Symbol::Equal), _) = adapt_scanner_error(scanner.peek(), error)?
    {
        scanner.eat();
        expr(error, compile_state, chunk, scanner, heap)?;
    } else {
        chunk.emit_nil(pos.line);
    }

    expect_next_token(error, TokenType::Symbol(Symbol::Semicolon), scanner)?;

    if compile_state.scope_depth == 0 {
        let global_slot = u8::try_from(compile_state.define_global(identifier)).or_else(|_| {
            error
                .report(pos, "too many globals")
                .map(|_| unreachable!())
        })?;
        chunk.emit_define_global(global_slot, pos.line);
        Ok(())
    } else {
        compile_state.define_local(identifier.to_string(), pos, error)
    }
}

fn statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    match adapt_scanner_error(scanner.peek(), error)? {
        Token(TokenType::Keyword(Keyword::Print), _) => {
            print_statement(error, compile_state, chunk, scanner, heap)
        }
        Token(TokenType::Keyword(Keyword::If), _) => {
            if_statement(error, compile_state, chunk, scanner, heap)
        }
        Token(TokenType::Symbol(Symbol::LeftBrace), pos) => {
            compile_state.begin_scope();
            let result = block(error, compile_state, chunk, scanner, heap);
            let pops = compile_state.end_scope();
            for _ in 0..pops {
                chunk.emit_pop(pos.line);
            }
            result
        }
        _ => expr_statement(error, compile_state, chunk, scanner, heap),
    }
}

fn block<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    scanner.eat(); // eat the {

    while !scanner.at_eof()
        && !scanner
            .peek()
            .map_or(false, |next| next.0 == Symbol::RightBrace)
    {
        declaration(error, compile_state, chunk, scanner, heap)
    }

    expect_next_token(error, TokenType::Symbol(Symbol::RightBrace), scanner)
}

fn print_statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let pos = if let Ok(Token(TokenType::Keyword(Keyword::Print), print_pos)) = scanner.next() {
        print_pos
    } else {
        unreachable!();
    };
    expr(error, compile_state, chunk, scanner, heap)?;
    expect_next_token(error, TokenType::Symbol(Symbol::Semicolon), scanner)?;
    chunk.emit_print(pos.line);

    Ok(())
}

fn if_statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let pos = if let Ok(Token(TokenType::Keyword(Keyword::If), pos)) = scanner.next() {
        pos
    } else {
        // Already tested this above
        unreachable!()
    };
    expect_next_token(error, TokenType::Symbol(Symbol::LeftParen), scanner)?;
    expr(error, compile_state, chunk, scanner, heap)?;
    expect_next_token(error, TokenType::Symbol(Symbol::RightParen), scanner)?;

    let then_jump = chunk.emit_jump_if_false(pos.line);

    statement(error, compile_state, chunk, scanner, heap)?;

    if !chunk.patch_jump(then_jump) {
        return error.report(pos, "branch jumps too far");
    }

    if let Ok(Token(TokenType::Keyword(Keyword::Else), pos)) = scanner.next() {
        let else_jump = chunk.emit_jump(pos.line);

        statement(error, compile_state, chunk, scanner, heap)?;

        if !chunk.patch_jump(else_jump) {
            return error.report(pos, "branch jumps too far");
        }
    }

    Ok(())
}

fn expr_statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let line = match scanner.peek() {
        Ok(token) => token.1.line,
        Err(e) => e.pos.line,
    };
    expr(error, compile_state, chunk, scanner, heap)?;
    expect_next_token(error, TokenType::Symbol(Symbol::Semicolon), scanner)?;
    chunk.emit_pop(line);

    Ok(())
}

// I have diverged from lox's implementation slightly something similar https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
fn expr<'heap, R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &'heap mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    expr_precedence(error, compile_state, chunk, scanner, heap, 1)
}

fn expr_precedence<'heap, R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    heap: &'heap mut Heap,
    min_precedence: u8,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    match adapt_scanner_error(scanner.next(), error)? {
        Token(TokenType::Symbol(sym), pos) => {
            if sym == Symbol::LeftParen {
                expr_precedence(error, compile_state, chunk, scanner, heap, 0)?;
                expect_next_token(error, TokenType::Symbol(Symbol::RightParen), scanner)?;
            } else {
                expr_precedence(error, compile_state, chunk, scanner, heap, unary_prec(sym))?;
                match sym {
                    Symbol::Minus => chunk.emit_negate(pos.line),
                    Symbol::Bang => chunk.emit_not(pos.line),
                    s => return error.report(pos, &format!("not a unary symbol: {}", s)),
                }
            }
        }
        Token(TokenType::Number(num), pos) => chunk.emit_constant(num.into(), pos.line),
        Token(TokenType::Keyword(Keyword::True), pos) => chunk.emit_bool(true, pos.line),
        Token(TokenType::Keyword(Keyword::False), pos) => chunk.emit_bool(false, pos.line),
        Token(TokenType::Keyword(Keyword::Nil), pos) => chunk.emit_nil(pos.line),
        Token(TokenType::Identifier(identifier), pos) => {
            // Try and peek to see if we are the right side of an equals
            if let Token(TokenType::Symbol(Symbol::Equal), pos) =
                adapt_scanner_error(scanner.peek(), error)?
                // Only allow in assignment position
                && min_precedence <= 1
            {
                scanner.eat();
                expr_precedence(error, compile_state, chunk, scanner, heap, 2)?;

                // Try and resolve a local first, if its not, then I guess we are going with global
                if let Some(local_slot) = compile_state.resolve_local(identifier) {
                    chunk.emit_set_local(local_slot.try_into().unwrap(), pos.line);
                } else if let Some(global_slot) = compile_state.resolve_global(identifier) {
                    chunk.emit_set_global(global_slot.try_into().unwrap(), pos.line);
                } else {
                    _ = error.report(
                        pos,
                        &format!("unknown variable for assignment: {}", identifier),
                    )
                }
            } else {
                if let Some(local_slot) = compile_state.resolve_local(identifier) {
                    chunk.emit_get_local(local_slot.try_into().unwrap(), pos.line);
                } else if let Some(global_slot) = compile_state.resolve_global(identifier) {
                    chunk.emit_get_global(global_slot.try_into().unwrap(), pos.line);
                } else {
                    _ = error.report(pos, &format!("unknown variable for access: {}", identifier))
                }
            }
        }
        Token(TokenType::String(string), pos) => {
            let str_obj = heap.alloc_string_in_heap(string);
            chunk.emit_constant(Value::Object(str_obj), pos.line);
        }
        _ => todo!(),
    };

    // Equivalent to the while (prec <= getRule(token).precedence)
    loop {
        let token = adapt_scanner_error(scanner.peek(), error)?;
        match binary_prec(token.0.clone()) {
            None => break,
            Some(prec) if min_precedence > prec => break,
            Some(prec) => {
                _ = scanner.next();
                expr_precedence(error, compile_state, chunk, scanner, heap, prec + 1)?;
                write_chunk_binary_ops(token, chunk);
            }
        }
    }

    Ok(())
}

// Do extra reporting logic instead of just From
fn adapt_scanner_error<T, R>(
    result: Result<T, scanner::Error>,
    error: &mut ErrorHandler<R>,
) -> Result<T, CompilePanic>
where
    R: Reporter,
{
    match result {
        Ok(k) => Ok(k),
        Err(e) => {
            error.reporter.report(e.pos, "unrecognized token");
            Err(COMPILE_PANIC)
        }
    }
}

/* The table from the book
const PREC_ZERO: u8 = 0;
const PREC_ASSIGNMENT: u8 = 1; // =
const PREC_OR: u8 = 2; // or
const PREC_AND: u8 = 3; // and
const PREC_EQUALITY: u8 = 4; // == !=
const PREC_COMPARISON: u8 = 5; // < > <= >=
const PREC_TERM: u8 = 6; // + -
const PREC_FACTOR: u8 = 7; // * /
const PREC_UNARY: u8 = 8; // ! -
const PREC_CALL: u8 = 9; // . ()
const PREC_PRIMARY: u8 = 10;
*/

fn expect_next_token<R>(
    error: &mut ErrorHandler<R>,
    token: TokenType,
    scanner: &mut Scanner,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    match scanner.next() {
        Err(e) => error.report(e.pos, "unrecognized token"),
        Ok(Token(next, _)) if token == next => Ok(()),
        Ok(Token(_, pos)) => error.report(pos, &format!("expected {:?}", token)),
    }
}

fn unary_prec(sym: Symbol) -> u8 {
    match sym {
        Symbol::Bang | Symbol::Minus => 8,
        s => panic!("not a unary symbol: {}", s),
    }
}

fn binary_prec(token: TokenType) -> Option<u8> {
    match token {
        TokenType::Symbol(sym) => match sym {
            Symbol::Slash | Symbol::Star => Some(7),
            Symbol::Plus | Symbol::Minus => Some(6),
            Symbol::Less | Symbol::LessEqual | Symbol::Greater | Symbol::GreaterEqual => Some(5),
            Symbol::EqualEqual | Symbol::BangEqual => Some(4),
            // We handle equality precedence directly in the expr_precedence leading
            // Symbol::Equal => Some(1),
            _ => None,
        },
        TokenType::Keyword(key) => match key {
            Keyword::And => Some(3),
            Keyword::Or => Some(2),
            _ => None,
        },
        _ => None,
    }
}

fn write_chunk_binary_ops(token: Token, chunk: &mut Chunk) {
    let Token(ttype, pos) = token;
    match ttype {
        TokenType::Symbol(sym) => match sym {
            Symbol::Plus => chunk.emit_binary_op(BinaryOp::Add, pos.line),
            Symbol::Minus => chunk.emit_binary_op(BinaryOp::Subtract, pos.line),
            Symbol::Star => chunk.emit_binary_op(BinaryOp::Multiply, pos.line),
            Symbol::Slash => chunk.emit_binary_op(BinaryOp::Divide, pos.line),
            Symbol::EqualEqual => chunk.emit_binary_op(BinaryOp::Equal, pos.line),
            Symbol::BangEqual => {
                chunk.emit_binary_op(BinaryOp::Equal, pos.line);
                chunk.emit_negate(pos.line);
            }
            Symbol::Greater => chunk.emit_binary_op(BinaryOp::Greater, pos.line),
            Symbol::GreaterEqual => {
                chunk.emit_binary_op(BinaryOp::Less, pos.line);
                chunk.emit_not(pos.line);
            }
            Symbol::Less => chunk.emit_binary_op(BinaryOp::Less, pos.line),
            Symbol::LessEqual => {
                chunk.emit_binary_op(BinaryOp::Greater, pos.line);
                chunk.emit_not(pos.line);
            }
            s => panic!("not a binary op: {}", s),
        },
        TokenType::Keyword(key) => panic!("not a binary op: {}", key),
        t => panic!("not a binary op: {:?}", t),
    }
}
