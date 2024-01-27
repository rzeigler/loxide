use anyhow::{anyhow, bail, Context, Result};

use crate::{
    bytecode::{BinaryOp, Value},
    reporter::Reporter,
    scanner::{Keyword, Pos, Scanner, Symbol, Token, TokenType},
};

use super::Chunk;

pub struct ErrorHandler<'r, R> {
    reporter: &'r mut R,
    in_panic: bool,
    has_errored: bool,
}

impl<'r, R> ErrorHandler<'r, R> {
    pub fn new(reporter: &'r mut R) -> ErrorHandler<'r, R> {
        ErrorHandler {
            reporter,
            in_panic: false,
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
        self.in_panic = true;
        // Returns for convenience to minimize the clutter of panic
        Err(COMPILE_PANIC)
    }
}

pub fn compile<R>(source: &str, reporter: &mut R) -> Result<Chunk>
where
    R: Reporter,
{
    let mut scanner = Scanner::new(source);
    let mut error = ErrorHandler::new(reporter);
    let mut chunk = Chunk::new();

    if let Err(_) = compile_stream(&mut error, &mut chunk, &mut scanner) {
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

fn compile_stream<R>(
    error: &mut ErrorHandler<R>,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    expr(error, chunk, scanner)
}

// I have diverged from lox's implementation slightly something similar https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
fn expr<R>(
    error: &mut ErrorHandler<R>,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    compile_precedence(error, chunk, scanner, 1)
}

fn compile_precedence<R>(
    error: &mut ErrorHandler<R>,
    chunk: &mut Chunk,
    scanner: &mut Scanner,
    min_precedence: u8,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    match scanner.next() {
        Ok(Token(TokenType::Symbol(sym), pos)) => {
            if sym == Symbol::LeftParen {
                compile_precedence(error, chunk, scanner, 0)?;
                expect_next_token(error, TokenType::Symbol(Symbol::RightParen), scanner)?;
            } else {
                compile_precedence(error, chunk, scanner, unary_prec(sym))?;
                match sym {
                    Symbol::Minus => chunk.emit_negate(pos.line),
                    Symbol::Bang => chunk.emit_not(pos.line),
                    s => return error.report(pos, &format!("not a unary symbol: {}", s)),
                }
            }
        }
        Ok(Token(TokenType::Number(num), pos)) => chunk.emit_constant(num.into(), pos.line),
        Ok(Token(TokenType::Keyword(Keyword::True), pos)) => chunk.emit_bool(true, pos.line),
        Ok(Token(TokenType::Keyword(Keyword::False), pos)) => chunk.emit_bool(false, pos.line),
        Ok(Token(TokenType::Keyword(Keyword::Nil), pos)) => chunk.emit_nil(pos.line),
        Err(e) => {
            return error.report(e.pos, "unrecognized token");
        }
        _ => todo!(),
    };

    // Equivalent to the while (prec <= getRule(token).precedence)
    loop {
        match scanner.peek() {
            Err(e) => {
                _ = scanner.next();
                return error.report(e.pos, "unrecognized token");
            }
            Ok(token) => match binary_prec(token.0.clone()) {
                None => break,
                Some(prec) if min_precedence > prec => break,
                Some(prec) => {
                    _ = scanner.next();
                    compile_precedence(error, chunk, scanner, prec + 1)?;
                    write_chunk_binary_ops(token, chunk);
                }
            },
        }
    }

    Ok(())
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
            Symbol::Equal => Some(1),
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
