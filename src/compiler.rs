use std::rc::Rc;

use anyhow::{anyhow, bail, Result};

use crate::{
    bytecode::{BinaryOp, Chunk},
    heap::{Function, Heap, Object, Value},
    reporter::Reporter,
    scanner::{self, Keyword, Pos, Scanner, Symbol, Token, TokenType},
};

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

pub fn compile<'heap, R>(source: &str, reporter: &mut R, heap: &'heap mut Heap) -> Result<Function>
where
    R: Reporter,
{
    let mut scanner = Scanner::new(source);
    let mut error = ErrorHandler::new(reporter);
    let mut compile_state = CompileState::new();

    if let Err(_) = compile_stream(&mut error, &mut compile_state, &mut scanner, heap) {
        bail!("compiler error");
    }

    compile_state.function.chunk.emit_return(0);

    if error.has_errored {
        Err(anyhow!("compile error"))
    } else {
        Ok(compile_state.function)
    }
}

pub(crate) struct CompilePanic {}

const COMPILE_PANIC: CompilePanic = CompilePanic {};

struct CompileState {
    globals: Vec<String>,
    locals: Vec<Local>,
    scope_depth: usize,
    function: Function,
}

impl CompileState {
    fn new() -> CompileState {
        let mut locals = Vec::new();
        // http://craftinginterpreters.com/calls-and-functions.html#creating-functions-at-compile-time
        locals.push(Local {
            name: "".to_owned(),
            depth: 0,
        });
        CompileState {
            globals: Vec::new(),
            locals: locals,
            scope_depth: 0,
            function: Function::new_script(),
        }
    }

    fn new_fun(name: &str) -> CompileState {
        let mut locals = Vec::new();
        // http://craftinginterpreters.com/calls-and-functions.html#creating-functions-at-compile-time
        locals.push(Local {
            name: name.to_owned(),
            depth: 0,
        });
        CompileState {
            globals: Vec::new(),
            locals: locals,
            scope_depth: 0,
            function: Function::new(name),
        }
    }

    fn chunk_mut(&mut self) -> &mut Chunk {
        &mut self.function.chunk
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

    fn define_global(&mut self, var: &str) -> Option<u8> {
        if self.resolve_global(var).is_none() {
            if self.globals.len() == u8::MAX.into() {
                return None;
            }
            self.globals.push(var.to_string());
        }
        self.resolve_global(var)
    }

    fn resolve_global(&self, name: &str) -> Option<u8> {
        self.globals
            .iter()
            .enumerate()
            .find(|(_, global)| *global == name)
            .map(|(i, _)| i.try_into().unwrap())
    }
}

struct Local {
    name: String,
    depth: usize,
}

fn compile_stream<'heap, R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &'heap mut Heap,
) -> Result<()>
where
    R: Reporter,
{
    while !scanner.at_eof() {
        declaration(error, compile_state, scanner, heap);
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
    scanner: &mut Scanner,
    heap: &mut Heap,
) where
    R: Reporter,
{
    let result = if peek_next_token(TokenType::Keyword(Keyword::Var), scanner) {
        scanner.eat();
        var_declaration(error, compile_state, scanner, heap)
    } else if peek_next_token(TokenType::Keyword(Keyword::Fun), scanner) {
        scanner.eat();
        fun_declaration(error, compile_state, scanner, heap)
    } else {
        statement(error, compile_state, scanner, heap)
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
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let (identifier, pos) = expect_next_identifier(error, scanner)?;
    let identifier = identifier.to_string();

    if let Token(TokenType::Symbol(Symbol::Equal), _) = adapt_scanner_error(scanner.peek(), error)?
    {
        scanner.eat();
        expr(error, compile_state, scanner, heap)?;
    } else {
        compile_state.function.chunk.emit_nil(pos.line);
    }

    expect_next_token(error, TokenType::Symbol(Symbol::Semicolon), scanner)?;

    if compile_state.scope_depth == 0 {
        if let Some(global_slot) = compile_state.define_global(&identifier) {
            compile_state
                .chunk_mut()
                .emit_define_global(global_slot, pos.line);
        } else {
            // No need to panic
            _ = error.report(pos, "too many globals")
        }
        Ok(())
    } else {
        compile_state.define_local(identifier.to_string(), pos, error)
    }
}

fn fun_declaration<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let (identifier, pos) = expect_next_identifier(error, scanner)?;
    let identifier = identifier.to_owned();
    let global = compile_state.define_global(&identifier);

    function(
        error,
        compile_state,
        scanner,
        heap,
        &identifier,
        pos.clone(),
        false,
    )?;

    if let Some(global) = global {
        compile_state
            .chunk_mut()
            .emit_define_global(global, pos.line);
    } else {
        // No need to panic
        _ = error.report(pos, "too many globals");
    }

    Ok(())
}

fn function<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &mut Heap,
    name: &str,
    pos: Pos,
    is_method: bool,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let mut inner_state = CompileState::new_fun(name);
    inner_state.begin_scope();

    expect_next_token(error, TokenType::Symbol(Symbol::LeftParen), scanner)?;

    if !peek_next_token(TokenType::Symbol(Symbol::RightParen), scanner) {
        loop {
            if inner_state.function.arity == u8::MAX {
                _ = error.report(pos, "cannot have more than 255 parameters")
            } else {
                inner_state.function.arity += 1;
            }
            let (ident, pos) = expect_next_identifier(error, scanner)?;
            _ = inner_state.define_local(ident.to_string(), pos, error);
            if peek_next_token(TokenType::Symbol(Symbol::Comma), scanner) {
                scanner.eat();
            } else {
                break;
            }
        }
    }

    expect_next_token(error, TokenType::Symbol(Symbol::RightParen), scanner)?;
    expect_next_token(error, TokenType::Symbol(Symbol::LeftBrace), scanner)?;
    block(error, &mut inner_state, scanner, heap)?;

    inner_state.end_scope();

    compile_state.chunk_mut().emit_constant(
        Value::Object(Object::Function(Rc::new(inner_state.function))),
        pos.line,
    );

    Ok(())
}

fn statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    match adapt_scanner_error(scanner.peek(), error)? {
        Token(TokenType::Keyword(Keyword::Print), _) => {
            print_statement(error, compile_state, scanner, heap)
        }
        Token(TokenType::Keyword(Keyword::If), _) => {
            if_statement(error, compile_state, scanner, heap)
        }
        Token(TokenType::Keyword(Keyword::While), _) => {
            while_statement(error, compile_state, scanner, heap)
        }
        Token(TokenType::Keyword(Keyword::For), _) => {
            for_statement(error, compile_state, scanner, heap)
        }
        Token(TokenType::Symbol(Symbol::LeftBrace), pos) => {
            scanner.eat(); // consume {
            compile_state.begin_scope();
            let result = block(error, compile_state, scanner, heap);
            let pops = compile_state.end_scope();
            for _ in 0..pops {
                compile_state.function.chunk.emit_pop(pos.line);
            }
            result
        }
        _ => expr_statement(error, compile_state, scanner, heap),
    }
}

fn block<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    while !scanner.at_eof()
        && !scanner
            .peek()
            .map_or(false, |next| next.0 == Symbol::RightBrace)
    {
        declaration(error, compile_state, scanner, heap)
    }

    expect_next_token(error, TokenType::Symbol(Symbol::RightBrace), scanner)
}

fn print_statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
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
    expr(error, compile_state, scanner, heap)?;
    expect_next_token(error, TokenType::Symbol(Symbol::Semicolon), scanner)?;
    compile_state.function.chunk.emit_print(pos.line);

    Ok(())
}

fn if_statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
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
    expr(error, compile_state, scanner, heap)?;
    expect_next_token(error, TokenType::Symbol(Symbol::RightParen), scanner)?;

    let skip_if_jump = compile_state.function.chunk.emit_jump_if_false(pos.line);
    compile_state.function.chunk.emit_pop(pos.line);

    statement(error, compile_state, scanner, heap)?;

    let skip_else_jump = compile_state.function.chunk.emit_jump(pos.line);
    if !compile_state.function.chunk.patch_jump(skip_if_jump) {
        return error.report(pos, "branch jumps too far");
    }
    compile_state.function.chunk.emit_pop(pos.line);
    // There's always a pop that we shouldn't jump over
    if let Ok(Token(TokenType::Keyword(Keyword::Else), _)) = scanner.peek() {
        scanner.eat();
        statement(error, compile_state, scanner, heap)?;
    }
    if !compile_state.function.chunk.patch_jump(skip_else_jump) {
        return error.report(pos, "branch jumps to far");
    }

    Ok(())
}

fn while_statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let pos = if let Ok(Token(TokenType::Keyword(Keyword::While), pos)) = scanner.next() {
        pos
    } else {
        // Already tested this above
        unreachable!()
    };

    let loop_start = compile_state.function.chunk.current_marker();
    expect_next_token(error, TokenType::Symbol(Symbol::LeftParen), scanner)?;
    expr(error, compile_state, scanner, heap)?;
    expect_next_token(error, TokenType::Symbol(Symbol::RightParen), scanner)?;

    // TODO: The looping
    let exit_jump = compile_state.function.chunk.emit_jump_if_false(pos.line);
    compile_state.function.chunk.emit_pop(pos.line);

    statement(error, compile_state, scanner, heap)?;

    if !compile_state.function.chunk.emit_loop(loop_start, pos.line) {
        return error.report(pos, "cannot jump that far");
    }

    if !compile_state.function.chunk.patch_jump(exit_jump) {
        return error.report(pos, "cannot jump that far");
    }
    compile_state.function.chunk.emit_pop(pos.line);

    Ok(())
}

fn for_statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let pos = if let Ok(Token(TokenType::Keyword(Keyword::For), pos)) = scanner.next() {
        pos
    } else {
        // Already tested this above
        unreachable!()
    };

    compile_state.begin_scope();

    expect_next_token(error, TokenType::Symbol(Symbol::LeftParen), scanner)?;

    // Both of these will consume the semi-colon
    if peek_next_token(TokenType::Keyword(Keyword::Var), scanner) {
        scanner.eat();
        var_declaration(error, compile_state, scanner, heap)?
    } else if !peek_next_token(TokenType::Symbol(Symbol::Semicolon), scanner) {
        expr_statement(error, compile_state, scanner, heap)?;
    }

    let mut loop_start = compile_state.function.chunk.current_marker();

    // There is no condition, so true...
    if peek_next_token(TokenType::Symbol(Symbol::Semicolon), scanner) {
        compile_state.function.chunk.emit_bool(true, pos.line);
    } else {
        expr(error, compile_state, scanner, heap)?;
    };
    let exit_jump = compile_state.function.chunk.emit_jump_if_false(pos.line);
    compile_state.function.chunk.emit_pop(pos.line);

    expect_next_token(error, TokenType::Symbol(Symbol::Semicolon), scanner)?;

    // Do the cross jump dance to enable single pass
    if !peek_next_token(TokenType::Symbol(Symbol::RightParen), scanner) {
        // TODO: This is the wrong line...
        let body_jump = compile_state.function.chunk.emit_jump(pos.line);
        let incr_start = compile_state.function.chunk.current_marker();

        expr(error, compile_state, scanner, heap)?;
        compile_state.function.chunk.emit_pop(pos.line);

        if !compile_state.function.chunk.emit_loop(loop_start, pos.line) {
            return error.report(pos, "cannot jump that far");
        }
        loop_start = incr_start;
        if !compile_state.function.chunk.patch_jump(body_jump) {
            return error.report(pos, "cannot jump that far");
        }
    }

    expect_next_token(error, TokenType::Symbol(Symbol::RightParen), scanner)?;

    statement(error, compile_state, scanner, heap)?;

    if !compile_state.function.chunk.emit_loop(loop_start, pos.line) {
        return error.report(pos, "cannot jump that far");
    }

    if !compile_state.function.chunk.patch_jump(exit_jump) {
        return error.report(pos, "cannot jump that far");
    }
    compile_state.function.chunk.emit_pop(pos.line);

    compile_state.end_scope();

    Ok(())
}

fn expr_statement<R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
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
    expr(error, compile_state, scanner, heap)?;
    expect_next_token(error, TokenType::Symbol(Symbol::Semicolon), scanner)?;
    compile_state.function.chunk.emit_pop(line);

    Ok(())
}

// I have diverged from lox's implementation slightly something similar https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
fn expr<'heap, R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &'heap mut Heap,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    expr_precedence(error, compile_state, scanner, heap, 1)
}

fn expr_precedence<'heap, R>(
    error: &mut ErrorHandler<R>,
    compile_state: &mut CompileState,
    scanner: &mut Scanner,
    heap: &'heap mut Heap,
    min_precedence: u8,
) -> Result<(), CompilePanic>
where
    R: Reporter,
{
    let can_assign = min_precedence <= 1;

    match adapt_scanner_error(scanner.next(), error)? {
        Token(TokenType::Symbol(sym), pos) => {
            if sym == Symbol::LeftParen {
                expr_precedence(error, compile_state, scanner, heap, 0)?;
                expect_next_token(error, TokenType::Symbol(Symbol::RightParen), scanner)?;
            } else {
                expr_precedence(error, compile_state, scanner, heap, unary_prec(sym))?;
                match sym {
                    Symbol::Minus => compile_state.function.chunk.emit_negate(pos.line),
                    Symbol::Bang => compile_state.function.chunk.emit_not(pos.line),
                    s => return error.report(pos, &format!("not a unary symbol: {}", s)),
                }
            }
        }
        Token(TokenType::Number(num), pos) => compile_state
            .chunk_mut()
            .emit_constant(num.into(), pos.line),
        Token(TokenType::Keyword(Keyword::True), pos) => {
            compile_state.function.chunk.emit_bool(true, pos.line)
        }
        Token(TokenType::Keyword(Keyword::False), pos) => {
            compile_state.function.chunk.emit_bool(false, pos.line)
        }
        Token(TokenType::Keyword(Keyword::Nil), pos) => {
            compile_state.function.chunk.emit_nil(pos.line)
        }
        Token(TokenType::Identifier(identifier), pos) => {
            // Try and peek to see if we are the right side of an equals
            if let Token(TokenType::Symbol(Symbol::Equal), pos) =
                adapt_scanner_error(scanner.peek(), error)?
                // Only allow in assignment position
                && can_assign
            {
                scanner.eat();
                expr_precedence(error, compile_state, scanner, heap, 2)?;

                // Try and resolve a local first, if its not, then I guess we are going with global
                if let Some(local_slot) = compile_state.resolve_local(identifier) {
                    compile_state
                        .chunk_mut()
                        .emit_set_local(local_slot.try_into().unwrap(), pos.line);
                } else if let Some(global_slot) = compile_state.resolve_global(identifier) {
                    compile_state
                        .chunk_mut()
                        .emit_set_global(global_slot.try_into().unwrap(), pos.line);
                } else {
                    _ = error.report(
                        pos,
                        &format!("unknown variable for assignment: {}", identifier),
                    )
                }
            } else {
                if let Some(local_slot) = compile_state.resolve_local(identifier) {
                    compile_state
                        .chunk_mut()
                        .emit_get_local(local_slot.try_into().unwrap(), pos.line);
                } else if let Some(global_slot) = compile_state.resolve_global(identifier) {
                    compile_state
                        .chunk_mut()
                        .emit_get_global(global_slot.try_into().unwrap(), pos.line);
                } else {
                    _ = error.report(pos, &format!("unknown variable for access: {}", identifier))
                }
            }
        }
        Token(TokenType::String(string), pos) => {
            compile_state.function.chunk.emit_constant(
                Value::Object(Object::String(Rc::new(string.to_owned()))),
                pos.line,
            );
        }
        _ => todo!(),
    };

    // Equivalent to the while (prec <= getRule(token).precedence)
    loop {
        let Token(ttype, pos) = adapt_scanner_error(scanner.peek(), error)?;
        match binary_prec(ttype.clone()) {
            None => break,
            Some(prec) if min_precedence > prec => break,
            Some(prec) => {
                scanner.eat();
                match ttype {
                    TokenType::Symbol(sym) => match sym {
                        Symbol::Plus => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Add, pos.line);
                        }
                        Symbol::Minus => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Subtract, pos.line)
                        }
                        Symbol::Star => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Multiply, pos.line)
                        }
                        Symbol::Slash => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Divide, pos.line)
                        }
                        Symbol::EqualEqual => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Equal, pos.line)
                        }
                        Symbol::BangEqual => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Equal, pos.line);
                            compile_state.function.chunk.emit_negate(pos.line);
                        }
                        Symbol::Greater => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Greater, pos.line)
                        }
                        Symbol::GreaterEqual => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Less, pos.line);
                            compile_state.function.chunk.emit_not(pos.line);
                        }
                        Symbol::Less => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Less, pos.line)
                        }
                        Symbol::LessEqual => {
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            compile_state
                                .chunk_mut()
                                .emit_binary_op(BinaryOp::Greater, pos.line);
                            compile_state.function.chunk.emit_not(pos.line);
                        }
                        _ => unreachable!(),
                    },
                    TokenType::Keyword(key) => match key {
                        Keyword::And => {
                            let end_jump =
                                compile_state.function.chunk.emit_jump_if_false(pos.line);
                            compile_state.function.chunk.emit_pop(pos.line);
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            if !compile_state.function.chunk.patch_jump(end_jump) {
                                return error.report(pos, "cannot jump that far");
                            }
                        }
                        Keyword::Or => {
                            let else_jump =
                                compile_state.function.chunk.emit_jump_if_false(pos.line);
                            let end_jump = compile_state.function.chunk.emit_jump(pos.line);
                            if !compile_state.function.chunk.patch_jump(else_jump) {
                                return error.report(pos, "cannot jump that far");
                            }
                            compile_state.function.chunk.emit_pop(pos.line);
                            expr_precedence(error, compile_state, scanner, heap, prec + 1)?;
                            if !compile_state.function.chunk.patch_jump(end_jump) {
                                return error.report(pos, "cannot jump that far");
                            }
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
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

fn peek_next_token(token: TokenType, scanner: &Scanner) -> bool {
    if let Ok(Token(ttype, _)) = scanner.peek() {
        ttype == token
    } else {
        false
    }
}

fn expect_next_identifier<'s, R>(
    error: &mut ErrorHandler<R>,
    scanner: &'s mut Scanner,
) -> Result<(&'s str, Pos), CompilePanic>
where
    R: Reporter,
{
    match scanner.next() {
        Ok(Token(TokenType::Identifier(ident), pos)) => Ok((ident, pos)),
        Ok(Token(_, pos)) => error
            .report(pos, "expected identifier")
            .map(|_| unreachable!()),
        Err(err) => error
            .report(err.pos, "unrecognized token")
            .map(|_| unreachable!()),
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
