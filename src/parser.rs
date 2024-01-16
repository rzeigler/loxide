use std::io::Write;

use crate::ast::*;
use crate::scanner::Keyword;
use crate::scanner::Pos;
use crate::scanner::Scanner;
use crate::scanner::Symbol;
use crate::scanner::Token;
use crate::scanner::TokenType;
use ordered_float::OrderedFloat;
use thiserror::Error;

// Public error type that is returned from the API
#[derive(Error, Debug)]
#[error("parse error")]
pub struct Error {}

// For unwinding, we don't actually care that much about the internal cause which is reported through the reporter
#[derive(Error, Debug)]
#[error("internal parse error")]
struct ParsePanic {}

pub trait ErrorReporter {
    fn report(&mut self, pos: Pos, message: &str);
}

struct TestErrorReporter;

impl ErrorReporter for TestErrorReporter {
    fn report(&mut self, _pos: Pos, _message: &str) {}
}

pub struct WriteErrorReporter<'w, W>
where
    W: Write,
{
    // Store this as a mut reference so we can't accidentally lose something like stderr().lock() inside the reporter
    // that doesn't go out of scope and cause a deadlock
    write: &'w mut W,
}

impl<'w, W> WriteErrorReporter<'w, W>
where
    W: Write,
{
    pub fn new(write: &'w mut W) -> WriteErrorReporter<'w, W> {
        WriteErrorReporter { write }
    }
}

impl<'w, W> ErrorReporter for WriteErrorReporter<'w, W>
where
    W: Write,
{
    fn report(&mut self, pos: Pos, message: &str) {
        // If w ecan't write to our output: 🤷🏻‍♂️
        _ = write!(self.write, "error at {}: {}\n", pos, message);
    }
}

/// Track whether or not an error actually occurred and delegate to another error reporter
/// This is only meant to be used internally so that parse can piggy back on whether an error actually occurred
struct StateTrackingReporter<'a, Reporter> {
    reporter: &'a mut Reporter,
    errored: bool,
}

impl<'a, Reporter> ErrorReporter for StateTrackingReporter<'a, Reporter>
where
    Reporter: ErrorReporter,
{
    fn report(&mut self, pos: Pos, message: &str) {
        self.errored = true;
        self.reporter.report(pos, message);
    }
}

pub fn parse<'src, Reporter>(
    reporter: &mut Reporter,
    mut scanner: Scanner<'src>,
) -> Result<Program, Error>
where
    Reporter: ErrorReporter,
{
    let mut reporter = StateTrackingReporter {
        reporter,
        errored: false,
    };
    if let Ok(program) = program(&mut reporter, &mut scanner) {
        expect_eof(&mut reporter, &mut scanner);
        if reporter.errored {
            Err(Error {})
        } else {
            Ok(program)
        }
    } else {
        Err(Error {})
    }
}

fn expect_eof<'src, Reporter>(reporter: &mut Reporter, scanner: &mut Scanner<'src>)
where
    Reporter: ErrorReporter,
{
    match scanner.next() {
        // This is the success case so do nothing
        Ok(Token {
            data: TokenType::Eof,
            pos: _,
        }) => {}
        Ok(Token { data: _, pos }) => {
            reporter.report(pos, "expected eof");
        }
        Err(err) => {
            reporter.report(err.pos, "expected eof");
        }
    }
}

fn program<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Program, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let mut stmts = Vec::<Stmt>::new();
    while !scanner.is_at_eof() {
        match declaration(reporter, scanner) {
            Ok(stmt) => stmts.push(stmt),
            Err(_) => synchronize(scanner),
        }
    }
    Ok(Program(stmts))
}

fn synchronize(scanner: &mut Scanner) {
    // Consume tokens until we have consumed a ';'
    // Avoid consuming EOF since we can abort there
    loop {
        let next = scanner.peek();
        match next {
            Ok(token) if token.data == Symbol::Semicolon => {
                _ = scanner.next();
                break;
            }
            Ok(token) if token.data == TokenType::Eof => {
                // Leave the EOF inplace
                break;
            }
            _ => {
                // Consume the token we saw
                let _ = scanner.next();
            }
        }
    }
}

fn declaration<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if scanner.next_if(|data| *data == Keyword::Var).is_some() {
        finish_var_decl(reporter, scanner)
    } else if scanner.next_if(|data| *data == Keyword::Fun).is_some() {
        finish_fun_decl(reporter, scanner)
    } else if scanner.next_if(|data| *data == Keyword::Class).is_some() {
        finish_class_decl(reporter, scanner)
    } else {
        statement(reporter, scanner)
    }
}

fn finish_var_decl<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let identifier = {
        match scanner.next() {
            Ok(Token {
                data: TokenType::Identifier(identifier),
                pos: _,
            }) => identifier.to_string(), // Copy into the AST arena
            Ok(token) => {
                reporter.report(token.pos, "expected an identifier");
                return Err(ParsePanic {});
            }
            Err(err) => {
                reporter.report(err.pos, "expected an identifier");
                return Err(ParsePanic {});
            }
        }
    };
    let initializer = if scanner.next_if(|next| *next == Symbol::Equal).is_some() {
        Some(expr(reporter, scanner)?)
    } else {
        // Generate a synthetic initializer as the constant null
        None
    };
    if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
        reporter.report(pos, "expected ';' after an expression");
        return Err(ParsePanic {});
    }
    Ok(Stmt::VarDecl {
        name: identifier,
        init: initializer,
    })
}

fn finish_fun_decl<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let name = expect_identifier(reporter, scanner)?.to_string();
    if let Err(pos) = expect_next_symbol(scanner, Symbol::LeftParen) {
        reporter.report(pos, "expected '(' after function name");
        return Err(ParsePanic {});
    }

    let mut parameters = Vec::new();
    if scanner
        .next_if(|next| *next == Symbol::RightParen)
        .is_none()
    {
        comma_separated_identifiers(&mut parameters, reporter, scanner)?;
        if let Err(pos) = expect_next_symbol(scanner, Symbol::RightParen) {
            reporter.report(pos, "expect ')' after argument list");
            return Err(ParsePanic {});
        }
    }
    if let Err(pos) = expect_next_symbol(scanner, Symbol::LeftBrace) {
        reporter.report(pos, "function bodies start with '{'");
        return Err(ParsePanic {});
    }
    let body = Box::new(finish_block(reporter, scanner)?);
    Ok(Stmt::FunDecl(FunDecl {
        name,
        parameters,
        body,
    }))
}

fn finish_class_decl<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let name = expect_identifier(reporter, scanner)?;
    if let Err(pos) = expect_next_symbol(scanner, Symbol::LeftBrace) {
        reporter.report(pos, "class bodies start with '{'");
        return Err(ParsePanic {});
    }
    let mut methods = Vec::new();
    // Class methods don't have fun prefix
    while scanner
        .next_if(|next| *next == Symbol::RightBrace)
        .is_none()
    {
        methods.push(match finish_fun_decl(reporter, scanner)? {
            Stmt::FunDecl(decl) => decl,
            _ => unreachable!("finish_fun_decl didn't return a FunDecl"),
        });
    }
    Ok(Stmt::ClassDecl {
        name: name.to_string(),
        body: ClassBody { methods },
    })
}

fn statement<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if scanner.next_if(|next| *next == Keyword::If).is_some() {
        if_stmt(reporter, scanner)
    } else if scanner.next_if(|next| *next == Keyword::While).is_some() {
        while_stmt(reporter, scanner)
    } else if scanner.next_if(|next| *next == Keyword::For).is_some() {
        for_stmt(reporter, scanner)
    } else if scanner.next_if(|next| *next == Keyword::Print).is_some() {
        print_stmt(reporter, scanner)
    } else if scanner.next_if(|next| *next == Keyword::Return).is_some() {
        let expr = if scanner.next_if(|next| *next == Symbol::Semicolon).is_some() {
            None
        } else {
            let e = expr(reporter, scanner)?;
            if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
                reporter.report(pos, "expected ';' after statement");
                return Err(ParsePanic {});
            }
            Some(e)
        };
        Ok(Stmt::Return(expr))
    } else if scanner.next_if(|next| *next == Keyword::Break).is_some() {
        if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
            reporter.report(pos, "expected ';' after break");
            return Err(ParsePanic {});
        }
        Ok(Stmt::Break)
    } else if scanner.next_if(|next| *next == Symbol::LeftBrace).is_some() {
        finish_block(reporter, scanner)
    } else {
        expr_stmt(reporter, scanner)
    }
}

fn finish_block<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let mut stmts: Vec<Stmt> = Vec::new();
    while !scanner.is_at_eof() && !peek_matches(scanner, Symbol::RightBrace) {
        let stmt = declaration(reporter, scanner)?;
        stmts.push(stmt);
    }
    if let Err(pos) = expect_next_symbol(scanner, Symbol::RightBrace) {
        reporter.report(pos, "Expected '}' after block");
        return Err(ParsePanic {});
    }
    Ok(Stmt::Block(stmts))
}

fn if_stmt<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if let Err(pos) = expect_next_symbol(scanner, Symbol::LeftParen) {
        reporter.report(pos, "expected '(' after if");
        return Err(ParsePanic {});
    }
    let test_expr = expr(reporter, scanner)?;
    if let Err(pos) = expect_next_symbol(scanner, Symbol::RightParen) {
        reporter.report(pos, "expected ')' after if condition");
        return Err(ParsePanic {});
    }
    let then_branch = Box::new(statement(reporter, scanner)?);
    let else_branch = if scanner.next_if(|next| *next == Keyword::Else).is_some() {
        Some(Box::new(statement(reporter, scanner)?))
    } else {
        None
    };
    Ok(Stmt::If {
        expr: test_expr,
        then: then_branch,
        or_else: else_branch,
    })
}

fn while_stmt<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if let Err(pos) = expect_next_symbol(scanner, Symbol::LeftParen) {
        reporter.report(pos, "expected '(' after when");
        return Err(ParsePanic {});
    }
    let expr = expr(reporter, scanner)?;
    if let Err(pos) = expect_next_symbol(scanner, Symbol::RightParen) {
        reporter.report(pos, "expected ')' after when condition");
        return Err(ParsePanic {});
    }
    let body = Box::new(statement(reporter, scanner)?);
    Ok(Stmt::Loop { expr, body })
}

fn for_stmt<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if let Err(pos) = expect_next_symbol(scanner, Symbol::LeftParen) {
        reporter.report(pos, "expected '(' after for");
        return Err(ParsePanic {});
    }
    let initializer = if scanner.next_if(|next| *next == Symbol::Semicolon).is_some() {
        None
    } else if scanner
        .clone()
        .next_if(|next| *next == Keyword::Var)
        .is_some()
    {
        Some(declaration(reporter, scanner)?)
    } else {
        Some(expr_stmt(reporter, scanner)?)
    };

    let condition = if scanner.next_if(|next| *next == Symbol::Semicolon).is_some() {
        Expr::Literal(Literal::Boolean(true))
    } else {
        let cond = expr(reporter, scanner)?;
        if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
            reporter.report(pos, "expected ';' after loop condition");
            return Err(ParsePanic {});
        }
        cond
    };

    let incr = if scanner
        .next_if(|next| *next == Symbol::RightParen)
        .is_some()
    {
        None
    } else {
        let expr = expr(reporter, scanner)?;
        if let Err(pos) = expect_next_symbol(scanner, Symbol::RightParen) {
            reporter.report(pos, "expected )' after for clauses");
            return Err(ParsePanic {});
        }
        Some(Stmt::Expr(expr))
    };

    let mut body = statement(reporter, scanner)?;
    // TODO: Avoid double nesting the blocks
    if let Some(incr) = incr {
        body = Stmt::Block(vec![body, incr]);
    }

    let for_loop = Stmt::Loop {
        expr: condition,
        body: Box::new(body),
    };

    if let Some(init) = initializer {
        Ok(Stmt::Block(vec![init, for_loop]))
    } else {
        Ok(for_loop)
    }
}

fn print_stmt<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let expr = expr(reporter, scanner)?;
    if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
        reporter.report(pos, "expected ';' after an expression");
        return Err(ParsePanic {});
    }
    Ok(Stmt::Print(expr))
}

fn expr_stmt<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Stmt, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let expr = expr(reporter, scanner)?;
    if let Err(pos) = expect_next_symbol(scanner, Symbol::Semicolon) {
        reporter.report(pos, "expected ';' after an expression");
        return Err(ParsePanic {});
    }
    Ok(Stmt::Expr(expr))
}

fn expr<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    assignment(reporter, scanner)
}

fn assignment<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let expr = logical_or(reporter, scanner)?;
    if let Some(eq) = scanner.next_if(|token| *token == Symbol::Equal) {
        let rhs = Box::new(logical_or(reporter, scanner)?);
        match expr {
            // A valid assignment target
            Expr::Identifier {
                name,
                scope_distance: _,
            } => Ok(Expr::Assignment {
                target: name,
                scope_distance: None,
                expr: rhs,
            }),
            Expr::Get { object, property } => Ok(Expr::Set {
                object: object,
                property: property,
                value: rhs,
            }),
            // Not a valid assignment target
            // Report the error to trigger top level error, but don't error out here so we continue parsing
            _ => {
                reporter.report(eq.pos, "Invalid assignment lhs");
                Ok(expr)
            }
        }
    } else {
        Ok(expr)
    }
}
// This encapsualtes the logic of the recursive parsing of levels of binary expression operators
// We define a set of matching symbols (and we have the symbol -> binary op) as well as a high precendence parser
// Observe
const EQUALITY_SYMBOLS: [Symbol; 2] = [Symbol::EqualEqual, Symbol::BangEqual];

const COMPARISON_SYMBOLS: [Symbol; 4] = [
    Symbol::Greater,
    Symbol::GreaterEqual,
    Symbol::Less,
    Symbol::LessEqual,
];

const TERM_SYMBOLS: [Symbol; 2] = [Symbol::Minus, Symbol::Plus];

const FACTOR_SYMBOLS: [Symbol; 2] = [Symbol::Star, Symbol::Slash];

// All binary symbols, This is used for error production in primary to recover when we see a binary symbol without a
// left hand operand
const BINARY_SYMBOLS: [Symbol; 10] = [
    Symbol::EqualEqual,
    Symbol::BangEqual,
    Symbol::Greater,
    Symbol::GreaterEqual,
    Symbol::Less,
    Symbol::LessEqual,
    Symbol::Minus,
    Symbol::Plus,
    Symbol::Star,
    Symbol::Slash,
];

fn logical_or<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_logical_op(reporter, scanner, Keyword::Or, logical_and)
}

fn logical_and<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_logical_op(reporter, scanner, Keyword::And, equality)
}

fn equality<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(reporter, scanner, &EQUALITY_SYMBOLS, ternary)
}

fn ternary<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let expr = comparison(reporter, scanner)?;
    if scanner.next_if(|next| *next == Symbol::Question).is_none() {
        Ok(expr)
    } else {
        let if_true = Box::new(comparison(reporter, scanner)?);
        if let Err(pos) = expect_next_symbol(scanner, Symbol::Colon) {
            reporter.report(pos, "expected a ':' in ternary");
            return Err(ParsePanic {});
        }
        let if_false = Box::new(comparison(reporter, scanner)?);
        Ok(Expr::Ternary {
            test: Box::new(expr),
            if_true,
            if_false,
        })
    }
}

fn comparison<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(reporter, scanner, &COMPARISON_SYMBOLS, term)
}

fn term<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(reporter, scanner, &TERM_SYMBOLS, factor)
}

fn factor<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    left_recursive_binary_op(reporter, scanner, &FACTOR_SYMBOLS, unary)
}

const UNARY_SYMBOLS: [Symbol; 2] = [Symbol::Minus, Symbol::Bang];

fn unary<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    if let Some(symbol) = scanner.next_if_some(|next| match next {
        TokenType::Symbol(symbol) if UNARY_SYMBOLS.contains(&symbol) => Some(symbol),
        _ => None,
    }) {
        let operator = symbol_to_unary_op(symbol);
        let right = Box::new(unary(reporter, scanner)?);
        Ok(Expr::Unary {
            op: operator,
            expr: right,
        })
    } else {
        call(reporter, scanner)
    }
}

fn call<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let mut expr = primary(reporter, scanner)?;
    loop {
        if scanner.next_if(|next| *next == Symbol::LeftParen).is_some() {
            expr = finish_call(reporter, scanner, expr)?;
        } else if scanner.next_if(|next| *next == Symbol::Dot).is_some() {
            let name = expect_identifier(reporter, scanner)?;
            expr = Expr::Get {
                object: Box::new(expr),
                property: name.to_string(),
            };
        } else {
            break;
        }
    }
    Ok(expr)
}

fn finish_call<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
    callee: Expr,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    let mut args = Vec::new();
    if scanner
        .next_if(|next| *next == Symbol::RightParen)
        .is_none()
    {
        loop {
            if args.len() >= 255 {
                reporter.report(scanner.peek_pos(), "Too many function arguments");
            } else {
                let arg = expr(reporter, scanner)?;
                args.push(arg);
            }
            if !scanner.next_if(|next| *next == Symbol::Comma).is_some() {
                break;
            }
        }
        // Note: we only need to consume the trailing ) if we didn't consume it in the has args branch
        if let Err(pos) = expect_next_symbol(scanner, Symbol::RightParen) {
            reporter.report(pos, "expect ')' after arguments");
            return Err(ParsePanic {});
        }
    }
    Ok(Expr::Call {
        callee: Box::new(callee),
        arguments: args,
    })
}

fn primary<'src, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
{
    match scanner.next() {
        Ok(token) => {
            let expr = match token.data {
                TokenType::Keyword(Keyword::True) => Expr::Literal(Literal::Boolean(true)),
                TokenType::Keyword(Keyword::False) => Expr::Literal(Literal::Boolean(false)),
                TokenType::Keyword(Keyword::Nil) => Expr::Literal(Literal::Nil),
                TokenType::String(string) => Expr::Literal(Literal::String(string.to_string())),
                TokenType::Number(number) => Expr::Literal(Literal::Number(OrderedFloat(number))),
                TokenType::Symbol(Symbol::LeftParen) => {
                    let inner = expr(reporter, scanner)?;
                    match scanner.next() {
                        Ok(token) => {
                            match token.data {
                                TokenType::Symbol(Symbol::RightParen) => {
                                    // This is the happy path in that we have successfully matched the trailing group
                                    Expr::Group(Box::new(inner))
                                }
                                _ => {
                                    reporter.report(token.pos, "expected a ')'");
                                    return Err(ParsePanic {});
                                }
                            }
                        }
                        Err(scan_err) => {
                            reporter.report(scan_err.pos, scan_err.error.message());
                            return Err(ParsePanic {});
                        }
                    }
                }
                TokenType::Identifier(ident) => Expr::Identifier {
                    name: ident.to_string(),
                    scope_distance: None,
                },
                // An unexpected binary symbol so lets try and parse the rhs before raising the error
                // - should be trapped by unary
                TokenType::Symbol(symbol)
                    if BINARY_SYMBOLS.iter().find(|bin| **bin == symbol).is_some() =>
                {
                    // Should this report something different?
                    reporter.report(token.pos, "binary operator without a left-hand side");
                    // result is unimportant, we are bailing anyway
                    let _rhs = expr(reporter, scanner);
                    return Err(ParsePanic {});
                }
                _ => {
                    reporter.report(
                        token.pos,
                        "unexpected token: expected true, false, nil, number, string or (",
                    );
                    return Err(ParsePanic {});
                }
            };
            Ok(expr)
        }
        Err(scan_err) => {
            reporter.report(scan_err.pos, scan_err.error.message());
            Err(ParsePanic {})
        }
    }
}

// It occurs to me it might be possible to do this a single recursive call that unfolds generically
// instead of encoding the recursion in separate helpers
fn left_recursive_binary_op<'src, Reporter, F>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
    symbols: &[Symbol],
    higher_precedence: F,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
    F: Fn(&mut Reporter, &mut Scanner<'src>) -> Result<Expr, ParsePanic>,
{
    let mut expr = higher_precedence(reporter, scanner)?;
    while let Some(symbol) = scanner.next_if_some(|next| match next {
        TokenType::Symbol(s) if symbols.contains(&s) => Some(s),
        _ => None,
    }) {
        let binary_op = symbol_to_binary_op(symbol);
        let right = Box::new(higher_precedence(reporter, scanner)?);
        expr = Expr::Binary {
            left: Box::new(expr),
            op: binary_op,
            right,
        }
    }
    Ok(expr)
}

fn left_recursive_logical_op<'src, Reporter, F>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
    keyword: Keyword,
    higher_precedence: F,
) -> Result<Expr, ParsePanic>
where
    Reporter: ErrorReporter,
    F: Fn(&mut Reporter, &mut Scanner<'src>) -> Result<Expr, ParsePanic>,
{
    let mut expr = higher_precedence(reporter, scanner)?;
    while let Some(kw) = scanner.next_if_some(|next| match next {
        TokenType::Keyword(kw) if keyword == kw => Some(kw),
        _ => None,
    }) {
        let logical_op = keyword_to_logical_op(kw);
        let right = Box::new(higher_precedence(reporter, scanner)?);
        expr = Expr::Logical {
            left: Box::new(expr),
            op: logical_op,
            right,
        }
    }
    Ok(expr)
}

fn symbol_to_binary_op(symbol: Symbol) -> BinaryOp {
    match symbol {
        Symbol::EqualEqual => BinaryOp::Equal,
        Symbol::BangEqual => BinaryOp::NotEqual,
        Symbol::Less => BinaryOp::LessThan,
        Symbol::LessEqual => BinaryOp::LessThanEqual,
        Symbol::Greater => BinaryOp::GreaterThan,
        Symbol::GreaterEqual => BinaryOp::GreaterThanEqual,
        Symbol::Plus => BinaryOp::Add,
        Symbol::Minus => BinaryOp::Subtract,
        Symbol::Star => BinaryOp::Multiply,
        Symbol::Slash => BinaryOp::Divide,
        s => panic!("symbol was not a valid binary operator: {}", s),
    }
}

fn keyword_to_logical_op(kw: Keyword) -> LogicalOp {
    match kw {
        Keyword::And => LogicalOp::And,
        Keyword::Or => LogicalOp::Or,
        kw => panic!("keyword was not a valid logical operator: {}", kw),
    }
}

fn symbol_to_unary_op(symbol: Symbol) -> UnaryOp {
    match symbol {
        Symbol::Bang => UnaryOp::Not,
        Symbol::Minus => UnaryOp::Negative,
        s => panic!("symbol was not a valid unary operator: {}", s),
    }
}

/// Expect that the next token from scanner is the given symbol
/// Returns the pos of the failed token (either due to error or mismatch) in Err
fn expect_next_symbol(scanner: &mut Scanner, symbol: Symbol) -> Result<(), Pos> {
    let next = scanner.next();
    match next {
        Ok(token) if token.data == symbol => Ok(()),
        Ok(token) => Err(token.pos),
        Err(err) => Err(err.pos),
    }
}

fn expect_identifier<'code, Reporter>(
    reporter: &mut Reporter,
    scanner: &mut Scanner<'code>,
) -> Result<&'code str, ParsePanic>
where
    Reporter: ErrorReporter,
{
    match scanner.next() {
        Ok(Token {
            data: TokenType::Identifier(ident),
            pos: _,
        }) => Ok(ident),
        Ok(Token { data: _, pos }) => {
            reporter.report(pos, "expected identifier");
            return Err(ParsePanic {});
        }
        Err(error) => {
            reporter.report(error.pos, "expected identifier");
            return Err(ParsePanic {});
        }
    }
}

// Helper to determine if a scanner result matches a specific input
fn peek_matches<'code, A>(scanner: &mut Scanner<'code>, rhs: A) -> bool
where
    TokenType<'code>: PartialEq<A>,
{
    match scanner.peek() {
        Ok(token) => token.data == rhs,
        _ => false,
    }
}

fn comma_separated_identifiers<'src, Reporter>(
    idents: &mut Vec<String>,
    reporter: &mut Reporter,
    scanner: &mut Scanner<'src>,
) -> Result<(), ParsePanic>
where
    Reporter: ErrorReporter,
{
    idents.push(expect_identifier(reporter, scanner)?.to_string());
    while scanner.next_if(|next| *next == Symbol::Comma).is_some() {
        idents.push(expect_identifier(reporter, scanner)?.to_string());
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use std::io::stderr;

    use super::*;

    #[test]
    fn test_pretty_print() {
        // (* (- 123) (group 45.67))
        let expr = Expr::Binary {
            left: Box::new(Expr::Unary {
                op: UnaryOp::Negative,
                expr: Box::new(Expr::Literal(Literal::Number(OrderedFloat(123f64)))),
            }),
            op: BinaryOp::Multiply,
            right: Box::new(Expr::Group(Box::new(Expr::Literal(Literal::Number(
                OrderedFloat(45.67f64),
            ))))),
        };

        let mut result = String::new();
        std::fmt::write(&mut result, format_args!("{}", expr)).unwrap();
        assert_eq!("(* (- 123) (group 45.67))", result);
    }

    #[test]
    fn test_parse_call() {
        _ = parse(&mut TestErrorReporter {}, Scanner::new("print clock();")).unwrap();
    }

    #[test]
    fn test_parse_call_args() {
        let program = parse(
            &mut TestErrorReporter {},
            Scanner::new("print print_num(\"12.3\");"),
        );
        program.unwrap();
    }

    #[test]
    fn test_fun_define() {
        let code = "fun add(a, b) {
            print a + b;
        }

        add(1, 2);
        ";
        let mut stderr = stderr().lock();
        let mut error = WriteErrorReporter::new(&mut stderr);
        let program = parse(&mut error, Scanner::new(code));
        program.unwrap();
    }
}
