use bumpalo::Bump;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::iter::{Enumerate, Peekable};
use std::str::{CharIndices, Chars};
use thiserror::Error;

#[derive(Debug, PartialEq, Eq)]
pub struct Pos {
    offset_in_line: usize,
    line: usize,
}

impl Display for Pos {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.offset_in_line);
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum ScanError {
    #[error("unterminated string: {0}")]
    UnterminatedString(Pos),
    #[error("unrecognized token: {0}")]
    UnrecognizedToken(Pos),
}

/// A token in the input stream
///
/// References the lifetime of the lifetime of the code

#[derive(Debug, PartialEq)]
pub enum Token<'code> {
    Symbol { symbol: Symbol, pos: Pos },
    Keyword { keyword: Keyword, pos: Pos },
    Identifier { identifier: &'code str, pos: Pos },
    String { string: &'code str, pos: Pos },
    Number { number: f64, pos: Pos },
}

#[derive(Debug, PartialEq, Eq)]
pub enum Symbol {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Keyword {
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}

impl Display for Keyword {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

struct Scanner<'lex> {
    code: &'lex str,
    code_iter: Peekable<CharIndices<'lex>>,

    line: usize,
    offset_in_line: usize,
}

impl<'lex> Scanner<'lex> {
    pub fn new(code: &'lex str) -> Scanner<'lex> {
        Scanner {
            code,
            code_iter: code.char_indices().peekable(),
            line: 0,
            offset_in_line: 0,
        }
    }

    fn current_pos(&self) -> Pos {
        Pos {
            line: self.line,
            offset_in_line: self.offset_in_line,
        }
    }
}

impl<'lex> Iterator for Scanner<'lex> {
    type Item = Result<Token<'lex>, ScanError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((offset, ch)) = self.code_iter.next() {
            match ch {
                '(' => {
                    let token = Token::Symbol {
                        symbol: Symbol::LeftParen,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                ')' => {
                    let token = Token::Symbol {
                        symbol: Symbol::RightParen,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '{' => {
                    let token = Token::Symbol {
                        symbol: Symbol::LeftBrace,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '}' => {
                    let token = Token::Symbol {
                        symbol: Symbol::RightBrace,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                ',' => {
                    let token = Token::Symbol {
                        symbol: Symbol::RightBrace,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '.' => {
                    let token = Token::Symbol {
                        symbol: Symbol::Dot,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '-' => {
                    let token = Token::Symbol {
                        symbol: Symbol::Minus,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '+' => {
                    let token = Token::Symbol {
                        symbol: Symbol::Plus,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                ';' => {
                    let token = Token::Symbol {
                        symbol: Symbol::Semicolon,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '*' => {
                    let token = Token::Symbol {
                        symbol: Symbol::Star,
                        pos: self.current_pos(),
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                _ => {
                    let pos = self.current_pos();
                    self.offset_in_line += 1;
                    Some(Err(ScanError::UnrecognizedToken(pos)))
                }
            }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn scan_anything() {
        let code = "var";
        let mut scanner = Scanner::new(&arena, &code);
        let first_token = scanner.next().unwrap().unwrap();
        assert_eq!(
            Pos {
                offset_in_line: 0,
                line: 0
            },
            first_token.pos
        )
    }
}
