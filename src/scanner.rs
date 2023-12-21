use std::fmt::{self, Display, Formatter};
use std::iter::Peekable;
use std::str::CharIndices;
use thiserror::Error;

#[derive(Debug, PartialEq, Eq)]
pub struct Pos {
    offset_in_line: usize,
    line: usize,
}

impl Display for Pos {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.offset_in_line)
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
pub struct Token<'code> {
    data: Data<'code>,
    pos: Pos,
}

#[derive(Debug, PartialEq)]
pub enum Data<'code> {
    Symbol { symbol: Symbol },
    Keyword { keyword: Keyword },
    Identifier { identifier: &'code str },
    String { string: &'code str },
    Number { number: f64 },
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

const KEYWORD_LITERAL_TO_SYMBOL: [(&'static str, Keyword); 16] = [
    ("and", Keyword::And),
    ("class", Keyword::Class),
    ("else", Keyword::Else),
    ("false", Keyword::False),
    ("fun", Keyword::Fun),
    ("for", Keyword::For),
    ("if", Keyword::If),
    ("nil", Keyword::Nil),
    ("or", Keyword::Or),
    ("print", Keyword::Print),
    ("return", Keyword::Return),
    ("super", Keyword::Super),
    ("this", Keyword::This),
    ("true", Keyword::True),
    ("var", Keyword::Var),
    ("while", Keyword::While),
];

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

    // Duplicate the current scanner so that we
    pub fn duplicate(&self) -> Scanner<'lex> {
        Scanner {
            code: self.code,
            code_iter: self.code_iter.clone(),
            line: self.line,
            offset_in_line: self.offset_in_line,
        }
    }

    fn current_pos(&self) -> Pos {
        Pos {
            line: self.line,
            offset_in_line: self.offset_in_line,
        }
    }

    fn consume_next_char_if_eq(&mut self, next_ch: char) -> bool {
        self.code_iter.next_if(|(_, ch)| *ch == next_ch).is_some()
    }

    fn consume_next_char_if_neq(&mut self, not_next_ch: char) -> bool {
        self.code_iter
            .next_if(|(_, ch)| *ch != not_next_ch)
            .is_some()
    }

    fn consume_next_char_if_match<F>(&mut self, predicate: F) -> bool
    where
        F: FnOnce(char) -> bool,
    {
        self.code_iter.next_if(|(_, ch)| predicate(*ch)).is_some()
    }

    fn consume_next_char_if_ws(&mut self) -> bool {
        self.code_iter
            .next_if(|(_, ch)| WS_CHARS.contains(*ch))
            .is_some()
    }

    fn gobble_whitespace(&mut self) {
        loop {
            if self.consume_next_char_if_ws() {
                self.offset_in_line += 1;
            } else if self.consume_next_char_if_eq('\n') {
                self.offset_in_line = 0;
                self.line += 1;
            } else {
                break;
            }
        }
    }

    // Slice the code slice to a length and and offset
    // This requires that offset point to the start of a code point (such as produced by code_iter)
    unsafe fn code_subslice(&self, offset: usize, len: usize) -> &'lex str {
        // TODO: We do this in 2 parts, we are able to jump to the start of the of the code slice directly
        // For now, however, there isn't a great mechanism for immediately finding the end
        // The consume_next_char* friends don't return the ending offset
        // We accept that hopefully most literal strings will be smallish
        let initial_skip = std::str::from_utf8_unchecked(&self.code.as_bytes()[offset..]);
        &initial_skip[0..len]
    }
}

const WS_CHARS: &'static str = " \r\t";

impl<'lex> Iterator for Scanner<'lex> {
    type Item = Result<Token<'lex>, ScanError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((offset, ch)) = self.code_iter.next() {
            let pos = self.current_pos();
            match ch {
                '(' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::LeftParen,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                ')' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::RightParen,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '{' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::LeftBrace,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '}' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::RightBrace,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                ',' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::Comma,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '.' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::Dot,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '-' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::Minus,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '+' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::Plus,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                ';' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::Semicolon,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '*' => {
                    let token = Token {
                        data: Data::Symbol {
                            symbol: Symbol::Star,
                        },
                        pos,
                    };
                    self.offset_in_line += 1;
                    Some(Ok(token))
                }
                '!' => {
                    let symbol = if self.consume_next_char_if_eq('=') {
                        self.offset_in_line += 2;
                        Symbol::BangEqual
                    } else {
                        self.offset_in_line += 1;
                        Symbol::Bang
                    };
                    Some(Ok(Token {
                        data: Data::Symbol { symbol },
                        pos,
                    }))
                }
                '=' => {
                    let symbol = if self.consume_next_char_if_eq('=') {
                        self.offset_in_line += 2;
                        Symbol::EqualEqual
                    } else {
                        self.offset_in_line += 1;
                        Symbol::Equal
                    };
                    Some(Ok(Token {
                        data: Data::Symbol { symbol },
                        pos,
                    }))
                }
                '<' => {
                    let symbol = if self.consume_next_char_if_eq('=') {
                        self.offset_in_line += 2;
                        Symbol::LessEqual
                    } else {
                        self.offset_in_line += 1;
                        Symbol::Less
                    };
                    Some(Ok(Token {
                        data: Data::Symbol { symbol },
                        pos,
                    }))
                }
                '>' => {
                    let symbol = if self.consume_next_char_if_eq('=') {
                        self.offset_in_line += 2;
                        Symbol::GreaterEqual
                    } else {
                        self.offset_in_line += 1;
                        Symbol::Greater
                    };
                    Some(Ok(Token {
                        data: Data::Symbol { symbol },
                        pos,
                    }))
                }
                '/' => {
                    if self.consume_next_char_if_eq('/') {
                        // Gobble the comment and then recursively call
                        let mut comment_len = 2;
                        while self.consume_next_char_if_neq('\n') {
                            comment_len += 1;
                        }
                        self.offset_in_line += comment_len;
                        // We don't consume the newline so there is no need to increment line here
                        // This assumes that the recursive call will start by gobbling the newline
                        self.next()
                    } else {
                        self.offset_in_line += 1;
                        Some(Ok(Token {
                            data: Data::Symbol {
                                symbol: Symbol::Slash,
                            },
                            pos,
                        }))
                    }
                }
                // Both of these have almost the same behavior. We gobble all the whitespace we can to avoid increasing
                // recursion depth in the case of many lines that have only whitespace characters
                ' ' | '\r' | '\t' => {
                    self.offset_in_line += 1;
                    self.gobble_whitespace();
                    self.next()
                }
                '\n' => {
                    self.offset_in_line = 0;
                    self.line += 1;
                    self.gobble_whitespace();
                    self.next()
                }
                '0'..='9' => {
                    let mut num_len = 1;
                    while self.consume_next_char_if_match(|ch| ch.is_digit(10)) {
                        num_len += 1;
                    }
                    if self.consume_next_char_if_eq('.')
                        && self.consume_next_char_if_match(|ch| ch.is_digit(10))
                    {
                        num_len += 2;
                        while self.consume_next_char_if_match(|ch| ch.is_digit(10)) {
                            num_len += 1;
                        }
                    }
                    self.offset_in_line += num_len;
                    // SAFETY: offset is generated as a valid utf-8 offset per CharIndices
                    let num_slice = unsafe { self.code_subslice(offset, num_len) };
                    let number = num_slice.parse::<f64>().unwrap();
                    let token = Token {
                        data: Data::Number { number },
                        pos,
                    };
                    Some(Ok(token))
                }
                '"' => {
                    // TODO: Handle escaping
                    let mut str_len = 0;
                    // Strings are multiline, so we need to track things like whether or not we cross a newline
                    let mut terminated = false;
                    while let Some((_, ch)) = self.code_iter.next() {
                        match ch {
                            '\n' => {
                                str_len += 1;
                                self.offset_in_line = 0;
                                self.line += 1;
                            }
                            '"' => {
                                self.offset_in_line += 1;
                                terminated = true;
                                break;
                            }
                            _ => {
                                str_len += 1;
                                self.offset_in_line += 1;
                            }
                        }
                    }
                    if !terminated {
                        Some(Err(ScanError::UnterminatedString(pos)))
                    } else {
                        // We slice str_len -1 since we want to snip the trailing quote
                        let string = unsafe {
                            // SAFETY: offset is generated as a valid utf-8 offset per CharIndices
                            // We skip over the leading quote but this is definitely only 1 byte
                            self.code_subslice(offset + 1, str_len)
                        };
                        Some(Ok(Token {
                            data: Data::String { string },
                            pos,
                        }))
                    }
                }
                c if c.is_alphabetic() => {
                    let mut num_len = 1;
                    while self.consume_next_char_if_match(|ch| ch.is_alphanumeric()) {
                        num_len += 1;
                    }
                    self.offset_in_line += num_len;
                    // SAFETY: offset is generated as a valid utf-8 offset per CharIndices
                    let identifier = unsafe { self.code_subslice(offset, num_len) };
                    let token = if let Some((_, kw)) = KEYWORD_LITERAL_TO_SYMBOL
                        .iter()
                        .find(|(lit, _)| *lit == identifier)
                    {
                        Token {
                            data: Data::Keyword { keyword: *kw },
                            pos,
                        }
                    } else {
                        Token {
                            data: Data::Identifier { identifier },
                            pos,
                        }
                    };
                    Some(Ok(token))
                }
                _ => {
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
        let mut scanner = Scanner::new(&code);
        let first_token = scanner.next().unwrap().unwrap();
        match first_token.data {
            Data::Keyword { keyword } => {
                assert_eq!(Keyword::Var, keyword);
                assert_eq!(
                    Pos {
                        offset_in_line: 0,
                        line: 0
                    },
                    first_token.pos
                );
            }
            _ => unreachable!(),
        };
    }

    #[test]
    fn scan_basic_sequence() {
        let code = "var marco = \"9001\"";
        let mut scanner = Scanner::new(&code);
        let token = scanner.next().unwrap().unwrap();
        match token.data {
            Data::Keyword { keyword } => {
                assert_eq!(Keyword::Var, keyword);
                assert_eq!(
                    Pos {
                        offset_in_line: 0,
                        line: 0
                    },
                    token.pos
                );
            }
            _ => unreachable!(),
        }

        let token = scanner.next().unwrap().unwrap();
        match token.data {
            Data::Identifier { identifier } => {
                assert_eq!("marco", identifier);
                assert_eq!(
                    Pos {
                        offset_in_line: 4,
                        line: 0
                    },
                    token.pos
                );
            }
            _ => unreachable!(),
        }

        let token = scanner.next().unwrap().unwrap();
        match token.data {
            Data::Symbol { symbol } => {
                assert_eq!(Symbol::Equal, symbol);
                assert_eq!(
                    Pos {
                        offset_in_line: 10,
                        line: 0
                    },
                    token.pos
                );
            }
            _ => unreachable!(),
        }

        let token = scanner.next().unwrap().unwrap();
        match token.data {
            Data::String { string } => {
                assert_eq!("9001", string);
                assert_eq!(
                    Pos {
                        offset_in_line: 12,
                        line: 0
                    },
                    token.pos
                );
            }
            _ => unreachable!(),
        }

        assert!(scanner.next().is_none());
    }

    #[test]
    fn test_multi_line_string_pos() {
        let code = r#"
"marco
bomp";
"#;
        let mut scanner = Scanner::new(&code);
        // Did we get a string?
        let token = scanner.next().unwrap().unwrap();
        match token.data {
            Data::String { string } => {
                assert_eq!("marco\nbomp", string);
                assert_eq!(1, token.pos.line);
            }
            _ => unreachable!(),
        }
        // Did we correctly update the lines etc
        let token = scanner.next().unwrap().unwrap();
        match token.data {
            Data::Symbol { symbol } => {
                assert_eq!(Symbol::Semicolon, symbol);
                assert_eq!(
                    Pos {
                        line: 2,
                        offset_in_line: 5
                    },
                    token.pos
                );
            }
            _ => unreachable!(),
        }
    }
}
