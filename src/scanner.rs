use std::fmt::{self, Display, Formatter};
use std::iter::Peekable;
use std::str::CharIndices;
use thiserror::Error;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Pos {
    pub offset_in_line: usize,
    pub line: usize,
}

impl Display for Pos {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.offset_in_line)
    }
}

#[derive(Clone, Error, Debug, PartialEq, Eq)]
#[error("scan error: {error:?} {pos}")]
pub struct ScanError {
    error: ScanErrorType,
    pos: Pos,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScanErrorType {
    UnterminatedString,
    UnrecognizedToken,
}

/// A token in the input stream
/// Contains a data which is the symbol variant and a position
/// Note that pos is always defined, but in the case of EOF will describe a location
/// Potentially off the end of the input stream
#[derive(Debug, PartialEq, Clone)]
pub struct Token<'code> {
    pub data: Data<'code>,
    pub pos: Pos,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Data<'code> {
    Symbol { symbol: Symbol },
    Keyword { keyword: Keyword },
    Identifier { identifier: &'code str },
    String { string: &'code str },
    Number { number: f64 },
    Eof,
}

/// Describe the type of a data without reference to the underlying data
/// This is useful for referring to an expeted token rather than input data
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DataType {
    Symbol(Symbol),
    Keyword(Keyword),
    Identifier,
    String,
    Number,
}

impl Display for DataType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Symbol(sym) => sym.fmt(f),
            Self::Keyword(kw) => kw.fmt(f),
            Self::Identifier => f.write_str("identifier"),
            Self::String => f.write_str("string"),
            Self::Number => f.write_str("number"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

#[derive(Clone)]
pub struct Scanner<'lex> {
    code: &'lex str,
    code_iter: Peekable<CharIndices<'lex>>,
    emitted_eof: bool, // Have we sent the EOF yet

    line: usize,
    offset_in_line: usize,
}

impl<'lex> Scanner<'lex> {
    pub fn new(code: &'lex str) -> Scanner<'lex> {
        Scanner {
            code,
            code_iter: code.char_indices().peekable(),
            emitted_eof: false,
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
        let pos = self.current_pos();
        if let Some((offset, ch)) = self.code_iter.next() {
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
                        Some(Err(ScanError {
                            error: ScanErrorType::UnterminatedString,
                            pos,
                        }))
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
                    Some(Err(ScanError {
                        error: ScanErrorType::UnrecognizedToken,
                        pos,
                    }))
                }
            }
        } else if !self.emitted_eof {
            self.emitted_eof = true;
            Some(Ok(Token {
                data: Data::Eof,
                pos,
            }))
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

        let token = scanner.next().unwrap().unwrap();
        match token.data {
            Data::Eof => {}
            _ => unreachable!(),
        }
        // We have passed the EOF
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

    // Verify we don't get into an infinite loop by error conditions
    #[test]
    fn no_infinite_seq_on_unterminate_string() {
        let code = "\"a string that isn't terminated";
        let mut scanner = Scanner::new(&code);
        let token = scanner.next().unwrap();
        assert_eq!(ScanErrorType::UnterminatedString, token.unwrap_err().error);
        let token = scanner.next().unwrap();
        assert_eq!(Data::Eof, token.unwrap().data);
        assert!(scanner.next().is_none());
    }

    #[test]
    fn no_infinite_seq_on_bad_token() {
        let code = "$var";
        let mut scanner = Scanner::new(&code);
        let token = scanner.next().unwrap();
        assert_eq!(ScanErrorType::UnrecognizedToken, token.unwrap_err().error);
    }
}
