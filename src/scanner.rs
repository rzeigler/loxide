use std::fmt::{self, Display, Formatter};
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
pub struct Error {
    pub error: ErrorType,
    pub pos: Pos,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorType {
    UnterminatedString,
    UnrecognizedToken,
}

// TODO: Delete me
impl ErrorType {
    pub fn message(&self) -> &'static str {
        match self {
            Self::UnterminatedString => "unterminated string",
            Self::UnrecognizedToken => "unrecognized token",
        }
    }
}

/// A token in the input stream
/// Contains a data which is the symbol variant and a position
/// Note that pos is always defined, but in the case of EOF will describe a location
/// Potentially off the end of the input stream
#[derive(Debug, PartialEq, Clone)]
pub struct Token<'code> {
    pub data: TokenType<'code>,
    pub pos: Pos,
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenType<'code> {
    Symbol(Symbol),
    Keyword(Keyword),
    Identifier(&'code str),
    String(&'code str),
    Number(f64),
    Eof,
}

impl<'code> PartialEq<Symbol> for TokenType<'code> {
    fn eq(&self, other: &Symbol) -> bool {
        match self {
            TokenType::Symbol(sym) => *sym == *other,
            _ => false,
        }
    }
}

impl<'code> PartialEq<Keyword> for TokenType<'code> {
    fn eq(&self, other: &Keyword) -> bool {
        match self {
            TokenType::Keyword(key) => *key == *other,
            _ => false,
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
    Question,
    Colon,

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

// TODO: Implementing this as an iterator has proven to be weird. It should probably implement somethign different
// The iterator implementation is a holdover form the first version where we just wanted to print tokens
// Subsequently, the Eof token was added because its always desirable have a position and a synthetic eof can exist for
// Eof
// So, we now have both Eof and None
// It is assumed to be an error to scan past the Eof in lots of places in the parser
// We should implement a custom iterator like protocol to account for this and remove all the unreachable bits
#[derive(Clone)]
pub struct Scanner<'code> {
    // Code, assumed to be valid utf-8, however, we want to iterate byte by byte
    // We mostly don't care about utf-8 and this should allow it to process just fine in strings
    code: &'code [u8],
    // The offset of the nxt character to process
    // When offset == code.len() the next character to emit is an EOF, when offset > code.len() this is a coding error
    offset: usize,

    // Track the state for helpful offsets
    line: usize,
    offset_in_line: usize,
}

impl<'lex> Scanner<'lex> {
    pub fn new(code: &'lex str) -> Scanner<'lex> {
        Scanner {
            code: code.as_bytes(),
            offset: 0,
            line: 0,
            offset_in_line: 0,
        }
    }

    /// Determine if the next token returned would be EOF
    pub fn is_at_eof(&self) -> bool {
        // This can't be just self.offset == self.code.len() because its possible there is trailing whitespace
        // So, instead, peek the next token and check what it is
        if let Ok(Token {
            data: TokenType::Eof,
            pos: _,
        }) = self.clone().next()
        {
            true
        } else {
            false
        }
    }

    /// Consume the next token iff. it matches the given predicate.
    /// If it does not, the next call to next will return it
    /// This function cannot error, it is assumed that a consumer is uninterested in consuming error state
    pub fn next_if<P>(&mut self, predicate: P) -> Option<Token<'lex>>
    where
        P: FnOnce(&TokenType<'lex>) -> bool,
    {
        let before = self.clone();
        if let Ok(token) = self.next() {
            if predicate(&token.data) {
                return Some(token);
            }
        }
        *self = before;
        None
    }

    /// Consume and return the next token if filter_map returns a Some
    /// This is useful to perform conditional peeks where we may want a limited bit of data, etc.
    /// This function cannot error, it is assumed that consumers are unintereste din errors
    ///
    pub fn next_if_some<F, A>(&mut self, filter_map: F) -> Option<A>
    where
        F: FnOnce(TokenType<'lex>) -> Option<A>,
    {
        let before = self.clone();
        if let Ok(token) = self.next() {
            if let Some(result) = filter_map(token.data) {
                return Some(result);
            }
        }
        *self = before;
        None
    }

    pub fn peek(&mut self) -> Result<Token<'lex>, Error> {
        let mut clone = self.clone();
        clone.next()
    }

    pub fn next(&mut self) -> Result<Token<'lex>, Error> {
        // First things first, consume any leading whitespace
        self.gobble_whitespace();
        let pos = self.current_pos();
        if self.offset > self.code.len() {
            panic!("scanned past EOF");
        } else if self.offset == self.code.len() {
            Ok(Token {
                data: TokenType::Eof,
                pos,
            })
        } else {
            let ch = self.code[self.offset];
            // Track the previous offset, some tokens like to have it
            let offset = self.offset;
            self.offset += 1;
            match ch {
                b'(' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::LeftParen),
                        pos,
                    })
                }
                b')' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::RightParen),
                        pos,
                    })
                }
                b'{' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::LeftBrace),
                        pos,
                    })
                }
                b'}' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::RightBrace),
                        pos,
                    })
                }
                b',' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::Comma),
                        pos,
                    })
                }
                b'.' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::Dot),
                        pos,
                    })
                }
                b'-' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::Minus),
                        pos,
                    })
                }
                b'+' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::Plus),
                        pos,
                    })
                }
                b';' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::Semicolon),
                        pos,
                    })
                }
                b'?' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::Question),
                        pos,
                    })
                }
                b':' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::Colon),
                        pos,
                    })
                }
                b'*' => {
                    self.offset_in_line += 1;
                    Ok(Token {
                        data: TokenType::Symbol(Symbol::Star),
                        pos,
                    })
                }
                b'!' => {
                    let symbol = if self.consume_next_char_if_eq(b'=') {
                        self.offset_in_line += 2;
                        Symbol::BangEqual
                    } else {
                        self.offset_in_line += 1;
                        Symbol::Bang
                    };
                    Ok(Token {
                        data: TokenType::Symbol(symbol),
                        pos,
                    })
                }
                b'=' => {
                    let symbol = if self.consume_next_char_if_eq(b'=') {
                        self.offset_in_line += 2;
                        Symbol::EqualEqual
                    } else {
                        self.offset_in_line += 1;
                        Symbol::Equal
                    };
                    Ok(Token {
                        data: TokenType::Symbol(symbol),
                        pos,
                    })
                }
                b'<' => {
                    let symbol = if self.consume_next_char_if_eq(b'=') {
                        self.offset_in_line += 2;
                        Symbol::LessEqual
                    } else {
                        self.offset_in_line += 1;
                        Symbol::Less
                    };
                    Ok(Token {
                        data: TokenType::Symbol(symbol),
                        pos,
                    })
                }
                b'>' => {
                    let symbol = if self.consume_next_char_if_eq(b'=') {
                        self.offset_in_line += 2;
                        Symbol::GreaterEqual
                    } else {
                        self.offset_in_line += 1;
                        Symbol::Greater
                    };
                    Ok(Token {
                        data: TokenType::Symbol(symbol),
                        pos,
                    })
                }
                b'/' => {
                    if self.consume_next_char_if_eq(b'/') {
                        // Gobble the comment and then recursively call
                        let mut comment_len = 2;
                        while self.consume_next_char_if_neq(b'\n') {
                            comment_len += 1;
                        }
                        self.offset_in_line += comment_len;
                        // We don't consume the newline so there is no need to increment line here
                        // This assumes that the recursive call will start by gobbling the newline
                        self.next()
                    } else {
                        self.offset_in_line += 1;
                        Ok(Token {
                            data: TokenType::Symbol(Symbol::Slash),
                            pos,
                        })
                    }
                }
                // Both of these have almost the same behavior. We gobble all the whitespace we can to avoid increasing
                // recursion depth in the case of many lines that have only whitespace characters
                b' ' | b'\r' | b'\t' => {
                    self.offset_in_line += 1;
                    self.gobble_whitespace();
                    self.next()
                }
                b'\n' => {
                    self.offset_in_line = 0;
                    self.line += 1;
                    self.gobble_whitespace();
                    self.next()
                }
                b'0'..=b'9' => {
                    let mut num_len = 1;
                    while self.consume_next_char_if_match(|ch| ch.is_ascii_digit()) {
                        num_len += 1;
                    }
                    if self.consume_next_char_if_eq(b'.')
                        && self.consume_next_char_if_match(|ch| ch.is_ascii_digit())
                    {
                        num_len += 2;
                        while self.consume_next_char_if_match(|ch| ch.is_ascii_digit()) {
                            num_len += 1;
                        }
                    }
                    self.offset_in_line += num_len;
                    // SAFETY: offset is generated as a valid utf-8 offset per CharIndices
                    let num_slice = unsafe { self.code_subslice(offset, num_len) };
                    let number = num_slice.parse::<f64>().unwrap();
                    let token = Token {
                        data: TokenType::Number(number),
                        pos,
                    };
                    Ok(token)
                }
                b'"' => {
                    // TODO: Handle escaping
                    let mut str_len = 0;
                    // Strings are multiline, so we need to track things like whether or not we cross a newline
                    while self.offset < self.code.len() && self.code[self.offset] != b'"' {
                        let ch = self.code[self.offset];
                        self.offset += 1;
                        str_len += 1;
                        if ch == b'\n' {
                            self.offset_in_line = 0;
                            self.line += 1;
                        } else {
                            self.offset_in_line += 1;
                        }
                    }
                    if self.offset == self.code.len() {
                        Err(Error {
                            error: ErrorType::UnterminatedString,
                            pos,
                        })
                    } else {
                        // We validly closed the string, we also need to consume the final '"'
                        self.offset += 1;
                        self.offset_in_line += 1;

                        // We slice str_len -1 since we want to snip the trailing quote
                        let string = unsafe {
                            // SAFETY: The only way to terminate the string validly is between valid single byte characters of "
                            self.code_subslice(offset + 1, str_len)
                        };
                        Ok(Token {
                            data: TokenType::String(string),
                            pos,
                        })
                    }
                }
                c if c.is_ascii_alphabetic() => {
                    let mut num_len = 1;
                    while self.consume_next_char_if_match(|ch| ch.is_ascii_alphanumeric()) {
                        num_len += 1;
                    }
                    self.offset_in_line += num_len;
                    // SAFETY: We only accept ascii characters for identifiers and keywords
                    let identifier = unsafe { self.code_subslice(offset, num_len) };
                    let token = if let Some((_, kw)) = KEYWORD_LITERAL_TO_SYMBOL
                        .iter()
                        .find(|(lit, _)| *lit == identifier)
                    {
                        Token {
                            data: TokenType::Keyword(*kw),
                            pos,
                        }
                    } else {
                        Token {
                            data: TokenType::Identifier(identifier),
                            pos,
                        }
                    };
                    Ok(token)
                }
                _ => {
                    self.offset_in_line += 1;
                    Err(Error {
                        error: ErrorType::UnrecognizedToken,
                        pos,
                    })
                }
            }
        }
    }

    pub fn current_pos(&self) -> Pos {
        Pos {
            line: self.line,
            offset_in_line: self.offset_in_line,
        }
    }

    fn consume_next_char_if_eq(&mut self, next_ch: u8) -> bool {
        if self.offset < self.code.len() && self.code[self.offset] == next_ch {
            self.offset += 1;
            true
        } else {
            false
        }
    }

    fn consume_next_char_if_neq(&mut self, not_next_ch: u8) -> bool {
        if self.offset < self.code.len() && self.code[self.offset] != not_next_ch {
            self.offset += 1;
            true
        } else {
            false
        }
    }

    fn consume_next_char_if_match<F>(&mut self, predicate: F) -> bool
    where
        F: FnOnce(u8) -> bool,
    {
        if self.offset < self.code.len() && predicate(self.code[self.offset]) {
            self.offset += 1;
            true
        } else {
            false
        }
    }

    fn consume_next_char_if_ws(&mut self) -> bool {
        if self.offset < self.code.len() && WS_CHARS.contains(&self.code[self.offset]) {
            self.offset += 1;
            true
        } else {
            false
        }
    }

    fn gobble_whitespace(&mut self) {
        loop {
            if self.consume_next_char_if_ws() {
                self.offset_in_line += 1;
            } else if self.consume_next_char_if_eq(b'\n') {
                self.offset_in_line = 0;
                self.line += 1;
            } else {
                break;
            }
        }
    }

    // Slice the code slice to a length and and offset
    // This requires that offset point to the start of a code point
    unsafe fn code_subslice(&self, offset: usize, len: usize) -> &'lex str {
        // TODO: We do this in 2 parts, we are able to jump to the start of the of the code slice directly
        // For now, however, there isn't a great mechanism for immediately finding the end
        // The consume_next_char* friends don't return the ending offset
        // We accept that hopefully most literal strings will be smallish
        let initial_skip = std::str::from_utf8_unchecked(&self.code[offset..]);
        &initial_skip[0..len]
    }
}

const WS_CHARS: &'static [u8] = b" \r\t";

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn scan_anything() {
        let code = "var";
        let mut scanner = Scanner::new(&code);
        let first_token = scanner.next().unwrap();
        match first_token.data {
            TokenType::Keyword(keyword) => {
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
        let token = scanner.next().unwrap();
        match token.data {
            TokenType::Keyword(keyword) => {
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

        let token = scanner.next().unwrap();
        match token.data {
            TokenType::Identifier(identifier) => {
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

        let token = scanner.next().unwrap();
        match token.data {
            TokenType::Symbol(symbol) => {
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

        let token = scanner.next().unwrap();
        match token.data {
            TokenType::String(string) => {
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

        let token = scanner.next().unwrap();
        match token.data {
            TokenType::Eof => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_multi_line_string_pos() {
        let code = r#"
"marco
bomp";
"#;
        let mut scanner = Scanner::new(&code);
        // Did we get a string?
        let token = scanner.next().unwrap();
        match token.data {
            TokenType::String(string) => {
                assert_eq!("marco\nbomp", string);
                assert_eq!(0, token.pos.offset_in_line);
                assert_eq!(1, token.pos.line);
            }
            _ => unreachable!(),
        }
        // Did we correctly update the lines etc
        let token = scanner.next().unwrap();
        match token.data {
            TokenType::Symbol(symbol) => {
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
        let token = scanner.next();
        assert_eq!(ErrorType::UnterminatedString, token.unwrap_err().error);
        let token = scanner.next();
        assert_eq!(TokenType::Eof, token.unwrap().data);
    }

    #[test]
    fn no_infinite_seq_on_bad_token() {
        let code = "$var";
        let mut scanner = Scanner::new(&code);
        let token = scanner.next();
        assert_eq!(ErrorType::UnrecognizedToken, token.unwrap_err().error);
    }
}
