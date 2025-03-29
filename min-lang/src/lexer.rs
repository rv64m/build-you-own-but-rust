use lazy_static::lazy_static;

use std::{collections::HashMap, fmt::Display, hash::Hash};

lazy_static! {
    static ref KEYWORDS: HashMap<Literal, TokenType> = {
        let mut m = HashMap::new();
        m.insert("fn".to_string(), TokenType::Function);
        m.insert("let".to_string(), TokenType::Let);
        m.insert("return".to_string(), TokenType::Return);
        m.insert("if".to_string(), TokenType::If);
        m.insert("else".to_string(), TokenType::Else);
        m.insert("true".to_string(), TokenType::True);
        m.insert("false".to_string(), TokenType::False);
        m
    };
}

/// Define token
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum TokenType {
    Illegal,
    Eof,
    Ident,
    True,
    False,
    Int,
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    Lt,
    Gt,
    Comma,
    Semicolon,
    LParaen,
    RParaen,
    LBrace,
    RBrace,
    Function,
    Let,
    If,
    Else,
    Return,
    Eq,
    Ne,
}

pub type Literal = String;

#[derive(Debug, Clone)]
pub struct Token {
    tok: TokenType,
    literal: Literal,
}

impl Token {
    pub fn new(token_type: TokenType, literal: Literal) -> Self {
        Self {
            tok: token_type,
            literal,
        }
    }

    pub fn token_type(&self) -> TokenType {
        self.tok
    }

    pub fn literal(&self) -> Literal {
        self.literal.clone()
    }

    pub fn is_eof(&self) -> bool {
        return self.tok == TokenType::Eof;
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Token({},{})", self.tok, self.literal)
    }
}

impl Default for Token {
    fn default() -> Self {
        Self::new(TokenType::Illegal, String::default())
    }
}

pub struct Lexer {
    chars: Vec<u8>,
    ch: char,
    read_pos: usize,
    pos: usize,
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        let mut lexer = Self {
            chars: input.as_bytes().to_owned(),
            ch: '\0',
            read_pos: 0,
            pos: 0,
        };

        lexer.read_char();
        lexer
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();
        let res = match self.ch {
            '\0' => Token::new(TokenType::Eof, "\0".to_string()),
            '=' => {
                let next_ch = self.peek_char();
                if next_ch == '=' {
                    self.read_char();
                    Token::new(TokenType::Eq, "==".to_string())
                } else {
                    Token::new(TokenType::Assign, self.ch.to_string())
                }
            }
            '+' => Token::new(TokenType::Plus, self.ch.to_string()),
            '-' => Token::new(TokenType::Minus, self.ch.to_string()),
            '*' => Token::new(TokenType::Asterisk, self.ch.to_string()),
            '/' => Token::new(TokenType::Slash, self.ch.to_string()),
            '!' => {
                let next_ch = self.peek_char();
                if next_ch == '=' {
                    self.read_char();
                    Token::new(TokenType::Ne, "!=".to_string())
                } else {
                    Token::new(TokenType::Bang, self.ch.to_string())
                }
            }

            '>' => Token::new(TokenType::Gt, self.ch.to_string()),
            '<' => Token::new(TokenType::Lt, self.ch.to_string()),
            '(' => Token::new(TokenType::LParaen, self.ch.to_string()),
            ')' => Token::new(TokenType::RParaen, self.ch.to_string()),
            '{' => Token::new(TokenType::LBrace, self.ch.to_string()),
            '}' => Token::new(TokenType::RBrace, self.ch.to_string()),
            ',' => Token::new(TokenType::Comma, self.ch.to_string()),
            ';' => Token::new(TokenType::Semicolon, self.ch.to_string()),
            _ => {
                if is_letter(self.ch) {
                    let literal = self.read_identifier();
                    let token_type = lookup_ident(&literal);
                    return Token::new(token_type, literal);
                } else if is_digit(self.ch) {
                    let number = self.read_number();
                    return number
                        .parse::<i64>()
                        .map_or(Token::new(TokenType::Illegal, self.ch.to_string()), |_| {
                            Token::new(TokenType::Int, number)
                        });
                } else {
                    return Token::new(TokenType::Illegal, self.ch.to_string());
                }
            }
        };
        self.read_char();
        res
    }

    fn read_char(&mut self) {
        if self.read_pos >= self.chars.len() {
            self.ch = '\0';
            return;
        }

        self.ch = char::from(self.chars[self.read_pos]);
        self.pos = self.read_pos;
        self.read_pos += 1;
    }

    fn peek_char(&self) -> char {
        if self.read_pos >= self.chars.len() {
            return '\0';
        }

        return char::from(self.chars[self.read_pos]);
    }

    fn read_identifier(&mut self) -> Literal {
        let pos = self.pos;
        while is_letter(self.ch) {
            self.read_char();
        }
        std::str::from_utf8(&self.chars[pos..self.pos])
            .expect("failed identifier")
            .to_string()
    }

    fn read_number(&mut self) -> Literal {
        let pos = self.pos;
        while is_digit(self.ch) {
            self.read_char();
        }
        std::str::from_utf8(&self.chars[pos..self.pos])
            .expect("failed identifier")
            .to_string()
    }

    fn skip_whitespace(&mut self) {
        loop {
            if self.ch == ' ' || self.ch == '\t' || self.ch == '\n' || self.ch == '\r' {
                self.read_char();
            } else {
                break;
            }
        }
    }
}

fn is_letter(ch: char) -> bool {
    return ('a' <= ch && ch <= 'z') || ('A' <= ch && ch <= 'Z') || ch == '_';
}

fn is_digit(ch: char) -> bool {
    return '0' <= ch && ch <= '9';
}

fn lookup_ident(literal: &Literal) -> TokenType {
    KEYWORDS.get(literal).map_or(TokenType::Ident, |tok| *tok)
}

impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenType::Illegal => write!(f, "ILLEGAL"),
            TokenType::Eof => write!(f, "EOF"),
            TokenType::Ident => write!(f, "IDENT"),
            TokenType::Int => write!(f, "INT"),
            TokenType::Assign => write!(f, "ASSIGN"),
            TokenType::Plus => write!(f, "PLUS"),
            TokenType::Minus => write!(f, "MINUS"),
            TokenType::Asterisk => write!(f, "ASTERISK"),
            TokenType::Slash => write!(f, "SLASH"),
            TokenType::Bang => write!(f, "BANG"),
            TokenType::Gt => write!(f, "GT"),
            TokenType::Lt => write!(f, "LT"),
            TokenType::Comma => write!(f, "COMMA"),
            TokenType::Semicolon => write!(f, "SEMICOLON"),
            TokenType::LParaen => write!(f, "LPAREN"),
            TokenType::RParaen => write!(f, "RPAREN"),
            TokenType::LBrace => write!(f, "LBRACE"),
            TokenType::RBrace => write!(f, "RBRACE"),
            TokenType::Function => write!(f, "FUNCTION"),
            TokenType::Let => write!(f, "LET"),
            TokenType::Return => write!(f, "RETURN"),
            TokenType::If => write!(f, "IF"),
            TokenType::Else => write!(f, "ELSE"),
            TokenType::True => write!(f, "TRUE"),
            TokenType::False => write!(f, "FALSE"),
            TokenType::Eq => write!(f, "EQ"),
            TokenType::Ne => write!(f, "NE"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Lexer, TokenType};

    struct TestCase {
        expected_token_type: TokenType,
        expected_literal: String,
    }

    impl TestCase {
        fn new(token_type: TokenType, literal: &str) -> Self {
            Self {
                expected_literal: literal.to_owned(),
                expected_token_type: token_type,
            }
        }
    }

    #[test]
    fn test_next_token() {
        let input = r#"
        let five = 5;
        let ten = 10;
        let add = fn(x,y){
            x + y;
        };

        let result = add(five, ten);
        !-/*5;
        5 < 10 > 5;

        if (5 < 10) {
            return true;
        } else {
            return false;
        }

        10 == 10;
        5 != 10;
        "#;

        let test_cases: Vec<TestCase> = vec![
            TestCase::new(TokenType::Let, "let"),
            TestCase::new(TokenType::Ident, "five"),
            TestCase::new(TokenType::Assign, "="),
            TestCase::new(TokenType::Int, "5"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::Let, "let"),
            TestCase::new(TokenType::Ident, "ten"),
            TestCase::new(TokenType::Assign, "="),
            TestCase::new(TokenType::Int, "10"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::Let, "let"),
            TestCase::new(TokenType::Ident, "add"),
            TestCase::new(TokenType::Assign, "="),
            TestCase::new(TokenType::Function, "fn"),
            TestCase::new(TokenType::LParaen, "("),
            TestCase::new(TokenType::Ident, "x"),
            TestCase::new(TokenType::Comma, ","),
            TestCase::new(TokenType::Ident, "y"),
            TestCase::new(TokenType::RParaen, ")"),
            TestCase::new(TokenType::LBrace, "{"),
            TestCase::new(TokenType::Ident, "x"),
            TestCase::new(TokenType::Plus, "+"),
            TestCase::new(TokenType::Ident, "y"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::RBrace, "}"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::Let, "let"),
            TestCase::new(TokenType::Ident, "result"),
            TestCase::new(TokenType::Assign, "="),
            TestCase::new(TokenType::Ident, "add"),
            TestCase::new(TokenType::LParaen, "("),
            TestCase::new(TokenType::Ident, "five"),
            TestCase::new(TokenType::Comma, ","),
            TestCase::new(TokenType::Ident, "ten"),
            TestCase::new(TokenType::RParaen, ")"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::Bang, "!"),
            TestCase::new(TokenType::Minus, "-"),
            TestCase::new(TokenType::Slash, "/"),
            TestCase::new(TokenType::Asterisk, "*"),
            TestCase::new(TokenType::Int, "5"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::Int, "5"),
            TestCase::new(TokenType::Lt, "<"),
            TestCase::new(TokenType::Int, "10"),
            TestCase::new(TokenType::Gt, ">"),
            TestCase::new(TokenType::Int, "5"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::If, "if"),
            TestCase::new(TokenType::LParaen, "("),
            TestCase::new(TokenType::Int, "5"),
            TestCase::new(TokenType::Lt, "<"),
            TestCase::new(TokenType::Int, "10"),
            TestCase::new(TokenType::RParaen, ")"),
            TestCase::new(TokenType::LBrace, "{"),
            TestCase::new(TokenType::Return, "return"),
            TestCase::new(TokenType::True, "true"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::RBrace, "}"),
            TestCase::new(TokenType::Else, "else"),
            TestCase::new(TokenType::LBrace, "{"),
            TestCase::new(TokenType::Return, "return"),
            TestCase::new(TokenType::False, "false"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::RBrace, "}"),
            TestCase::new(TokenType::Int, "10"),
            TestCase::new(TokenType::Eq, "=="),
            TestCase::new(TokenType::Int, "10"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::Int, "5"),
            TestCase::new(TokenType::Ne, "!="),
            TestCase::new(TokenType::Int, "10"),
            TestCase::new(TokenType::Semicolon, ";"),
            TestCase::new(TokenType::Eof, "\0"),
        ];

        let mut lexer = Lexer::new(input);

        for tc in test_cases.iter() {
            let token = lexer.next_token();

            assert_eq!(
                tc.expected_token_type,
                token.token_type(),
                "expected token: {}, found token: {}",
                tc.expected_token_type,
                token.token_type()
            );

            assert_eq!(
                tc.expected_literal,
                token.literal(),
                "expected token literal: {}, found literal: {}",
                tc.expected_literal,
                token.literal()
            );
        }
    }
}
