use std::fmt;

pub mod lexer;
mod reader;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TokenType {
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
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Identifier,
    String,
    Number,
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

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub typ: TokenType,
    pub line: u32,
    pub lexeme: String,
    pub literal: Value,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "line: {:4} type: {:12} lexeme: {}",
            self.line,
            self.typ.to_string(),
            self.lexeme,
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Nil,
    Bool(bool),
    Str(String),
    Num(f64),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&match self {
            Value::Nil => "nil".to_string(),
            Value::Bool(value) => value.to_string(),
            Value::Str(value) => format!("\"{value}\""),
            Value::Num(value) => value.to_string(),
        })
    }
}
