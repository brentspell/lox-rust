/*!
# Lox language data model and helpers.
*/

use std::fmt;

mod env;
pub mod interp;
pub mod lexer;
pub mod parser;
mod reader;

#[derive(Debug)]
pub struct Program {
    stmts: Vec<Stmt>,
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, e) in self.stmts.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            e.fmt(f)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Stmt {
    Block(Vec<Stmt>),
    Decl(Token, Expr),
    Expr(Expr),
    Print(Expr),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Block(stmts) => {
                writeln!(f, "{{")?;
                for (i, e) in stmts.iter().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    e.fmt(f)?;
                }
                writeln!(f, "}}")?;
                Ok(())
            }
            Self::Decl(tok, expr) => {
                if let Expr::Literal(Value::Nil) = expr {
                    write!(f, "var {};", tok.lexeme)
                } else {
                    write!(f, "var {} = {};", tok.lexeme, expr)
                }
            }
            Self::Expr(expr) => write!(f, "{};", expr),
            Self::Print(expr) => write!(f, "print {};", expr),
        }
    }
}

/**
This enumeration represents an Abstract Syntax Tree (AST) for an expression in Lox.
*/
#[derive(Debug)]
pub enum Expr {
    Assignment(Token, Box<Expr>),
    Binary(Box<Expr>, Token, Box<Expr>),
    Grouping(Box<Expr>),
    Literal(Value),
    Unary(Token, Box<Expr>),
    Variable(Token),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Assignment(var, expr) => write!(f, "{} = {}", var.lexeme, expr),
            Self::Binary(lhs, op, rhs) => write!(f, "{} {} {}", lhs, op.lexeme, rhs),
            Self::Grouping(expr) => write!(f, "({})", expr),
            Self::Literal(value) => write!(f, "{}", value),
            Self::Unary(op, expr) => write!(f, "{}{}", op.lexeme, expr),
            Self::Variable(var) => write!(f, "{}", var.lexeme),
        }
    }
}

/**
The token structure is the lexical unit in the Lox language.
*/
#[derive(Debug)]
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
            self.line, self.typ, self.lexeme,
        )
    }
}

/**
These are the supported token types returned by the Lox lexer.
*/
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

impl TokenType {
    pub fn is_equality(&self) -> bool {
        use TokenType::*;
        matches!(self, BangEqual | EqualEqual)
    }

    pub fn is_comparison(&self) -> bool {
        use TokenType::*;
        matches!(self, Greater | GreaterEqual | Less | LessEqual)
    }

    pub fn is_term(&self) -> bool {
        use TokenType::*;
        matches!(self, Minus | Plus)
    }

    pub fn is_factor(&self) -> bool {
        use TokenType::*;
        matches!(self, Slash | Star)
    }

    pub fn is_unary(&self) -> bool {
        use TokenType::*;
        matches!(self, Bang | Minus)
    }

    pub fn is_stmt_begin(&self) -> bool {
        use TokenType::*;
        matches!(self, Class | For | Fun | If | Print | Return | Var | While)
    }
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/**
This structure represents a literal/primitive value in the Lox language.
*/
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Nil,
    Boolean(bool),
    Num(f64),
    Str(String),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&match self {
            Value::Nil => "nil".to_string(),
            Value::Boolean(value) => value.to_string(),
            Value::Num(value) => {
                if value % 1.0 == 0.0 {
                    (*value as i64).to_string()
                } else {
                    value.to_string()
                }
            }
            Value::Str(value) => format!("\"{value}\""),
        })
    }
}
