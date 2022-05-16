/*!
# Lox language data model and helpers.
*/

use std::fmt;
use std::sync::{Arc, Mutex};

mod env;
pub mod interp;
pub mod lexer;
pub mod parser;
mod reader;
mod scope;

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum Stmt {
    Block(Vec<Stmt>),
    Break(bool),
    Var(Token, String, Expr),
    Expr(Expr),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Print(Expr),
    While(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Fun(Token, String, Vec<String>, Box<Stmt>),
    Return(Token, Expr),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Block(stmts) => {
                writeln!(f, "{{")?;
                for e in stmts.iter() {
                    writeln!(f, "{}", e)?;
                }
                writeln!(f, "}}")?;
                Ok(())
            }
            Self::Break(cont) => write!(f, "{};", if *cont { "continue" } else { "break" }),
            Self::Var(tok, _name, expr) => {
                if let Expr::Literal(Value::Nil) = expr {
                    write!(f, "var {};", tok.lexeme)
                } else {
                    write!(f, "var {} = {};", tok.lexeme, expr)
                }
            }
            Self::Expr(expr) => write!(f, "{};", expr),
            Self::If(cond, cons, None) => write!(f, "if ({}) {}", cond, cons),
            Self::If(cond, cons, Some(alt)) => write!(f, "if ({}) {} else {}", cond, cons, alt),
            Self::Print(expr) => write!(f, "print {};", expr),
            Self::While(cond, body, None) => write!(f, "while ({}) {}", cond, body),
            Self::While(cond, body, Some(post)) => write!(f, "while ({}) {} {}", cond, body, post),
            Self::Fun(tok, _name, params, body) => {
                write!(f, "fun {}(", tok.lexeme)?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    p.split("::").last().unwrap().fmt(f)?;
                }
                write!(f, ") {}", body)?;
                Ok(())
            }
            Self::Return(_tok, expr) => write!(f, "return {};", expr),
        }
    }
}

/**
This enumeration represents an Abstract Syntax Tree (AST) for an expression in Lox.
*/
#[derive(Debug, Clone)]
pub enum Expr {
    Assignment(Token, String, Box<Expr>),
    Binary(Box<Expr>, Token, Box<Expr>),
    Call(Box<Expr>, Token, Vec<Expr>),
    Grouping(Box<Expr>),
    Literal(Value),
    Logical(Box<Expr>, Token, Box<Expr>),
    Unary(Token, Box<Expr>),
    Variable(Token, String),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Assignment(tok, _qname, expr) => write!(f, "{} = {}", tok.lexeme, expr),
            Self::Binary(lhs, op, rhs) => write!(f, "{} {} {}", lhs, op.lexeme, rhs),
            Self::Call(callee, _paren, args) => {
                write!(f, "{}(", callee)?;
                for (i, e) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    e.fmt(f)?;
                }
                write!(f, ")")?;
                Ok(())
            }
            Self::Grouping(expr) => write!(f, "({})", expr),
            Self::Literal(value) => write!(f, "{}", value),
            Self::Logical(lhs, op, rhs) => write!(f, "{} {} {}", lhs, op.lexeme, rhs),
            Self::Unary(op, expr) => write!(f, "{}{}", op.lexeme, expr),
            Self::Variable(tok, _qname) => write!(f, "{}", tok.lexeme),
        }
    }
}

/**
The token structure is the lexical unit in the Lox language.
*/
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
            self.line, self.typ, self.lexeme,
        )
    }
}

/**
These are the supported token types returned by the Lox lexer.
*/
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TokenType {
    Break,
    Continue,
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
#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Boolean(bool),
    Num(f64),
    Str(String),
    Fun(Box<Stmt>, Arc<Mutex<crate::lang::env::Env>>),
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Boolean(v1), Self::Boolean(v2)) => v1 == v2,
            (Self::Num(v1), Self::Num(v2)) => v1 == v2,
            (Self::Str(v1), Self::Str(v2)) => v1 == v2,
            _ => false,
        }
    }
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
            Value::Fun(stmt, _env) => match &**stmt {
                Stmt::Fun(tok, _, _, _) => format!("<function {}>", tok.lexeme),
                _ => panic!("invalid function value"),
            },
        })
    }
}
