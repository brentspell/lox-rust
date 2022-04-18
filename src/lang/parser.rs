/*!
# The Lox language parser

## Usage
```
use crate::lang::{lexer, parser};

let lexer = lexer::Lexer::from_str(r#"print "Hello World";"#);
let expr = parser::Parser::new(Box::new(lexer)).parse()?;
dbg!(expr);
```

*/

use std::fmt;

use anyhow::{bail, Error, Result};

use crate::lang::reader::LookaheadReader;
use crate::lang::{Expr, Token, TokenType, Value};

/**
This struct maintains the current state of the parser as it progresses through the token
stream (usually a lexer). The parser maintains an internal lookahead buffer for peeking
at an arbitrary number of tokens ahead of the current position.
*/
pub struct Parser {
    reader: LookaheadReader<Token>,
}

impl Parser {
    /**
    Creates a new parser instance from a token stream.

    # Arguments
    * `tokens` - iterator over a sequence of tokens, usually a lexer instance

    # Returns
    The initialized parser.
    */
    pub fn new(tokens: Box<dyn Iterator<Item = Result<Token>>>) -> Parser {
        Self {
            reader: LookaheadReader::new(tokens),
        }
    }

    /**
    Parses the current token stream.

    # Returns
    A parse tree representing the user's program. If any errors occur, they are stored in
    a ParseErrors struct and embedded in an anyhow error. All errors encountered are printed
    by the default formatter, but individual errors can be accessed by downcasting the
    anyhow error and calling into_iter().
    */
    pub fn parse_all(&mut self) -> Result<Expr> {
        let expr = self.parse()?;
        if let Some(tok) = self.peek(0)? {
            bail!("expected end of input, found: {}", tok.lexeme);
        }
        Ok(expr)
    }

    /**
    Parses the current token stream.

    # Returns
    A parse tree representing the user's program.
    */
    pub fn parse(&mut self) -> Result<Expr> {
        let mut errors = ParseErrors::new();
        loop {
            // continue parsing, only return an expression if no errors occurred
            match (self.expression(), errors.is_empty()) {
                (Ok(expr), true) => break Ok(expr),
                (Ok(_), false) => bail!(errors),
                (Err(error), _) => {
                    // parse error, attempt to sync so we can collect more errors
                    errors.push(error);
                    match self.synchronize() {
                        Ok(true) => continue,
                        Ok(false) => bail!(errors),
                        Err(error) => errors.push(error),
                    }
                }
            }
        }
    }

    fn expression(&mut self) -> Result<Expr> {
        self.equality()
    }

    fn equality(&mut self) -> Result<Expr> {
        let mut expr = self.comparison()?;
        while matches!(self.peek_type(0)?, Some(typ) if typ.is_equality()) {
            expr = Expr::Binary(Box::new(expr), self.read()?, Box::new(self.comparison()?));
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> Result<Expr> {
        let mut expr = self.term()?;
        while matches!(self.peek_type(0)?, Some(typ) if typ.is_comparison()) {
            expr = Expr::Binary(Box::new(expr), self.read()?, Box::new(self.term()?));
        }
        Ok(expr)
    }

    fn term(&mut self) -> Result<Expr> {
        let mut expr = self.factor()?;
        while matches!(self.peek_type(0)?, Some(typ) if typ.is_term()) {
            expr = Expr::Binary(Box::new(expr), self.read()?, Box::new(self.factor()?));
        }
        Ok(expr)
    }

    fn factor(&mut self) -> Result<Expr> {
        let mut expr = self.unary()?;
        while matches!(self.peek_type(0)?, Some(typ) if typ.is_factor()) {
            expr = Expr::Binary(Box::new(expr), self.read()?, Box::new(self.unary()?));
        }
        Ok(expr)
    }

    fn unary(&mut self) -> Result<Expr> {
        if matches!(self.peek_type(0)?, Some(typ) if typ.is_unary()) {
            Ok(Expr::Unary(self.read()?, Box::new(self.unary()?)))
        } else {
            self.primary()
        }
    }

    fn primary(&mut self) -> Result<Expr> {
        let tok = self.read()?;
        Ok(match tok.typ {
            TokenType::Nil => Expr::Literal(Value::Nil),
            TokenType::False => Expr::Literal(Value::Boolean(false)),
            TokenType::True => Expr::Literal(Value::Boolean(true)),
            TokenType::Number => Expr::Literal(tok.literal),
            TokenType::String => Expr::Literal(tok.literal),
            TokenType::LeftParen => self.grouping()?,
            _ => bail!(
                "line {}: expected literal or (, found {}",
                tok.line,
                tok.lexeme
            ),
        })
    }

    fn grouping(&mut self) -> Result<Expr> {
        let expr = self.expression()?;
        Ok(match self.peek(0)? {
            Some(tok) if tok.typ == TokenType::RightParen => {
                self.read()?;
                Expr::Grouping(Box::new(expr))
            }
            Some(tok) => bail!(
                "line {}: expected ) after expression, found {}",
                tok.line,
                tok.lexeme
            ),
            None => bail!("expected ) after expression, found end of input"),
        })
    }

    fn synchronize(&mut self) -> Result<bool> {
        Ok(loop {
            match self.peek_type(0)? {
                None => {
                    break false;
                }
                Some(TokenType::Semicolon) => {
                    self.read()?;
                    break self.peek(0)?.is_some();
                }
                Some(typ) if typ.is_stmt_begin() => {
                    break true;
                }
                _ => {
                    self.read()?;
                }
            }
        })
    }

    fn read(&mut self) -> Result<Token> {
        if let Some(tok) = self.reader.read()? {
            Ok(tok)
        } else {
            bail!("unexpected end of input")
        }
    }

    fn peek(&mut self, ahead: usize) -> Result<Option<&Token>> {
        self.reader.peek(ahead)
    }

    fn peek_type(&mut self, ahead: usize) -> Result<Option<TokenType>> {
        Ok(self.peek(ahead)?.map(|t| t.typ))
    }
}

/**
Parse error structure, which maintains a sequence of all errors that occurred during parsing.
*/
#[derive(Debug)]
pub struct ParseErrors {
    errors: Vec<Error>,
}

impl ParseErrors {
    /**
    Creates a new parse errors instance.
    */
    pub fn new() -> Self {
        Self { errors: Vec::new() }
    }

    /**
    Returns true if there are no parse errors, false otherwise.
    */
    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }

    /**
    Adds a new parse error to the list.
    */
    pub fn push(&mut self, e: Error) {
        self.errors.push(e);
    }
}

impl IntoIterator for ParseErrors {
    type Item = Error;
    type IntoIter = ::std::vec::IntoIter<Error>;

    fn into_iter(self) -> Self::IntoIter {
        self.errors.into_iter()
    }
}

impl fmt::Display for ParseErrors {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for e in self.errors.iter() {
            e.fmt(f)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::lexer::Lexer;

    use super::*;

    #[test]
    fn test_errors() {
        assert!(parse("")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(parse("😀")
            .unwrap_err()
            .to_string()
            .contains("unexpected character"));
        assert!(parse("+")
            .unwrap_err()
            .to_string()
            .contains("expected literal or ("));
        assert!(parse("(")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(parse("(1")
            .unwrap_err()
            .to_string()
            .contains("expected ) after expression, found end of input"));
        assert!(parse("(1 2")
            .unwrap_err()
            .to_string()
            .contains("expected ) after expression"));

        assert_eq!(
            parse("")
                .unwrap_err()
                .downcast::<ParseErrors>()
                .unwrap()
                .into_iter()
                .count(),
            1
        );
        assert_eq!(
            parse("😀;1😀")
                .unwrap_err()
                .downcast::<ParseErrors>()
                .unwrap()
                .into_iter()
                .count(),
            2
        );
    }

    #[test]
    fn test_primary() {
        assert!(roundtrip("nil"));
        assert!(roundtrip("true"));
        assert!(roundtrip("false"));
        assert!(roundtrip("42"));
        assert!(roundtrip(r#""test""#));

        assert!(matches!(parse("nil"), Ok(Expr::Literal(Value::Nil))));
        assert!(matches!(
            parse("true"),
            Ok(Expr::Literal(Value::Boolean(true)))
        ));
        assert!(matches!(
            parse("false"),
            Ok(Expr::Literal(Value::Boolean(false)))
        ));
        assert!(matches!(
            parse("42"),
            Ok(Expr::Literal(Value::Num(x))) if x == 42.0
        ));
        assert!(matches!(
            parse(r#""test""#),
            Ok(Expr::Literal(Value::Str(s))) if s == "test"
        ));
    }

    #[test]
    fn test_unary() {
        assert!(roundtrip("-1"));
        assert!(roundtrip("--2"));
        assert!(roundtrip("!true"));
        assert!(roundtrip("!!false"));

        match parse("-1") {
            Ok(Expr::Unary(op, value)) => {
                assert_eq!(op.typ, TokenType::Minus);
                assert!(matches!(*value, Expr::Literal(Value::Num(x)) if x == 1.0));
            }
            _ => panic!(),
        }
        match parse("!!true") {
            Ok(Expr::Unary(op1, expr2)) => {
                assert_eq!(op1.typ, TokenType::Bang);
                match *expr2 {
                    Expr::Unary(op2, value) => {
                        assert_eq!(op2.typ, TokenType::Bang);
                        assert!(matches!(*value, Expr::Literal(Value::Boolean(true))));
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_factor() {
        assert!(roundtrip("1 * 2"));
        assert!(roundtrip("3 / 4"));
        assert!(roundtrip("1 * 2 / 3"));

        match parse("1 * 2") {
            Ok(Expr::Binary(value1, op, value2)) => {
                assert_eq!(op.typ, TokenType::Star);
                assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
            }
            _ => panic!(),
        }

        match parse("1 * 2 / 3") {
            Ok(Expr::Binary(expr1, op2, value3)) => {
                assert_eq!(op2.typ, TokenType::Slash);
                assert!(matches!(*value3, Expr::Literal(Value::Num(x)) if x == 3.0));
                match *expr1 {
                    Expr::Binary(value1, op1, value2) => {
                        assert_eq!(op1.typ, TokenType::Star);
                        assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                        assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_term() {
        assert!(roundtrip("1 + 2"));
        assert!(roundtrip("3 - 4"));
        assert!(roundtrip("1 + 2 - 3"));

        match parse("1 + 2") {
            Ok(Expr::Binary(value1, op, value2)) => {
                assert_eq!(op.typ, TokenType::Plus);
                assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
            }
            _ => panic!(),
        }

        match parse("1 + 2 - 3") {
            Ok(Expr::Binary(expr1, op2, value3)) => {
                assert_eq!(op2.typ, TokenType::Minus);
                assert!(matches!(*value3, Expr::Literal(Value::Num(x)) if x == 3.0));
                match *expr1 {
                    Expr::Binary(value1, op1, value2) => {
                        assert_eq!(op1.typ, TokenType::Plus);
                        assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                        assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_comparison() {
        assert!(roundtrip("1 > 2"));
        assert!(roundtrip("3 >= 4"));
        assert!(roundtrip("1 < 2 <= 3"));

        match parse("1 > 2") {
            Ok(Expr::Binary(value1, op, value2)) => {
                assert_eq!(op.typ, TokenType::Greater);
                assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
            }
            _ => panic!(),
        }

        match parse("1 < 2 <= 3") {
            Ok(Expr::Binary(expr1, op2, value3)) => {
                assert_eq!(op2.typ, TokenType::LessEqual);
                assert!(matches!(*value3, Expr::Literal(Value::Num(x)) if x == 3.0));
                match *expr1 {
                    Expr::Binary(value1, op1, value2) => {
                        assert_eq!(op1.typ, TokenType::Less);
                        assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                        assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_equality() {
        assert!(roundtrip("1 == 2"));
        assert!(roundtrip("3 != 4"));
        assert!(roundtrip("1 == 2 != 3"));

        match parse("1 == 2") {
            Ok(Expr::Binary(value1, op, value2)) => {
                assert_eq!(op.typ, TokenType::EqualEqual);
                assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
            }
            _ => panic!(),
        }

        match parse("1 == 2 != 3") {
            Ok(Expr::Binary(expr1, op2, value3)) => {
                assert_eq!(op2.typ, TokenType::BangEqual);
                assert!(matches!(*value3, Expr::Literal(Value::Num(x)) if x == 3.0));
                match *expr1 {
                    Expr::Binary(value1, op1, value2) => {
                        assert_eq!(op1.typ, TokenType::EqualEqual);
                        assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                        assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_grouping() {
        assert!(roundtrip("(1)"));
        assert!(roundtrip("(1 + 2) * 3"));
        assert!(roundtrip("3 * (1 + 2)"));

        match parse("(1)") {
            Ok(Expr::Grouping(value)) => {
                assert!(matches!(*value, Expr::Literal(Value::Num(x)) if x == 1.0));
            }
            _ => panic!(),
        }

        match parse("3 * (1 + 2)") {
            Ok(Expr::Binary(value3, op2, expr1)) => {
                assert_eq!(op2.typ, TokenType::Star);
                assert!(matches!(*value3, Expr::Literal(Value::Num(x)) if x == 3.0));
                match *expr1 {
                    Expr::Grouping(group) => match *group {
                        Expr::Binary(value1, op1, value2) => {
                            assert_eq!(op1.typ, TokenType::Plus);
                            assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                            assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
                        }
                        _ => panic!(),
                    },
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_precedence() {
        assert!(roundtrip("1 == 2 < 3 + 4 * -5"));

        match parse("1 == 2 < 3 + 4 * -5") {
            Ok(Expr::Binary(_, eqop, eq2)) => {
                assert_eq!(eqop.typ, TokenType::EqualEqual);
                match *eq2 {
                    Expr::Binary(_, ltop, lt2) => {
                        assert_eq!(ltop.typ, TokenType::Less);
                        match *lt2 {
                            Expr::Binary(_, plop, pl2) => {
                                assert_eq!(plop.typ, TokenType::Plus);
                                match *pl2 {
                                    Expr::Binary(_, muop, un) => {
                                        assert_eq!(muop.typ, TokenType::Star);
                                        match *un {
                                            Expr::Unary(unop, _) => {
                                                assert_eq!(unop.typ, TokenType::Minus);
                                            }
                                            _ => panic!(),
                                        }
                                    }
                                    _ => panic!(),
                                }
                            }
                            _ => panic!(),
                        }
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    fn parse(string: &str) -> Result<Expr> {
        Parser::new(Box::new(Lexer::from_str(string))).parse_all()
    }

    fn roundtrip(string: &str) -> bool {
        format!("{}", parse(string).unwrap()) == string
    }
}
