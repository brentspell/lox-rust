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

use anyhow::{anyhow, bail, Error, Result};

use crate::lang::reader::LookaheadReader;
use crate::lang::{Expr, Program, Stmt, Token, TokenType, Value};

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
    pub fn parse(&mut self) -> Result<Program> {
        let mut stmts = Vec::new();
        let mut errors = ParseErrors::new();

        // parse the whole program
        loop {
            match self.declaration() {
                Ok(None) => break,
                Ok(Some(stmt)) => stmts.push(stmt),
                Err(error) => {
                    // parse error, attempt to sync so we can collect more errors
                    errors.push(error);
                    match self.synchronize() {
                        Ok(true) => continue,
                        Ok(false) => break,
                        Err(error) => errors.push(error),
                    }
                }
            }
        }

        // return failure if any parse errors were encountered
        if !errors.is_empty() {
            bail!(errors);
        }

        Ok(Program { stmts })
    }

    /**
    Parses a single expression from the token stream. Consumes the whole stream.

    # Returns
    A parse tree representing the user's program.
    */
    #[allow(dead_code)]
    pub fn parse_expr(&mut self) -> Result<Expr> {
        let mut errors = ParseErrors::new();

        // parse until we hit the first valid expression
        let expr = loop {
            match self.expression() {
                Ok(expr) => break expr,
                Err(error) => {
                    // parse error, attempt to sync so we can collect more errors
                    errors.push(error);
                    match self.synchronize() {
                        Ok(true) => continue,
                        Ok(false) => bail!(errors),
                        Err(error) => errors.push(error),
                    }
                }
            }
        };

        // ensure we have consumed the whole input
        match self.peek(0) {
            Ok(None) => (),
            Ok(Some(tok)) => errors.push(anyhow!(
                "line {}: expected end of input, found: {}",
                tok.line,
                tok.lexeme
            )),
            Err(error) => errors.push(error),
        }

        // return failure if any parse errors were encountered
        if !errors.is_empty() {
            bail!(errors);
        }

        Ok(expr)
    }

    fn declaration(&mut self) -> Result<Option<Stmt>> {
        match self.peek_type(0)? {
            None => Ok(None),
            Some(TokenType::Var) => {
                self.read()?;

                // match the variable name
                let var = self.read()?;
                if var.typ != TokenType::Identifier {
                    bail!(
                        "line {}: expected identifier, found {}",
                        var.line,
                        var.lexeme
                    );
                }

                // match the optional variable value
                let val = if self.peek_type(0)? == Some(TokenType::Equal) {
                    self.read()?;
                    self.expression()?
                } else {
                    Expr::Literal(Value::Nil)
                };

                // match the statement terminator
                let end = self.read()?;
                if end.typ != TokenType::Semicolon {
                    bail!(
                        "line {}: expected ; or expression, found {}",
                        end.line,
                        end.lexeme
                    );
                }
                Ok(Some(Stmt::Decl(var, val)))
            }

            _ => Ok(Some(self.statement()?)),
        }
    }

    fn statement(&mut self) -> Result<Stmt> {
        let stmt = match self.peek_type(0)? {
            // match special forms
            Some(TokenType::Print) => {
                self.read()?;
                Stmt::Print(self.expression()?)
            }

            // match blocks
            Some(TokenType::LeftBrace) => {
                return Ok(Stmt::Block(self.block()?));
            }

            // everything else is an expression statement
            _ => Stmt::Expr(self.expression()?),
        };

        // match the statement terminator
        let end = self.read()?;
        if end.typ != TokenType::Semicolon {
            bail!("line {}: expected ; found {}", end.line, end.lexeme);
        }

        Ok(stmt)
    }

    fn block(&mut self) -> Result<Vec<Stmt>> {
        let mut statements = Vec::new();

        self.read()?;
        loop {
            match self.peek_type(0)? {
                Some(TokenType::RightBrace) => break,
                Some(_) => statements.push(self.declaration()?.unwrap()),
                None => bail!("unexpected end of input"),
            }
        }
        self.read()?;

        Ok(statements)
    }

    fn expression(&mut self) -> Result<Expr> {
        self.assignment()
    }

    fn assignment(&mut self) -> Result<Expr> {
        let lhs = self.equality()?;
        match self.peek_type(0)? {
            Some(TokenType::Equal) => {
                self.read()?;
                let rhs = self.assignment()?;
                match lhs {
                    Expr::Variable(tok) => Ok(Expr::Assignment(tok, Box::new(rhs))),
                    _ => bail!("invalid assignment target: {}", lhs),
                }
            }
            _ => Ok(lhs),
        }
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
            TokenType::Identifier => Expr::Variable(tok),
            TokenType::LeftParen => self.grouping()?,
            _ => bail!(
                "line {}: expected expression, found {}",
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
            bail!("unexpected end of input, missing ; perhaps?")
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
    fn test_stmt_errors() {
        assert!(parse("😟;")
            .unwrap_err()
            .to_string()
            .contains("unexpected character"));
        assert_eq!(
            parse("😀;1😀")
                .unwrap_err()
                .downcast::<ParseErrors>()
                .unwrap()
                .into_iter()
                .count(),
            2
        );

        assert!(parse("var;")
            .unwrap_err()
            .to_string()
            .contains("expected identifier, found ;"));
        assert!(parse("var 42 = 1;")
            .unwrap_err()
            .to_string()
            .contains("expected identifier, found 42"));
        assert!(parse("var x =;")
            .unwrap_err()
            .to_string()
            .contains("expected expression, found ;"));
        assert!(parse("var x 42;")
            .unwrap_err()
            .to_string()
            .contains("expected ; or expression, found 42"));
        assert!(parse("var x = 42")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(parse("print 42")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(parse("print;")
            .unwrap_err()
            .to_string()
            .contains("expected expression, found ;"));
        assert!(parse("{")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(parse("{{}")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
    }

    #[test]
    fn test_expr_errors() {
        assert!(parse_expr("")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(parse_expr("😀")
            .unwrap_err()
            .to_string()
            .contains("unexpected character"));
        assert!(parse_expr("+")
            .unwrap_err()
            .to_string()
            .contains("expected expression"));
        assert!(parse_expr("(")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(parse_expr("(1")
            .unwrap_err()
            .to_string()
            .contains("expected ) after expression, found end of input"));
        assert!(parse_expr("(1 2")
            .unwrap_err()
            .to_string()
            .contains("expected ) after expression"));
        assert!(parse_expr("1 = 2")
            .unwrap_err()
            .to_string()
            .contains("invalid assignment target"));

        assert_eq!(
            parse_expr("")
                .unwrap_err()
                .downcast::<ParseErrors>()
                .unwrap()
                .into_iter()
                .count(),
            1
        );
        assert_eq!(
            parse_expr("😀;1😀")
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
        assert!(roundtrip_expr("nil"));
        assert!(roundtrip_expr("true"));
        assert!(roundtrip_expr("false"));
        assert!(roundtrip_expr("42"));
        assert!(roundtrip_expr(r#""test""#));
        assert!(roundtrip_expr("x"));

        assert!(matches!(parse_expr("nil"), Ok(Expr::Literal(Value::Nil))));
        assert!(matches!(
            parse_expr("true"),
            Ok(Expr::Literal(Value::Boolean(true)))
        ));
        assert!(matches!(
            parse_expr("false"),
            Ok(Expr::Literal(Value::Boolean(false)))
        ));
        assert!(matches!(
            parse_expr("42"),
            Ok(Expr::Literal(Value::Num(x))) if x == 42.0
        ));
        assert!(matches!(
            parse_expr(r#""test""#),
            Ok(Expr::Literal(Value::Str(s))) if s == "test"
        ));
        assert!(matches!(
            parse_expr("x"),
            Ok(Expr::Variable(tok)) if tok.lexeme == "x"
        ));
    }

    #[test]
    fn test_unary() {
        assert!(roundtrip_expr("-1"));
        assert!(roundtrip_expr("--2"));
        assert!(roundtrip_expr("!true"));
        assert!(roundtrip_expr("!!false"));

        match parse_expr("-1") {
            Ok(Expr::Unary(op, value)) => {
                assert_eq!(op.typ, TokenType::Minus);
                assert!(matches!(*value, Expr::Literal(Value::Num(x)) if x == 1.0));
            }
            _ => panic!(),
        }
        match parse_expr("!!true") {
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
        assert!(roundtrip_expr("1 * 2"));
        assert!(roundtrip_expr("3 / 4"));
        assert!(roundtrip_expr("1 * 2 / 3"));

        match parse_expr("1 * 2") {
            Ok(Expr::Binary(value1, op, value2)) => {
                assert_eq!(op.typ, TokenType::Star);
                assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
            }
            _ => panic!(),
        }

        match parse_expr("1 * 2 / 3") {
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
        assert!(roundtrip_expr("1 + 2"));
        assert!(roundtrip_expr("3 - 4"));
        assert!(roundtrip_expr("1 + 2 - 3"));

        match parse_expr("1 + 2") {
            Ok(Expr::Binary(value1, op, value2)) => {
                assert_eq!(op.typ, TokenType::Plus);
                assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
            }
            _ => panic!(),
        }

        match parse_expr("1 + 2 - 3") {
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
        assert!(roundtrip_expr("1 > 2"));
        assert!(roundtrip_expr("3 >= 4"));
        assert!(roundtrip_expr("1 < 2 <= 3"));

        match parse_expr("1 > 2") {
            Ok(Expr::Binary(value1, op, value2)) => {
                assert_eq!(op.typ, TokenType::Greater);
                assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
            }
            _ => panic!(),
        }

        match parse_expr("1 < 2 <= 3") {
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
        assert!(roundtrip_expr("1 == 2"));
        assert!(roundtrip_expr("3 != 4"));
        assert!(roundtrip_expr("1 == 2 != 3"));

        match parse_expr("1 == 2") {
            Ok(Expr::Binary(value1, op, value2)) => {
                assert_eq!(op.typ, TokenType::EqualEqual);
                assert!(matches!(*value1, Expr::Literal(Value::Num(x)) if x == 1.0));
                assert!(matches!(*value2, Expr::Literal(Value::Num(x)) if x == 2.0));
            }
            _ => panic!(),
        }

        match parse_expr("1 == 2 != 3") {
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
    fn test_assignment() {
        assert!(roundtrip_expr("x = 1"));
        assert!(roundtrip_expr("y = x + 1"));

        match parse_expr("x = 1") {
            Ok(Expr::Assignment(var, expr)) => {
                assert_eq!(var.typ, TokenType::Identifier);
                assert!(matches!(*expr, Expr::Literal(Value::Num(x)) if x == 1.0));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_grouping() {
        assert!(roundtrip_expr("(1)"));
        assert!(roundtrip_expr("(1 + 2) * 3"));
        assert!(roundtrip_expr("3 * (1 + 2)"));

        match parse_expr("(1)") {
            Ok(Expr::Grouping(value)) => {
                assert!(matches!(*value, Expr::Literal(Value::Num(x)) if x == 1.0));
            }
            _ => panic!(),
        }

        match parse_expr("3 * (1 + 2)") {
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
        assert!(roundtrip_expr("1 == 2 < 3 + 4 * -5"));

        match parse_expr("1 == 2 < 3 + 4 * -5") {
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

    #[test]
    fn test_statements() {
        assert!(roundtrip(""));
        assert!(parse("").unwrap().stmts.is_empty());
    }

    #[test]
    fn test_decl_stmt() {
        assert!(roundtrip("var x;"));
        assert!(roundtrip("var y = 42;"));

        match &parse("var x;").unwrap().stmts[0] {
            Stmt::Decl(tok, expr) => {
                assert_eq!(tok.typ, TokenType::Identifier);
                assert_eq!(tok.lexeme, "x");
                match expr {
                    Expr::Literal(value) => assert_eq!(*value, Value::Nil),
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }

        match &parse("var y = 42;").unwrap().stmts[0] {
            Stmt::Decl(tok, expr) => {
                assert_eq!(tok.typ, TokenType::Identifier);
                assert_eq!(tok.lexeme, "y");
                match expr {
                    Expr::Literal(value) => assert_eq!(*value, Value::Num(42.0)),
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_expr_stmt() {
        assert!(roundtrip("42;"));

        match &parse("42;").unwrap().stmts[0] {
            Stmt::Expr(expr) => match expr {
                Expr::Literal(value) => assert_eq!(*value, Value::Num(42.0)),
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn test_print_stmt() {
        assert!(roundtrip("print x;"));

        match &parse("print x;").unwrap().stmts[0] {
            Stmt::Print(expr) => match expr {
                Expr::Variable(tok) => assert_eq!(tok.lexeme, "x"),
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn test_stmt_block() {
        assert!(roundtrip("{\n}\n"));
        assert!(roundtrip("{\nvar x = 1;}\n"));

        match &parse("{ var x = 1; var y = 2; }").unwrap().stmts[0] {
            Stmt::Block(stmts) => {
                match &stmts[0] {
                    Stmt::Decl(tok, expr) => {
                        assert_eq!(tok.typ, TokenType::Identifier);
                        assert_eq!(tok.lexeme, "x");
                        match expr {
                            Expr::Literal(value) => assert_eq!(*value, Value::Num(1.0)),
                            _ => panic!(),
                        }
                    }
                    _ => panic!(),
                }
                match &stmts[1] {
                    Stmt::Decl(tok, expr) => {
                        assert_eq!(tok.typ, TokenType::Identifier);
                        assert_eq!(tok.lexeme, "y");
                        match expr {
                            Expr::Literal(value) => assert_eq!(*value, Value::Num(2.0)),
                            _ => panic!(),
                        }
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    fn parse(string: &str) -> Result<Program> {
        Parser::new(Box::new(Lexer::from_str(string))).parse()
    }

    fn roundtrip(string: &str) -> bool {
        format!("{}", parse(string).unwrap()) == string
    }

    fn parse_expr(string: &str) -> Result<Expr> {
        Parser::new(Box::new(Lexer::from_str(string))).parse_expr()
    }

    fn roundtrip_expr(string: &str) -> bool {
        format!("{}", parse_expr(string).unwrap()) == string
    }
}
