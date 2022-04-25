/*!
# The Lox language interpreter

## Usage
```
use crate::lang::{lexer, parser, interp};

let lexer = lexer::Lexer::from_str(r"2 + 2 == 5");
let program = parser::Parser::new(Box::new(lexer)).parse()?;
let interpreter = interp::Interpreter::new();
let result = interpreter.eval(&program)?;
dbg!(result);
```

*/

use anyhow::{bail, Result};

use crate::lang::env::Env;
use crate::lang::{Expr, Program, Stmt, Token, TokenType as TT, Value, Value::*};

/**
This struct maintains the current state of the interpreter between program evaluations.
 */
pub struct Interpreter {
    env: Env,
}

impl Interpreter {
    /**
    Creates a new interpreter instance.

    # Returns
    The initialized interpreter.
    */
    pub fn new() -> Self {
        Self {
            env: Env::default(),
        }
    }

    /**
    Evaluates a parsed Lox program.

    # Arguments
    * `program` - the Lox program (sequence of statements) to evaluate

    # Returns
    The contents of stdout after the program was run.
    */
    pub fn eval(&mut self, program: &Program) -> Result<String> {
        self.eval_stmts(&program.stmts)
    }

    fn eval_stmts(&mut self, stmts: &[Stmt]) -> Result<String> {
        let mut stdout = String::new();

        for stmt in stmts.iter() {
            stdout.push_str(&self.eval_stmt(stmt)?);
        }

        Ok(stdout)
    }

    fn eval_stmt(&mut self, stmt: &Stmt) -> Result<String> {
        Ok(match stmt {
            Stmt::Block(stmts) => {
                // push a new child environment, eval, and then restore the old environment
                self.env = std::mem::take(&mut self.env).push();
                let stdout = self.eval_stmts(stmts);
                self.env = std::mem::take(&mut self.env).pop().unwrap();
                stdout?
            }
            Stmt::Decl(tok, expr) => {
                // define a new variable in the current environment
                let value = self.eval_expr(expr)?;
                self.env.define(&tok.lexeme, value);
                "".to_string()
            }
            Stmt::Expr(expr) => {
                // just evaluate for effects
                self.eval_expr(expr)?;
                "".to_string()
            }
            Stmt::Print(expr) => {
                // evaluate and write to stdout
                format!("{}\n", self.eval_expr(expr)?)
            }
        })
    }

    /**
    Evaluates a Lox expression.

    # Arguments
    * `expr` - parsed expression

    # Returns
    The result value of the evaluated expression.
    */
    pub fn eval_expr(&mut self, expr: &Expr) -> Result<Value> {
        Ok(match expr {
            Expr::Assignment(var, expr) => self.eval_assign(var, expr)?,
            Expr::Binary(lhs, tok, rhs) => self.eval_binary(lhs, tok, rhs)?,
            Expr::Grouping(expr) => self.eval_expr(expr)?,
            Expr::Literal(value) => value.clone(),
            Expr::Unary(tok, expr) => self.eval_unary(tok, expr)?,
            Expr::Variable(tok) => self.env.get(tok)?.clone(),
        })
    }

    fn eval_assign(&mut self, var: &Token, expr: &Expr) -> Result<Value> {
        let value = self.eval_expr(expr)?;
        self.env.assign(var, value.clone())?;
        Ok(value)
    }

    fn eval_binary(&mut self, lhs: &Expr, tok: &Token, rhs: &Expr) -> Result<Value> {
        let lhs = self.eval_expr(lhs)?;
        let rhs = self.eval_expr(rhs)?;
        Ok(match tok.typ {
            TT::Plus | TT::Slash | TT::Star | TT::Minus => self.eval_arithmetic(&lhs, tok, &rhs)?,
            TT::Greater | TT::GreaterEqual | TT::Less | TT::LessEqual => {
                self.eval_comparison(&lhs, tok, &rhs)?
            }
            TT::EqualEqual => Boolean(self.eval_equality(&lhs, &rhs)),
            TT::BangEqual => Boolean(!self.eval_equality(&lhs, &rhs)),
            typ => panic!("invalid binary: {}", typ),
        })
    }

    fn eval_unary(&mut self, tok: &Token, expr: &Expr) -> Result<Value> {
        let expr = self.eval_expr(expr)?;
        Ok(match tok.typ {
            TT::Bang => Boolean(!self.eval_truthy(&expr)),
            TT::Minus => match expr {
                Num(num) => Num(-num),
                value => bail!(
                    "line {}: expected number, found: {}{}",
                    tok.line,
                    tok.lexeme,
                    value
                ),
            },
            typ => panic!("invalid unary: {}", typ),
        })
    }

    fn eval_equality(&mut self, lhs: &Value, rhs: &Value) -> bool {
        match (lhs, rhs) {
            (Nil, Nil) => true,
            (Boolean(lhs), Boolean(rhs)) => lhs == rhs,
            (Num(lhs), Num(rhs)) => lhs == rhs,
            (Str(lhs), Str(rhs)) => lhs == rhs,
            _ => false,
        }
    }

    fn eval_comparison(&mut self, lhs: &Value, tok: &Token, rhs: &Value) -> Result<Value> {
        Ok(Boolean(match (lhs, tok.typ, rhs) {
            (Num(lhs), TT::Less, Num(rhs)) => lhs < rhs,
            (Num(lhs), TT::LessEqual, Num(rhs)) => lhs <= rhs,
            (Num(lhs), TT::Greater, Num(rhs)) => lhs > rhs,
            (Num(lhs), TT::GreaterEqual, Num(rhs)) => lhs >= rhs,
            (Str(lhs), TT::Less, Str(rhs)) => lhs < rhs,
            (Str(lhs), TT::LessEqual, Str(rhs)) => lhs <= rhs,
            (Str(lhs), TT::Greater, Str(rhs)) => lhs > rhs,
            (Str(lhs), TT::GreaterEqual, Str(rhs)) => lhs >= rhs,
            _ => bail!(
                "line {}: expected numbers or strings, found: {} {} {}",
                tok.line,
                lhs,
                tok.lexeme,
                rhs
            ),
        }))
    }

    fn eval_arithmetic(&mut self, lhs: &Value, tok: &Token, rhs: &Value) -> Result<Value> {
        Ok(match (lhs, tok.typ, rhs) {
            (Num(lhs), TT::Plus, Num(rhs)) => Num(lhs + rhs),
            (Num(lhs), TT::Minus, Num(rhs)) => Num(lhs - rhs),
            (Num(lhs), TT::Star, Num(rhs)) => Num(lhs * rhs),
            (Num(lhs), TT::Slash, Num(rhs)) => Num(lhs / rhs),
            (Str(lhs), TT::Plus, Str(rhs)) => Str(lhs.clone() + rhs),
            _ => bail!(
                "line {}: expected numbers, found: {} {} {}",
                tok.line,
                lhs,
                tok.lexeme,
                rhs
            ),
        })
    }

    fn eval_truthy(&mut self, value: &Value) -> bool {
        match value {
            Nil => false,
            Boolean(value) => *value,
            _ => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::lexer::Lexer;
    use crate::lang::parser::Parser;

    use super::*;

    #[test]
    fn test_errors() {
        assert!(eval_expr_str("😀")
            .unwrap_err()
            .to_string()
            .contains("unexpected character"));
        assert!(eval_str("😀")
            .unwrap_err()
            .to_string()
            .contains("unexpected character"));
        assert!(eval_expr_str("=")
            .unwrap_err()
            .to_string()
            .contains("expected expression"));
        assert!(eval_str("42")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
    }

    #[test]
    fn test_eval() {
        assert_eq!(eval_str("{}").unwrap(), "");
        assert_eq!(eval_str("42;").unwrap(), "");
        assert_eq!(eval_str("var x = 1;").unwrap(), "");

        let program = "
            var x = 1;
            x = x + 1;
            print x;
        ";
        assert_eq!(eval_str(program).unwrap(), "2\n");
    }

    #[test]
    fn test_block() {
        let program = "
            var x = 0;
            var y = 1;
            {
                var x = x + 1;
                {
                    y = x + 1;
                }
                print x;
                print y;
            }
            x = x + 1;
            print x;
            print y;
        ";
        assert_eq!(eval_str(program).unwrap(), "1\n2\n1\n2\n");
    }

    #[test]
    fn test_literal() {
        assert_eq!(eval_expr_str("nil").unwrap(), Nil);
        assert_eq!(eval_expr_str("true").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("false").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("42").unwrap(), Num(42.0));
        assert_eq!(eval_expr_str(r#""a""#).unwrap(), Str("a".to_string()));
    }

    #[test]
    fn test_grouping() {
        assert_eq!(eval_expr_str("(1 + 2) * 3").unwrap(), Num(9.0));
    }

    #[test]
    fn test_unary() {
        assert!(eval_expr_str("-true")
            .unwrap_err()
            .to_string()
            .contains("expected number"));

        assert_eq!(eval_expr_str("!false").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("!true").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("!nil").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("!1").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("!\"\"").unwrap(), Boolean(false));

        assert_eq!(eval_expr_str("-0").unwrap(), Num(0.0));
        assert_eq!(eval_expr_str("-1").unwrap(), Num(-1.0));
        assert_eq!(eval_expr_str("-2.5").unwrap(), Num(-2.5));
    }

    #[test]
    fn test_arithmetic() {
        assert!(eval_expr_str("nil + nil")
            .unwrap_err()
            .to_string()
            .contains("expected numbers"));
        assert!(eval_expr_str("1 + \"1\"")
            .unwrap_err()
            .to_string()
            .contains("expected numbers"));

        assert_eq!(eval_expr_str("1 + 1").unwrap(), Num(2.0));
        assert_eq!(eval_expr_str("2.5 - 1").unwrap(), Num(1.5));
        assert_eq!(eval_expr_str("3.1 * 2").unwrap(), Num(6.2));
        assert_eq!(eval_expr_str("5 / 2").unwrap(), Num(2.5));
        assert_eq!(eval_expr_str("1 / 0").unwrap(), Num(f64::INFINITY));

        assert_eq!(
            eval_expr_str(r#""a" + "b""#).unwrap(),
            Str("ab".to_string())
        );
    }

    #[test]
    fn test_comparison() {
        assert!(eval_expr_str("false < true")
            .unwrap_err()
            .to_string()
            .contains("expected numbers or strings"));

        assert_eq!(eval_expr_str("1 < 2").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("2 < 1").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("1 <= 1").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("1 <= 2").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("2 <= 1").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("1 > 2").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("2 > 1").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("1 >= 1").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("1 >= 2").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("2 >= 1").unwrap(), Boolean(true));

        assert_eq!(eval_expr_str(r#""a" < "b""#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""b" < "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#""a" <= "a""#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""a" <= "b""#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""a" > "b""#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#""b" > "a""#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""a" >= "a""#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""a" >= "b""#).unwrap(), Boolean(false));
    }

    #[test]
    fn test_equality() {
        assert_eq!(eval_expr_str("nil == nil").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("nil != nil").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("nil == true").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("nil != true").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("nil == 1").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("nil != 1").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#"nil == "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#"nil != "a""#).unwrap(), Boolean(true));

        assert_eq!(eval_expr_str("true == true").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("true != true").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("false == false").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("false != false").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("true == false").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("true != false").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("true == nil").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("true != nil").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("true == 1").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("true != 1").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#"true == "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#"true != "a""#).unwrap(), Boolean(true));

        assert_eq!(eval_expr_str("42 == 42.0").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("42 != 42.0").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("1 == 2").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("1 != 2").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("1 == nil").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("1 != nil").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("1 == true").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("1 != true").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#"1 == "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#"1 != "a""#).unwrap(), Boolean(true));

        assert_eq!(eval_expr_str(r#""a" == "a""#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""a" != "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#""a" == "b""#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#""a" != "b""#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""a" == nil"#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#""a" != nil"#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""true" == true"#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#""true" != true"#).unwrap(), Boolean(true));
        assert_eq!(eval_expr_str(r#""a" == 1"#).unwrap(), Boolean(false));
        assert_eq!(eval_expr_str(r#""a" != 1"#).unwrap(), Boolean(true));
    }

    fn eval_str(string: &str) -> Result<String> {
        Interpreter::new().eval(&Parser::new(Box::new(Lexer::from_str(string))).parse()?)
    }

    fn eval_expr_str(string: &str) -> Result<Value> {
        Interpreter::new().eval_expr(&Parser::new(Box::new(Lexer::from_str(string))).parse_expr()?)
    }
}
