/*!
# The Lox language interpreter

## Usage
```
use crate::lang::{lexer, parser, interp};

let lexer = lexer::Lexer::from_str(r"2 + 2 == 5");
let program = parser::Parser::new(lexer).parse()?;
let interpreter = interp::Interpreter::new();
let result = interpreter.eval(&program)?;
dbg!(result);
```

*/

use std::sync::{Arc, Mutex};

use anyhow::{bail, Result};

use crate::lang::env::Env;
use crate::lang::{Expr, Program, Stmt, Token, TokenType as TT, Value, Value::*};

/**
This struct maintains the current state of the interpreter between program evaluations.
 */
pub struct Interpreter {
    env: Arc<Mutex<Env>>,
    breaking: Option<bool>,
    retval: Option<Value>,
    printer: Box<dyn FnMut(&str) + Send + Sync>,
}

impl Interpreter {
    /**
    Creates a new interpreter instance.

    # Returns
    The initialized interpreter.
    */
    pub fn new(printer: impl FnMut(&str) + Send + Sync + 'static) -> Self {
        Self {
            env: Arc::new(Mutex::new(Env::default())),
            breaking: None,
            retval: None,
            printer: Box::new(printer),
        }
    }

    /**
    Evaluates a parsed Lox program.

    # Arguments
    * `program` - the Lox program (sequence of statements) to evaluate

    # Returns
    The contents of stdout after the program was run.
    */
    pub fn eval(&mut self, program: &Program) -> Result<()> {
        self.eval_stmts(&program.stmts)
    }

    fn eval_stmts(&mut self, stmts: &[Stmt]) -> Result<()> {
        for stmt in stmts.iter() {
            self.eval_stmt(stmt)?;
            if self.breaking.is_some() || self.retval.is_some() {
                break;
            }
        }

        Ok(())
    }

    fn eval_stmt(&mut self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Block(stmts) => self.eval_block(stmts),
            Stmt::Break(cont) => self.eval_break(*cont),
            Stmt::Var(tok, expr) => self.eval_var(tok, expr),
            Stmt::Fun(name, _params, _body) => self.eval_fun(name, stmt),
            Stmt::Expr(expr) => self.eval_expr(expr).map(|_| ()),
            Stmt::If(cond, cons, alt) => self.eval_if(cond, cons, alt),
            Stmt::Print(expr) => self.eval_print(expr),
            Stmt::While(cond, body, post) => self.eval_while(cond, body, post),
            Stmt::Return(_tok, value) => self.eval_return(value),
        }
    }

    fn eval_block(&mut self, stmts: &[Stmt]) -> Result<()> {
        self.env = Env::push(&self.env);
        let result = self.eval_stmts(stmts);
        self.env = Env::pop(&self.env).unwrap();
        result
    }

    fn eval_break(&mut self, cont: bool) -> Result<()> {
        self.breaking = Some(cont);
        Ok(())
    }

    fn eval_var(&mut self, tok: &Token, expr: &Expr) -> Result<()> {
        let value = self.eval_expr(expr)?;
        self.env.lock().unwrap().define(&tok.lexeme, value);
        Ok(())
    }

    fn eval_fun(&mut self, name: &Token, stmt: &Stmt) -> Result<()> {
        let value = Value::Fun(Box::new(stmt.clone()), self.env.clone());
        self.env.lock().unwrap().define(&name.lexeme, value);
        Ok(())
    }

    fn eval_if(&mut self, cond: &Expr, cons: &Stmt, alt: &Option<Box<Stmt>>) -> Result<()> {
        let cond = self.eval_expr(cond)?;
        if self.eval_truthy(&cond) {
            self.eval_stmt(cons)?;
        } else if let Some(alt) = alt {
            self.eval_stmt(alt)?;
        }
        Ok(())
    }

    fn eval_print(&mut self, expr: &Expr) -> Result<()> {
        let value = self.eval_expr(expr)?;
        let value = value;
        let stdout = match value {
            Value::Str(string) => format!("{}\n", string),
            value => format!("{}\n", value),
        };
        (self.printer)(&stdout);
        Ok(())
    }

    fn eval_while(&mut self, cond: &Expr, body: &Stmt, post: &Option<Box<Stmt>>) -> Result<()> {
        loop {
            // evaluate the loop condition
            let cond = self.eval_expr(cond)?;
            if !self.eval_truthy(&cond) {
                break;
            }

            // evaluate the loop body
            self.eval_stmt(body)?;

            // if we are breaking (not continuing), bail out
            if let Some(false) = std::mem::replace(&mut self.breaking, None) {
                break;
            }

            // evaluate the optional loop post-processing (for continue inside for-loop)
            if let Some(post) = post {
                self.eval_stmt(post)?;
            }
        }

        Ok(())
    }

    fn eval_return(&mut self, expr: &Expr) -> Result<()> {
        self.retval = Some(self.eval_expr(expr)?);
        Ok(())
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
            Expr::Call(callee, tok, args) => self.eval_call(callee, tok, args)?,
            Expr::Grouping(expr) => self.eval_expr(expr)?,
            Expr::Literal(value) => value.clone(),
            Expr::Logical(lhs, tok, rhs) => self.eval_logical(lhs, tok, rhs)?,
            Expr::Unary(tok, expr) => self.eval_unary(tok, expr)?,
            Expr::Variable(tok) => self.env.lock().unwrap().get(tok)?,
        })
    }

    fn eval_assign(&mut self, var: &Token, expr: &Expr) -> Result<Value> {
        let value = self.eval_expr(expr)?;
        self.env.lock().unwrap().assign(var, value.clone())?;
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

    fn eval_logical(&mut self, lhs: &Expr, tok: &Token, rhs: &Expr) -> Result<Value> {
        let lhs = self.eval_expr(lhs)?;
        let lhb = self.eval_truthy(&lhs);
        Ok(match (lhb, tok.typ) {
            (true, TT::Or) => lhs,
            (false, TT::And) => lhs,
            (_, TT::Or | TT::And) => self.eval_expr(rhs)?,
            (_, typ) => panic!("invalid logical: {}", typ),
        })
    }

    fn eval_unary(&mut self, tok: &Token, expr: &Expr) -> Result<Value> {
        let value = self.eval_expr(expr)?;
        Ok(match tok.typ {
            TT::Bang => Boolean(!self.eval_truthy(&value)),
            TT::Minus => match value {
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

    fn eval_call(&mut self, callee: &Expr, tok: &Token, args: &[Expr]) -> Result<Value> {
        let callee = self.eval_expr(callee)?;
        match callee {
            Value::Fun(stmt, env) => {
                let env = Env::push(&env);
                match *stmt {
                    Stmt::Fun(name, params, body) => {
                        if args.len() != params.len() {
                            bail!(
                                "line {}: in call to {}, expected {} arguments, found {}",
                                tok.line,
                                name.lexeme,
                                params.len(),
                                args.len()
                            );
                        }

                        for (p, a) in params.iter().zip(args.iter()) {
                            env.lock().unwrap().define(&p.lexeme, self.eval_expr(a)?);
                        }

                        let env = std::mem::replace(&mut self.env, env);
                        let result = self.eval_stmt(&body);
                        self.env = env;
                        let value = self.retval.take();
                        result.and(Ok(value.unwrap_or(Value::Nil)))
                    }
                    _ => panic!("invalid function statement"),
                }
            }
            _ => bail!("line {}: expected callable (function or class)", tok.line),
        }
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
    fn test_if() {
        assert_eq!(eval_str(r#"if (false) print "cons";"#).unwrap(), "");
        assert_eq!(eval_str(r#"if (true) print "cons";"#).unwrap(), "cons\n");
        assert_eq!(
            eval_str(r#"if (false) print "cons"; else print "alt";"#).unwrap(),
            "alt\n"
        );
        assert_eq!(eval_str(r#"if (nil) print "cons";"#).unwrap(), "");
        assert_eq!(eval_str(r#"if (42) print "cons";"#).unwrap(), "cons\n");
        assert_eq!(eval_str(r#"if ("a") print "cons";"#).unwrap(), "cons\n");
    }

    #[test]
    fn test_while() {
        assert_eq!(eval_str(r#"while (false) print "wrong";"#).unwrap(), "");

        let program = "
            var x = 0;
            while (x < 10) {
                print x;
                x = x + 1;
            }
        ";
        assert_eq!(eval_str(program).unwrap(), "0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n");

        let program = "
            for (var x = 0; x < 10; x = x + 1)
                print x;
        ";
        assert_eq!(eval_str(program).unwrap(), "0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n");
    }

    #[test]
    fn test_break() {
        let program = "
            for (var x = 0; x < 10; x = x + 1) {
                if (x == 2)
                    break;
                print x;
            }
        ";
        assert_eq!(eval_str(program).unwrap(), "0\n1\n");

        let program = "
            for (var x = 0; x < 10; x = x + 1) {
                if (x == 2)
                    break;
                print x;
                for (var y = 0; y < 10; y = y + 1) {
                    if (y == 2)
                        break;
                    print y;
                }
            }
        ";
        assert_eq!(eval_str(program).unwrap(), "0\n0\n1\n1\n0\n1\n");

        let program = "
            for (var x = 0; x < 10; x = x + 1) {
                print x;
                if (x > 0)
                    continue;
                print x;
            }
        ";
        assert_eq!(
            eval_str(program).unwrap(),
            "0\n0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n"
        );
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
    fn test_logical() {
        assert_eq!(eval_expr_str("false or false").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("false or true").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("true or false").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("true or true").unwrap(), Boolean(true));

        assert_eq!(eval_expr_str("false and false").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("false and true").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("true and false").unwrap(), Boolean(false));
        assert_eq!(eval_expr_str("true and true").unwrap(), Boolean(true));

        assert_eq!(eval_expr_str("true or (true + 1)").unwrap(), Boolean(true));
        assert_eq!(eval_expr_str("1 or false").unwrap(), Num(1.0));

        assert_eq!(
            eval_expr_str("false and (true + 1)").unwrap(),
            Boolean(false)
        );
        assert_eq!(eval_expr_str("true and 1").unwrap(), Num(1.0));

        assert_eq!(
            eval_expr_str("false and true or true").unwrap(),
            Boolean(true)
        );
        assert_eq!(
            eval_expr_str("true or true and false").unwrap(),
            Boolean(true)
        );
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
        let s = Arc::new(Mutex::new("".to_string()));
        let r = s.clone();

        Interpreter::new(move |t: &str| {
            s.lock().unwrap().push_str(t);
        })
        .eval(&Parser::new(Lexer::from_str(string)).parse()?)?;

        let r = r.lock().unwrap().clone();
        Ok(r)
    }

    fn eval_expr_str(string: &str) -> Result<Value> {
        Ok(Interpreter::new(|_| {})
            .eval_expr(&Parser::new(Lexer::from_str(string)).parse_expr()?)?)
    }
}
