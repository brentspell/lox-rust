/*!
# The Lox language interpreter

## Usage
```
use crate::lang::{lexer, parser, interp};

let lexer = lexer::Lexer::from_str(r"2 + 2 == 5");
let expr = parser::Parser::new(Box::new(lexer)).parse()?;
let result = interp::eval(&expr)?;
dbg!(result);
```

*/

use anyhow::{bail, Result};

use crate::lang::{Expr, Token, TokenType as TT, Value, Value::*};

/**
Evaluates a Lox expression.

# Arguments
* `expr` - parsed expression

# Returns
The result value of the evaluated expression.
*/
pub fn eval(expr: &Expr) -> Result<Value> {
    Ok(match expr {
        Expr::Binary(lhs, tok, rhs) => eval_binary(lhs, tok, rhs)?,
        Expr::Grouping(expr) => eval(expr)?,
        Expr::Literal(value) => value.clone(),
        Expr::Unary(tok, expr) => eval_unary(tok, expr)?,
    })
}

fn eval_binary(lhs: &Expr, tok: &Token, rhs: &Expr) -> Result<Value> {
    let lhs = eval(lhs)?;
    let rhs = eval(rhs)?;
    Ok(match tok.typ {
        TT::Plus | TT::Slash | TT::Star | TT::Minus => eval_arithmetic(&lhs, tok, &rhs)?,
        TT::Greater | TT::GreaterEqual | TT::Less | TT::LessEqual => {
            eval_comparison(&lhs, tok, &rhs)?
        }
        TT::EqualEqual => Boolean(eval_equality(&lhs, &rhs)),
        TT::BangEqual => Boolean(!eval_equality(&lhs, &rhs)),
        typ => panic!("invalid binary: {}", typ),
    })
}

fn eval_unary(tok: &Token, expr: &Expr) -> Result<Value> {
    let expr = eval(expr)?;
    Ok(match tok.typ {
        TT::Bang => Boolean(!eval_truthy(&expr)),
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

fn eval_equality(lhs: &Value, rhs: &Value) -> bool {
    match (lhs, rhs) {
        (Nil, Nil) => true,
        (Boolean(lhs), Boolean(rhs)) => lhs == rhs,
        (Num(lhs), Num(rhs)) => lhs == rhs,
        (Str(lhs), Str(rhs)) => lhs == rhs,
        _ => false,
    }
}

fn eval_comparison(lhs: &Value, tok: &Token, rhs: &Value) -> Result<Value> {
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

fn eval_arithmetic(lhs: &Value, tok: &Token, rhs: &Value) -> Result<Value> {
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

fn eval_truthy(value: &Value) -> bool {
    match value {
        Nil => false,
        Boolean(value) => *value,
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::lexer::Lexer;
    use crate::lang::parser::Parser;

    use super::*;

    #[test]
    fn test_errors() {
        assert!(eval_str("😀")
            .unwrap_err()
            .to_string()
            .contains("unexpected character"));
        assert!(eval_str("=")
            .unwrap_err()
            .to_string()
            .contains("expected literal or ("));
    }

    #[test]
    fn test_literal() {
        assert_eq!(eval_str("nil").unwrap(), Nil);
        assert_eq!(eval_str("true").unwrap(), Boolean(true));
        assert_eq!(eval_str("false").unwrap(), Boolean(false));
        assert_eq!(eval_str("42").unwrap(), Num(42.0));
        assert_eq!(eval_str(r#""a""#).unwrap(), Str("a".to_string()));
    }

    #[test]
    fn test_grouping() {
        assert_eq!(eval_str("(1 + 2) * 3").unwrap(), Num(9.0));
    }

    #[test]
    fn test_unary() {
        assert!(eval_str("-true")
            .unwrap_err()
            .to_string()
            .contains("expected number"));

        assert_eq!(eval_str("!false").unwrap(), Boolean(true));
        assert_eq!(eval_str("!true").unwrap(), Boolean(false));
        assert_eq!(eval_str("!nil").unwrap(), Boolean(true));
        assert_eq!(eval_str("!1").unwrap(), Boolean(false));
        assert_eq!(eval_str("!\"\"").unwrap(), Boolean(false));

        assert_eq!(eval_str("-0").unwrap(), Num(0.0));
        assert_eq!(eval_str("-1").unwrap(), Num(-1.0));
        assert_eq!(eval_str("-2.5").unwrap(), Num(-2.5));
    }

    #[test]
    fn test_arithmetic() {
        assert!(eval_str("nil + nil")
            .unwrap_err()
            .to_string()
            .contains("expected numbers"));
        assert!(eval_str("1 + \"1\"")
            .unwrap_err()
            .to_string()
            .contains("expected numbers"));

        assert_eq!(eval_str("1 + 1").unwrap(), Num(2.0));
        assert_eq!(eval_str("2.5 - 1").unwrap(), Num(1.5));
        assert_eq!(eval_str("3.1 * 2").unwrap(), Num(6.2));
        assert_eq!(eval_str("5 / 2").unwrap(), Num(2.5));
        assert_eq!(eval_str("1 / 0").unwrap(), Num(f64::INFINITY));

        assert_eq!(eval_str(r#""a" + "b""#).unwrap(), Str("ab".to_string()));
    }

    #[test]
    fn test_comparison() {
        assert!(eval_str("false < true")
            .unwrap_err()
            .to_string()
            .contains("expected numbers or strings"));

        assert_eq!(eval_str("1 < 2").unwrap(), Boolean(true));
        assert_eq!(eval_str("2 < 1").unwrap(), Boolean(false));
        assert_eq!(eval_str("1 <= 1").unwrap(), Boolean(true));
        assert_eq!(eval_str("1 <= 2").unwrap(), Boolean(true));
        assert_eq!(eval_str("2 <= 1").unwrap(), Boolean(false));
        assert_eq!(eval_str("1 > 2").unwrap(), Boolean(false));
        assert_eq!(eval_str("2 > 1").unwrap(), Boolean(true));
        assert_eq!(eval_str("1 >= 1").unwrap(), Boolean(true));
        assert_eq!(eval_str("1 >= 2").unwrap(), Boolean(false));
        assert_eq!(eval_str("2 >= 1").unwrap(), Boolean(true));

        assert_eq!(eval_str(r#""a" < "b""#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""b" < "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#""a" <= "a""#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""a" <= "b""#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""a" > "b""#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#""b" > "a""#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""a" >= "a""#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""a" >= "b""#).unwrap(), Boolean(false));
    }

    #[test]
    fn test_equality() {
        assert_eq!(eval_str("nil == nil").unwrap(), Boolean(true));
        assert_eq!(eval_str("nil != nil").unwrap(), Boolean(false));
        assert_eq!(eval_str("nil == true").unwrap(), Boolean(false));
        assert_eq!(eval_str("nil != true").unwrap(), Boolean(true));
        assert_eq!(eval_str("nil == 1").unwrap(), Boolean(false));
        assert_eq!(eval_str("nil != 1").unwrap(), Boolean(true));
        assert_eq!(eval_str(r#"nil == "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#"nil != "a""#).unwrap(), Boolean(true));

        assert_eq!(eval_str("true == true").unwrap(), Boolean(true));
        assert_eq!(eval_str("true != true").unwrap(), Boolean(false));
        assert_eq!(eval_str("false == false").unwrap(), Boolean(true));
        assert_eq!(eval_str("false != false").unwrap(), Boolean(false));
        assert_eq!(eval_str("true == false").unwrap(), Boolean(false));
        assert_eq!(eval_str("true != false").unwrap(), Boolean(true));
        assert_eq!(eval_str("true == nil").unwrap(), Boolean(false));
        assert_eq!(eval_str("true != nil").unwrap(), Boolean(true));
        assert_eq!(eval_str("true == 1").unwrap(), Boolean(false));
        assert_eq!(eval_str("true != 1").unwrap(), Boolean(true));
        assert_eq!(eval_str(r#"true == "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#"true != "a""#).unwrap(), Boolean(true));

        assert_eq!(eval_str("42 == 42.0").unwrap(), Boolean(true));
        assert_eq!(eval_str("42 != 42.0").unwrap(), Boolean(false));
        assert_eq!(eval_str("1 == 2").unwrap(), Boolean(false));
        assert_eq!(eval_str("1 != 2").unwrap(), Boolean(true));
        assert_eq!(eval_str("1 == nil").unwrap(), Boolean(false));
        assert_eq!(eval_str("1 != nil").unwrap(), Boolean(true));
        assert_eq!(eval_str("1 == true").unwrap(), Boolean(false));
        assert_eq!(eval_str("1 != true").unwrap(), Boolean(true));
        assert_eq!(eval_str(r#"1 == "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#"1 != "a""#).unwrap(), Boolean(true));

        assert_eq!(eval_str(r#""a" == "a""#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""a" != "a""#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#""a" == "b""#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#""a" != "b""#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""a" == nil"#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#""a" != nil"#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""true" == true"#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#""true" != true"#).unwrap(), Boolean(true));
        assert_eq!(eval_str(r#""a" == 1"#).unwrap(), Boolean(false));
        assert_eq!(eval_str(r#""a" != 1"#).unwrap(), Boolean(true));
    }

    fn eval_str(string: &str) -> Result<Value> {
        eval(&Parser::new(Box::new(Lexer::from_str(string))).parse_all()?)
    }
}
