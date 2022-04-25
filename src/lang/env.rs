/*!
# Lox block-scoped environment

This struct represents a stackable key/value mapping that can be used to represent an
environment in the Lox language. Names must be declared/initialized with `define` before being
used or assigned to. If values are not defined in the current environment, the get/assign request
is forwarded to the parent environment.
*/

use std::collections::HashMap;

use anyhow::{bail, Result};

use crate::lang::{Token, Value};

/**
This struct stores the values of all variables used by the interpreter. Scoping is accomplished
via the linked list of parent environments. The default environment contains no parent and
an empty mapping.
*/
#[derive(Debug, Default)]
pub struct Env {
    parent: Option<Box<Env>>,
    data: HashMap<String, Value>,
}

impl Env {
    /**
    Enters a new block scope, which contains a reference to the current scope as parent.
    */
    pub fn push(self) -> Self {
        Env {
            parent: Some(Box::new(self)),
            data: HashMap::new(),
        }
    }

    /**
    Exits the current block scope, returning the parent environment as the new scope.
    */
    pub fn pop(self) -> Option<Self> {
        self.parent.map(|p| *p)
    }

    /**
    Declares and initializes a new variable, replacing/shadowing any existing variable
    with the same name.

    # Arguments
    * `name` - the name of the new variable
    * `value` - the value to assign

    */
    pub fn define(&mut self, name: &str, value: Value) {
        self.data.insert(name.to_string(), value);
    }

    /**
    Retrieves the value of a variable. The variable must exist in the current or
    parent scope.

    # Arguments
    * `tok` - the token containing the name to retrieve

    # Returns
    The value of the requested variable, or error if it was not defined.
    */
    pub fn get(&self, tok: &Token) -> Result<&Value> {
        match self.data.get(&tok.lexeme) {
            Some(value) => Ok(value),
            None => match &self.parent {
                Some(parent) => Ok(parent.get(tok)?),
                None => bail!("line {}: undefined variable {}", tok.line, tok.lexeme),
            },
        }
    }

    /**
    Assigns the value of a variable. The variable must exist in the current or
    parent scope.

    # Arguments
    * `tok` - the token containing the name to retrieve
    * `value` - the value to assign to the variable

    # Returns
    Ok if the variable was assigned, or error if was not defined.
    */
    pub fn assign(&mut self, tok: &Token, value: Value) -> Result<()> {
        if self.data.contains_key(&tok.lexeme) {
            self.data.insert(tok.lexeme.to_string(), value);
            Ok(())
        } else {
            match &mut self.parent {
                Some(parent) => parent.assign(tok, value),
                None => bail!("line {}: undefined variable {}", tok.line, tok.lexeme),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::TokenType;

    use super::*;

    #[test]
    fn test_define_get_assign() {
        let mut env = Env::default();
        let x = Token {
            typ: TokenType::Identifier,
            line: 1,
            lexeme: "x".to_string(),
            literal: Value::Num(1.0),
        };
        let y = Token {
            typ: TokenType::Identifier,
            line: 1,
            lexeme: "y".to_string(),
            literal: Value::Num(2.0),
        };

        assert!(env
            .get(&x)
            .unwrap_err()
            .to_string()
            .contains("undefined variable"));
        assert!(env
            .assign(&x, Value::Num(2.0))
            .unwrap_err()
            .to_string()
            .contains("undefined variable"));

        env.define(&x.lexeme, x.literal.clone());
        env.define(&y.lexeme, y.literal.clone());
        assert_eq!(*env.get(&x).unwrap(), x.literal);
        assert_eq!(*env.get(&y).unwrap(), y.literal);

        env.assign(&x, y.literal.clone()).unwrap();
        assert_eq!(*env.get(&x).unwrap(), y.literal);
    }

    #[test]
    fn test_push_pop() {
        let mut env = Env::default();
        let x = Token {
            typ: TokenType::Identifier,
            line: 1,
            lexeme: "x".to_string(),
            literal: Value::Num(1.0),
        };
        let y = Token {
            typ: TokenType::Identifier,
            line: 1,
            lexeme: "y".to_string(),
            literal: Value::Num(2.0),
        };

        env.define(&x.lexeme, x.literal.clone());
        env.define(&y.lexeme, y.literal.clone());

        let mut env = env.push();
        env.define(&x.lexeme, y.literal.clone());
        env.assign(&y, x.literal.clone()).unwrap();
        assert_eq!(*env.get(&x).unwrap(), y.literal);
        assert_eq!(*env.get(&y).unwrap(), x.literal);

        let env = env.pop().unwrap();
        assert_eq!(*env.get(&x).unwrap(), x.literal);
        assert_eq!(*env.get(&y).unwrap(), x.literal);
    }
}
