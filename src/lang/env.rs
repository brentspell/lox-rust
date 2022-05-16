/*!
# Lox block-scoped environment

This struct represents a stackable key/value mapping that can be used to represent an
environment in the Lox language. Names must be declared/initialized with `define` before being
used or assigned to. If values are not defined in the current environment, the get/assign request
is forwarded to the parent environment.
*/

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use anyhow::{bail, Result};

use crate::lang::{Token, Value};

/**
This struct stores the values of all variables used by the interpreter. Scoping is accomplished
via the linked list of parent environments. The default environment contains no parent and
an empty mapping.
*/
#[derive(Debug, Default)]
pub struct Env {
    parent: Option<Arc<Mutex<Env>>>,
    data: HashMap<String, Value>,
}

impl Env {
    /**
    Enters a new block scope, which contains a reference to the current scope as parent.
    */
    pub fn push(env: &Arc<Mutex<Self>>) -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self {
            parent: Some(env.clone()),
            data: HashMap::new(),
        }))
    }

    /**
    Exits the current block scope, returning the parent environment as the new scope.
    */
    pub fn pop(env: &Arc<Mutex<Self>>) -> Option<Arc<Mutex<Self>>> {
        env.lock().unwrap().parent.clone()
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
    pub fn get(&self, tok: &Token, qname: &str) -> Result<Value> {
        match self.data.get(qname) {
            Some(value) => Ok(value.clone()),
            None => match &self.parent {
                Some(parent) => Ok(parent.lock().unwrap().get(tok, qname)?),
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
    pub fn assign(&mut self, tok: &Token, qname: &str, value: Value) -> Result<()> {
        if self.data.contains_key(qname) {
            self.data.insert(qname.to_string(), value);
            Ok(())
        } else {
            match &self.parent {
                Some(parent) => parent.lock().unwrap().assign(tok, qname, value),
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
            .get(&x, &x.lexeme)
            .unwrap_err()
            .to_string()
            .contains("undefined variable"));
        assert!(env
            .assign(&x, &x.lexeme, Value::Num(2.0))
            .unwrap_err()
            .to_string()
            .contains("undefined variable"));

        env.define(&x.lexeme, x.literal.clone());
        env.define(&y.lexeme, y.literal.clone());
        assert_eq!(env.get(&x, &x.lexeme).unwrap(), x.literal);
        assert_eq!(env.get(&y, &y.lexeme).unwrap(), y.literal);

        env.assign(&x, &x.lexeme, y.literal.clone()).unwrap();
        assert_eq!(env.get(&x, &x.lexeme).unwrap(), y.literal);
    }

    #[test]
    fn test_push_pop() {
        let env = Arc::new(Mutex::new(Env::default()));
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

        env.lock().unwrap().define(&x.lexeme, x.literal.clone());
        env.lock().unwrap().define(&y.lexeme, y.literal.clone());

        let env = Env::push(&env);
        env.lock().unwrap().define(&x.lexeme, y.literal.clone());
        env.lock()
            .unwrap()
            .assign(&y, &y.lexeme, x.literal.clone())
            .unwrap();
        assert_eq!(env.lock().unwrap().get(&x, &x.lexeme).unwrap(), y.literal);
        assert_eq!(env.lock().unwrap().get(&y, &y.lexeme).unwrap(), x.literal);

        let env = Env::pop(&env).unwrap();
        assert_eq!(env.lock().unwrap().get(&x, &x.lexeme).unwrap(), x.literal);
        assert_eq!(env.lock().unwrap().get(&y, &y.lexeme).unwrap(), x.literal);
    }
}
