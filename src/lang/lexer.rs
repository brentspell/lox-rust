/*!
Lexical analyzer for the Lox language.

## Usage
```
use crate::lang::lexer::Lexer;

for result in Lexer::from_str(r#"print "Hell😎 W😎rld";"#) {
    match result {
        Ok(token) => println!("{}", token)
        Err(error) => println!("uh oh {}", error)
    }
}
```
*/

use std::collections::{HashMap, HashSet};

use anyhow::{anyhow, bail, Result};
use lazy_static::lazy_static;
use unicode_general_category as unicode_cat;
use unicode_normalization::UnicodeNormalization;

use crate::lang::{Token, TokenType, Value};
use crate::lang::reader::{CharReaderIterator, LookaheadReader};

lazy_static! {
    // lox language reserved words and associated token types
    static ref KEYWORD_TYPES: HashMap<&'static str, TokenType> = [
        ("and", TokenType::And),
        ("class", TokenType::Class),
        ("else", TokenType::Else),
        ("false", TokenType::False),
        ("for", TokenType::For),
        ("fun", TokenType::Fun),
        ("if", TokenType::If),
        ("nil", TokenType::Nil),
        ("or", TokenType::Or),
        ("print", TokenType::Print),
        ("return", TokenType::Return),
        ("super", TokenType::Super),
        ("this", TokenType::This),
        ("true", TokenType::True),
        ("var", TokenType::Var),
        ("while", TokenType::While),
    ]
    .iter()
    .copied()
    .collect();

    // unicode categories for identifier first character (unicode for [_A-Za-z])
    static ref IDENT_START_CATS: HashSet<unicode_cat::GeneralCategory> = [
        unicode_cat::GeneralCategory::LetterNumber,
        unicode_cat::GeneralCategory::LowercaseLetter,
        unicode_cat::GeneralCategory::ModifierLetter,
        unicode_cat::GeneralCategory::OtherLetter,
        unicode_cat::GeneralCategory::TitlecaseLetter,
        unicode_cat::GeneralCategory::UppercaseLetter,
    ]
    .iter()
    .copied()
    .collect();

    // unicode categories for subsequent identifier character (unicode for [_A-Za-z0-9])
    static ref IDENT_CONT_CATS: HashSet<unicode_cat::GeneralCategory> = [
        unicode_cat::GeneralCategory::ConnectorPunctuation,
        unicode_cat::GeneralCategory::DecimalNumber,
        unicode_cat::GeneralCategory::NonspacingMark,
        unicode_cat::GeneralCategory::SpacingMark,
    ]
    .iter()
    .chain(IDENT_START_CATS.iter())
    .copied()
    .collect();
}

/**
This struct maintains the current state of the analyzer as it progresses through the character
stream. We use the char_reader line for buffered character-oriented input, which can work with
any underlying store that supports Read, and avoids memory spikes for extremely long lines. The
lexer maintains an internal lookahead buffer for peeking at an arbitrary number of characters. We
also track the current line/column numbers for error reporting.

The lexer implements Iter, so tokens can be retrieved from it by simple iteration. Every token
is wrapped in a Result, so that scanning can continue even if there are lexical errors.
*/
pub struct Lexer {
    reader: LookaheadReader<char>,
    line: u32,
    column: u32,
}

impl Lexer {
    /**
    Creates a new lexer instance from a Lox language string.

    # Arguments
    * `text` - the text string to read

    # Returns
    The initialized lexer.
    */
    pub fn from_str(text: &str) -> Self {
        Self::from_read(Box::new(std::io::Cursor::new(text.to_string())))
    }

    /**
    Creates a new lexer to read from a byte stream.

    # Arguments
    * `read` - the IO reader trait to attach

    # Returns
    The initialized lexer.
    */
    pub fn from_read(read: Box<dyn std::io::Read>) -> Self {
        Self {
            reader: LookaheadReader::new(Box::new(CharReaderIterator::new(Box::new(read)))),
            line: 1,
            column: 0,
        }
    }

    fn scan_next(&mut self) -> Result<Option<Token>> {
        self.skip_space()?;
        if self.peek(0)?.is_some() {
            match self.scan_token() {
                Ok(t) => Ok(Some(t)),
                Err(e) => Err(anyhow!("line {}, col {}: {}", self.line, self.column, e)),
            }
        } else {
            Ok(None)
        }
    }

    fn skip_space(&mut self) -> Result<()> {
        while let Some(ch) = self.peek(0)? {
            match ch {
                // treat comments as whitespace
                '/' => match self.peek(1)? {
                    // match single-line comment, read until newline or EOF
                    Some('/') => {
                        while matches!(self.peek(0)?, Some(ch) if ch != '\n') {
                            self.read()?;
                        }
                    }
                    // match multiline comment, read until closed, error on unclosed
                    Some('*') => {
                        while self.read()? != '*' || self.peek(0)? != Some('/') {}
                        self.read()?;
                    }
                    _ => break,
                },
                // ignore whitespace characters
                ' ' | '\r' | '\t' | '\n' => {
                    self.read()?;
                }
                _ => break,
            }
        }
        Ok(())
    }

    fn scan_token(&mut self) -> Result<Token> {
        match self.peek(0)?.unwrap() {
            '(' => self.scan_char(TokenType::LeftParen),
            ')' => self.scan_char(TokenType::RightParen),
            '{' => self.scan_char(TokenType::LeftBrace),
            '}' => self.scan_char(TokenType::RightBrace),
            ',' => self.scan_char(TokenType::Comma),
            '.' => self.scan_char(TokenType::Dot),
            '-' => self.scan_char(TokenType::Minus),
            '+' => self.scan_char(TokenType::Plus),
            ';' => self.scan_char(TokenType::Semicolon),
            '*' => self.scan_char(TokenType::Star),
            '/' => self.scan_char(TokenType::Slash),
            '!' => self.scan_pair(TokenType::Bang, '=', TokenType::BangEqual),
            '=' => self.scan_pair(TokenType::Equal, '=', TokenType::EqualEqual),
            '<' => self.scan_pair(TokenType::Less, '=', TokenType::LessEqual),
            '>' => self.scan_pair(TokenType::Greater, '=', TokenType::GreaterEqual),
            '"' => self.scan_string(),
            d if d.is_digit(10) => self.scan_digit(),
            id if is_ident_start(id) => self.scan_keyword_ident(),
            _ => Err(anyhow!("unexpected character: {}", self.read()?)),
        }
    }

    fn scan_char(&mut self, typ: TokenType) -> Result<Token> {
        Ok(Token {
            typ,
            line: self.line,
            lexeme: self.read()?.to_string(),
            literal: Value::Nil,
        })
    }

    fn scan_pair(
        &mut self,
        lhs_typ: TokenType,
        rhs_char: char,
        rhs_typ: TokenType,
    ) -> Result<Token> {
        let lhs = self.read()?;
        if self.peek(0)? == Some(rhs_char) {
            Ok(Token {
                typ: rhs_typ,
                line: self.line,
                lexeme: [lhs, self.read()?].iter().collect(),
                literal: Value::Nil,
            })
        } else {
            Ok(Token {
                typ: lhs_typ,
                line: self.line,
                lexeme: lhs.to_string(),
                literal: Value::Nil,
            })
        }
    }

    fn scan_string(&mut self) -> Result<Token> {
        let line = self.line;
        let mut chars: Vec<char> = Vec::new();

        self.read()?;
        loop {
            match self.read()? {
                '"' => break,
                '\\' => chars.push(match self.read()? {
                    '\\' => '\\',
                    '"' => '"',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    ch => bail!("invalid string escape: \\{}", ch),
                }),
                ch => chars.push(ch),
            }
        }

        let value: String = chars.into_iter().collect();
        Ok(Token {
            typ: TokenType::String,
            line,
            lexeme: format!(r#""{}""#, value),
            literal: Value::Str(value),
        })
    }

    fn scan_digit(&mut self) -> Result<Token> {
        let mut chars: Vec<char> = Vec::new();

        // match leading digits
        while matches!(self.peek(0)?, Some(ch) if ch.is_digit(10)) {
            chars.push(self.read()?);
        }

        // match the optional separator and fractional part
        if self.peek(0)? == Some('.') {
            chars.push(self.read()?);
            while matches!(self.peek(0)?, Some(ch) if ch.is_digit(10)) {
                chars.push(self.read()?);
            }
        }

        let string: String = chars.into_iter().collect();
        Ok(Token {
            typ: TokenType::Number,
            line: self.line,
            lexeme: string.clone(),
            literal: Value::Num(string.parse()?),
        })
    }

    fn scan_keyword_ident(&mut self) -> Result<Token> {
        let mut chars: Vec<char> = Vec::new();

        // add any identifier continuation characters to the string
        while matches!(self.peek(0)?, Some(ch) if is_ident_cont(ch)) {
            chars.push(self.read()?);
        }

        // normalize the string and check to see if the identifier is keyword
        let ident: String = chars.into_iter().collect::<String>().nfkc().collect();
        if KEYWORD_TYPES.contains_key(ident.as_str()) {
            Ok(Token {
                typ: KEYWORD_TYPES[ident.as_str()],
                line: self.line,
                lexeme: ident,
                literal: Value::Nil,
            })
        } else {
            Ok(Token {
                typ: TokenType::Identifier,
                line: self.line,
                lexeme: ident,
                literal: Value::Nil,
            })
        }
    }

    fn read(&mut self) -> Result<char> {
        if let Some(ch) = self.reader.read()? {
            if ch == '\n' {
                self.line += 1;
                self.column = 0;
            } else {
                self.column += 1;
            }
            Ok(ch)
        } else {
            bail!("unexpected end of input")
        }
    }

    fn peek(&mut self, ahead: usize) -> Result<Option<char>> {
        self.reader.peek(ahead).map(|c| c.copied())
    }
}

impl Iterator for Lexer {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Result<Token>> {
        self.scan_next().transpose()
    }
}

fn is_ident_start(ch: char) -> bool {
    ch == '_' || IDENT_START_CATS.contains(&unicode_cat::get_general_category(ch))
}

fn is_ident_cont(ch: char) -> bool {
    ch == '_' || IDENT_CONT_CATS.contains(&unicode_cat::get_general_category(ch))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        assert_eq!(scan("").unwrap().len(), 0);
        assert_eq!(scan(" ").unwrap().len(), 0);
        assert_eq!(scan("\n").unwrap().len(), 0);
    }

    #[test]
    fn test_invalid() {
        assert!(scan("😀")
            .unwrap_err()
            .to_string()
            .contains("unexpected character"));
    }

    #[test]
    fn test_char_singles() {
        assert_eq!(scan("(").unwrap()[0].typ, TokenType::LeftParen);
        assert_eq!(scan(")").unwrap()[0].typ, TokenType::RightParen);
        assert_eq!(scan("{").unwrap()[0].typ, TokenType::LeftBrace);
        assert_eq!(scan("}").unwrap()[0].typ, TokenType::RightBrace);
        assert_eq!(scan(",").unwrap()[0].typ, TokenType::Comma);
        assert_eq!(scan(".").unwrap()[0].typ, TokenType::Dot);
        assert_eq!(scan("-").unwrap()[0].typ, TokenType::Minus);
        assert_eq!(scan("+").unwrap()[0].typ, TokenType::Plus);
        assert_eq!(scan(";").unwrap()[0].typ, TokenType::Semicolon);
        assert_eq!(scan("*").unwrap()[0].typ, TokenType::Star);
    }

    #[test]
    fn test_char_pairs() {
        assert_eq!(scan("!").unwrap()[0].typ, TokenType::Bang);
        assert_eq!(scan("=").unwrap()[0].typ, TokenType::Equal);
        assert_eq!(scan("!=").unwrap()[0].typ, TokenType::BangEqual);
        assert_eq!(scan("==").unwrap()[0].typ, TokenType::EqualEqual);
        assert_eq!(scan("<").unwrap()[0].typ, TokenType::Less);
        assert_eq!(scan("<=").unwrap()[0].typ, TokenType::LessEqual);
        assert_eq!(scan(">").unwrap()[0].typ, TokenType::Greater);
        assert_eq!(scan(">=").unwrap()[0].typ, TokenType::GreaterEqual);
        assert_eq!(scan("/").unwrap()[0].typ, TokenType::Slash);
    }

    #[test]
    fn test_comments() {
        assert_eq!(scan("//").unwrap().len(), 0);
        assert_eq!(scan("//a").unwrap().len(), 0);
        assert_eq!(scan("//ab").unwrap().len(), 0);
        assert_eq!(scan("//\n").unwrap().len(), 0);
        assert_eq!(scan(" \r\n\t").unwrap().len(), 0);

        assert_eq!(scan("/**/").unwrap().len(), 0);
        assert_eq!(scan("/*test*/").unwrap().len(), 0);
        assert_eq!(scan("/*test\ntest\n*/").unwrap().len(), 0);
        assert_eq!(scan("/***/").unwrap().len(), 0);
        assert_eq!(scan("/** /*/").unwrap().len(), 0);

        assert_eq!(scan("/ *").unwrap().len(), 2);
        assert_eq!(scan("/**/*/").unwrap().len(), 2);
        assert_eq!(scan("/*/**/*/").unwrap().len(), 2);
        assert!(scan("/*")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(scan("/**")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(scan("/** /")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
    }

    #[test]
    fn test_strings() {
        let token = &scan(r#""""#).unwrap()[0];
        assert_eq!(token.typ, TokenType::String);
        assert_eq!(token.line, 1);
        assert_eq!(token.lexeme, r#""""#);
        assert_eq!(token.literal, Value::Str("".to_string()));

        let token = &scan("\"test\ntest\n\"").unwrap()[0];
        assert_eq!(token.line, 1);
        assert_eq!(token.lexeme, "\"test\ntest\n\"");
        assert_eq!(token.literal, Value::Str("test\ntest\n".to_string()));

        assert_eq!(
            scan(r#""😀""#).unwrap()[0].literal,
            Value::Str("😀".to_string())
        );

        assert_eq!(
            scan(r#""\\""#).unwrap()[0].literal,
            Value::Str("\\".to_string())
        );
        assert_eq!(
            scan(r#""\"""#).unwrap()[0].literal,
            Value::Str("\"".to_string())
        );
        assert_eq!(
            scan(r#""\n""#).unwrap()[0].literal,
            Value::Str("\n".to_string())
        );
        assert_eq!(
            scan(r#""\r""#).unwrap()[0].literal,
            Value::Str("\r".to_string())
        );
        assert_eq!(
            scan(r#""\t""#).unwrap()[0].literal,
            Value::Str("\t".to_string())
        );

        assert!(scan(r#"""#)
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(scan(r#""test"#)
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(scan("\"test\n")
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(scan(r#""\"#)
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(scan(r#""\""#)
            .unwrap_err()
            .to_string()
            .contains("unexpected end of input"));
        assert!(scan(r#""\z""#)
            .unwrap_err()
            .to_string()
            .contains("invalid string escape"));
    }

    #[test]
    fn test_numbers() {
        let token = &scan("0").unwrap()[0];
        assert_eq!(token.typ, TokenType::Number);
        assert_eq!(token.line, 1);
        assert_eq!(token.lexeme, "0");
        assert_eq!(token.literal, Value::Num(0.0));

        assert_eq!(scan("1.5").unwrap()[0].literal, Value::Num(1.5));
    }

    #[test]
    fn test_keywords() {
        for (&kw, &typ) in KEYWORD_TYPES.iter() {
            let token = &scan(kw).unwrap()[0];
            assert_eq!(token.typ, typ);
            assert_eq!(token.line, 1);
            assert_eq!(token.lexeme, kw);
        }
    }

    #[test]
    fn test_identifiers() {
        let token = &scan("test").unwrap()[0];
        assert_eq!(token.typ, TokenType::Identifier);
        assert_eq!(token.line, 1);
        assert_eq!(token.lexeme, "test");

        assert_eq!(scan("__1").unwrap()[0].typ, TokenType::Identifier);
        assert_eq!(scan("test_").unwrap()[0].typ, TokenType::Identifier);
        assert_eq!(scan("π").unwrap()[0].typ, TokenType::Identifier);

        let token = &scan("a̐éö̲").unwrap()[0];
        assert_eq!(token.typ, TokenType::Identifier);
        assert_eq!(token.lexeme, "a̐éö̲".nfkc().collect::<String>());
    }

    #[test]
    fn test_line_numbers() {
        assert_eq!(scan("\ntest").unwrap()[0].line, 2);
        assert_eq!(scan("\n\ntest").unwrap()[0].line, 3);
        assert_eq!(scan("\"\n\"test").unwrap()[1].line, 2);
    }

    fn scan(text: &str) -> Result<Vec<Token>> {
        let mut results: Vec<Token> = Vec::new();
        for result in Lexer::from_str(text) {
            match result {
                Ok(token) => results.push(token),
                Err(error) => return Err(error),
            }
        }
        Ok(results)
    }
}
