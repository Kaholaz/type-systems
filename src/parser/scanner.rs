use std::rc::Rc;

use crate::parser::{ParserError, RESERVED_CHARACTERS};

#[derive(Clone)]
pub struct Scanner {
    input: Rc<[char]>,
    pos: usize,
    line_and_column: LineAndColumn,
}

impl Scanner {
    pub fn new(input: String) -> Self {
        Self {
            input: input.chars().collect::<Vec<_>>().into(),
            pos: 0,
            line_and_column: LineAndColumn::default(),
        }
    }

    pub fn skip_whitespace(&mut self) {
        while !self.is_at_end() {
            if self
                .current_char()
                .expect("we already checked this")
                .is_whitespace()
            {
                self.advance().expect("we already checked this");
            } else {
                return;
            }
        }
    }

    pub fn current_char(&self) -> Result<&char, ParserError> {
        self.input.get(self.pos).ok_or(ParserError {
            message: "unexpected EOF while scanning source".to_string(),
            span: self.line_and_column,
        })
    }

    pub fn advance(&mut self) -> Result<(), ParserError> {
        if *self.current_char()? == '\n' {
            self.line_and_column.new_line();
        } else {
            self.line_and_column.new_column();
        }
        self.pos += 1;
        Ok(())
    }

    pub fn advance_and_skip_whitespace(&mut self) -> Result<(), ParserError> {
        self.advance()?;
        self.skip_whitespace();
        Ok(())
    }

    pub fn is_at_end(&self) -> bool {
        self.pos >= self.input.len()
    }

    pub fn get_chars_until_whitespace(&mut self) -> String {
        let mut out = Vec::new();
        while !self.is_at_end()
            && !self
                .current_char()
                .expect("we already checked this")
                .is_whitespace()
            && !RESERVED_CHARACTERS.contains(self.current_char().expect("we already checked this"))
        {
            out.push(*self.current_char().expect("we already checked this"));
            self.advance().expect("we already checked this");
        }
        self.skip_whitespace();
        out.iter().collect()
    }

    pub fn expect_character(
        &mut self,
        character: char,
        error_message: String,
    ) -> Result<(), ParserError> {
        if *self.current_char()? != character {
            return Err(ParserError {
                message: error_message,
                span: self.line_and_column,
            });
        }

        self.advance()
    }

    pub fn line_and_column(&self) -> LineAndColumn {
        self.line_and_column
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineAndColumn {
    pub line: usize,
    pub column: usize,
}

impl LineAndColumn {
    pub fn new_column(&mut self) {
        self.column += 1;
    }

    pub fn new_line(&mut self) {
        self.column = 1;
        self.line += 1;
    }
}

impl Default for LineAndColumn {
    fn default() -> Self {
        Self { line: 1, column: 1 }
    }
}
