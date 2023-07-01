#![feature(assert_matches)]

use std::{
    fmt::{self, Display},
    sync::Arc,
};

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Position {
    line: usize,
    col: usize,
    file: Arc<str>,
}

impl Position {
    pub fn line(&self) -> usize {
        self.line
    }

    pub fn col(&self) -> usize {
        self.col
    }

    pub fn file(&self) -> &str {
        &self.file
    }

    pub fn file_clone(&self) -> Arc<str> {
        Arc::clone(&self.file)
    }

    pub fn new<IS: Into<Arc<str>>>(file: IS, line: usize, col: usize) -> Self {
        Self {
            line,
            col,
            file: file.into()
        }
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.col)
    }
}

pub mod parser;
pub mod tokenizer;
pub mod vm;
