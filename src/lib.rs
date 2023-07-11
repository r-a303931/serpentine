// serpentine/src/lib.rs: hub for serpentine, providing access to the vm,
// error, parser, and tokenizer
// Copyright (C) 2023 Andrew Rioux
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.

#![feature(assert_matches)]

use std::{
    fmt::{self, Display},
    sync::Arc,
};

#[derive(Debug)]
pub enum SerpentineError {
    Tokenize(tokenizer::TokenizerError),
    Parse(parser::ParseError),
    Runtime(vm::error::RuntimeError),
}

pub type SError = SerpentineError;

impl From<tokenizer::TokenizerError> for SerpentineError {
    fn from(e: tokenizer::TokenizerError) -> Self {
        Self::Tokenize(e)
    }
}

impl From<parser::ParseError> for SerpentineError {
    fn from(e: parser::ParseError) -> Self {
        Self::Parse(e)
    }
}

impl From<vm::error::RuntimeError> for SerpentineError {
    fn from(e: vm::error::RuntimeError) -> Self {
        Self::Runtime(e)
    }
}

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
            file: file.into(),
        }
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.col)
    }
}

#[macro_use]
pub mod parser;
pub mod tokenizer;
pub mod vm;
