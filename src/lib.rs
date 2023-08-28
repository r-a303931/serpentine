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
    path::Path,
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

#[non_exhaustive]
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum PositionSource {
    File(Arc<Path>),
    Repl,
    Test,
}

impl std::fmt::Display for PositionSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::File(p) => write!(f, "{:?}", p),
            Self::Repl => write!(f, "<repl>"),
            Self::Test => write!(f, "<test>"),
        }
    }
}

impl<IS: Into<Arc<Path>>> From<IS> for PositionSource {
    fn from(value: IS) -> Self {
        Self::File(value.into())
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Position {
    line: usize,
    col: usize,
    source: PositionSource,
}

impl Position {
    pub fn line(&self) -> usize {
        self.line
    }

    pub fn col(&self) -> usize {
        self.col
    }

    pub fn file(&self) -> &PositionSource {
        &self.source
    }

    pub fn new<IS: Into<PositionSource>>(source: IS, line: usize, col: usize) -> Self {
        Self {
            line,
            col,
            source: source.into(),
        }
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}:{}", self.source, self.line, self.col)
    }
}

#[macro_use]
pub mod parser;
pub mod stdlib;
pub mod tokenizer;
pub mod vm;
