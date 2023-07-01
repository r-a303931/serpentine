// Copyright (C) 2023 Andrew Rioux
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

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
            file: file.into(),
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
