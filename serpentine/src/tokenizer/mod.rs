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

use std::sync::Arc;

use crate::Position;

#[derive(Debug, PartialEq, Eq)]
pub struct TokenizerError {
    pub position: Position,
    pub message: String,
}

pub struct InputFile {
    pub name: String,
    pub contents: Vec<char>,
}

fn next_line(pos: &mut Position) {
    pos.line += 1;
    pos.col = 0;
}

fn next_col(pos: &mut Position) {
    pos.col += 1;
}

fn move_cols(pos: &mut Position, count: usize) {
    pos.col += count;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenType<'a> {
    RightParen,
    LeftParen,
    QuoteParen,
    QuoteSymbol(&'a [char]),
    BackquoteParen,
    UnquoteSymbol(&'a [char]),
    UnquoteExprParen,
    ListSpliceSymbol(&'a [char]),
    ListSpliceParen,
    String(&'a [char]),
    Symbol(&'a [char]),
    FuncSymbol(&'a [char]),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token<'a> {
    pub position: Position,
    pub ttype: TokenType<'a>,
}

fn symbol_end(ch: char) -> bool {
    "() \t\r\n,`@".contains(ch)
}

fn to_symbol_end(ptr: &[char]) -> (&[char], &[char]) {
    let mut count = 1;

    loop {
        if count >= ptr.len() || symbol_end(ptr[count]) {
            return (&ptr[..count], &ptr[count..]);
        }

        count += 1;
    }
}

fn to_string_end(ptr: &[char]) -> Option<(&[char], &[char])> {
    let mut count = 1;

    loop {
        if count >= ptr.len() {
            return None;
        }

        if ptr[count] == '\\' {
            count += 2;
            continue;
        }

        if ptr[count] == '"' {
            return Some((&ptr[..count], &ptr[(count + 1)..]));
        }

        count += 1;
    }
}

pub fn tokenize(input: &InputFile) -> Result<Vec<Token<'_>>, TokenizerError> {
    let mut return_value = vec![];
    let mut content_ptr = &*input.contents;
    let mut current_position = Position {
        file: Arc::from(input.name.to_owned()),
        line: 1,
        col: 0,
    };

    macro_rules! simple_push {
        ($token:tt, $count:expr) => {{
            return_value.push(Token {
                position: current_position.clone(),
                ttype: TokenType::$token,
            });
            move_cols(&mut current_position, $count);
            content_ptr = &content_ptr[$count..];
        }};
    }

    macro_rules! token_err {
        ($err:expr) => {
            return Err(TokenizerError {
                position: current_position.clone(),
                message: $err.to_string(),
            })
        };
    }

    macro_rules! token_error {
        ($err:expr) => {
            return Err(TokenizerError {
                position: current_position.clone(),
                message: $err,
            })
        };
    }

    while let Some(first_char) = content_ptr.first() {
        match first_char {
            ';' => {
                while let Some(first_char) = content_ptr.first() {
                    if *first_char == '\n' {
                        break;
                    }

                    content_ptr = &content_ptr[1..];
                }
            }
            ')' => simple_push!(RightParen, 1),
            '(' => simple_push!(LeftParen, 1),
            '\r' => {
                content_ptr = &content_ptr[1..];
            }
            '\n' => {
                next_line(&mut current_position);
                content_ptr = &content_ptr[1..];
            }
            ' ' | '\t' => {
                next_col(&mut current_position);
                content_ptr = &content_ptr[1..];
            }
            '\'' if content_ptr.len() >= 2 => match content_ptr[1] {
                '(' => simple_push!(QuoteParen, 2),
                c if symbol_end(c) => token_err!("unexpected end of symbol"),
                _ => {
                    let (symbol, new_content_ptr) = to_symbol_end(&content_ptr[1..]);

                    let amount_to_move = 1 + symbol.len();
                    return_value.push(Token {
                        position: current_position.clone(),
                        ttype: TokenType::QuoteSymbol(symbol),
                    });
                    move_cols(&mut current_position, amount_to_move);
                    content_ptr = new_content_ptr;
                }
            },
            '\'' => token_err!("end of file while tokenizing symbol"),
            '`' => match content_ptr.get(1) {
                Some('(') => simple_push!(BackquoteParen, 2),
                c => token_error!(format!(
                    "error tokenizing backtick paren, expected ')' but got '{c:?}'"
                )),
            },
            ',' if content_ptr.len() >= 2 => match content_ptr[1] {
                '(' => simple_push!(UnquoteExprParen, 2),
                '@' if content_ptr.len() >= 3 => match content_ptr[2] {
                    '(' => simple_push!(ListSpliceParen, 3),
                    c if symbol_end(c) => token_err!("unexpected end of symbol"),
                    _ => {
                        let (symbol, new_content_ptr) = to_symbol_end(&content_ptr[2..]);

                        let amount_to_move = 2 + symbol.len();
                        return_value.push(Token {
                            position: current_position.clone(),
                            ttype: TokenType::ListSpliceSymbol(symbol),
                        });
                        move_cols(&mut current_position, amount_to_move);
                        content_ptr = new_content_ptr;
                    }
                },
                '@' => token_err!("end of file while tokenizing symbol"),
                c if symbol_end(c) => token_err!("unexpected end of symbol"),
                _ => {
                    let (symbol, new_content_ptr) = to_symbol_end(&content_ptr[1..]);

                    let amount_to_move = 1 + symbol.len();
                    return_value.push(Token {
                        position: current_position.clone(),
                        ttype: TokenType::UnquoteSymbol(symbol),
                    });
                    move_cols(&mut current_position, amount_to_move);
                    content_ptr = new_content_ptr;
                }
            },
            ',' => token_err!("end of file while tokenizing symbol"),
            '"' => match to_string_end(&content_ptr[1..]) {
                Some((string, new_content_ptr)) => {
                    let amount_to_move = 2 + string.len();
                    return_value.push(Token {
                        position: current_position.clone(),
                        ttype: TokenType::String(string),
                    });
                    move_cols(&mut current_position, amount_to_move);
                    content_ptr = new_content_ptr;
                }
                None => token_err!("unexpected end of file when searching for end of string"),
            },
            '#' if content_ptr.len() >= 3 => match content_ptr[1] {
                '\'' => {
                    let (symbol, new_content_ptr) = to_symbol_end(&content_ptr[2..]);

                    let amount_to_move = 2 + symbol.len();
                    return_value.push(Token {
                        position: current_position.clone(),
                        ttype: TokenType::FuncSymbol(symbol),
                    });
                    move_cols(&mut current_position, amount_to_move);
                    content_ptr = new_content_ptr;
                }
                c => token_error!(format!(
                    "dispatch function for '{c}' has not been implemented"
                )),
            },
            '#' => token_err!("end of file while tokenizing"),
            c if !symbol_end(*c) => {
                let (symbol, new_content_ptr) = to_symbol_end(content_ptr);
                let symbollen = symbol.len();
                return_value.push(Token {
                    position: current_position.clone(),
                    ttype: TokenType::Symbol(symbol),
                });
                move_cols(&mut current_position, symbollen);
                content_ptr = new_content_ptr;
            }
            c => token_error!(format!("unexpected character: {c}")),
        }
    }

    Ok(return_value)
}

#[cfg(test)]
mod test {
    use super::*;
    use std::assert_matches::assert_matches;

    const ASDF: &[char] = &['a', 's', 'd', 'f'];

    macro_rules! assert_tokens_eq {
        ([$($token:expr),*], $test:expr) => {
            let tokens = $test.as_ref().expect("tokenizing failed with error");

            assert_eq!(vec![$($token),*], tokens.iter().map(|tok| tok.ttype.clone()).collect::<Vec<_>>());
        }
    }

    #[test]
    fn basic_parens() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: "()()".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_tokens_eq!(
            [
                TokenType::LeftParen,
                TokenType::RightParen,
                TokenType::LeftParen,
                TokenType::RightParen
            ],
            tokens
        );
    }

    #[test]
    fn basic_positioning() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: "\t\n (".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_eq!(
            Ok(vec![Token {
                position: Position {
                    file: Arc::from("<test>"),
                    line: 2,
                    col: 1
                },
                ttype: TokenType::LeftParen
            }]),
            tokens
        );
    }

    #[test]
    fn handle_quote_parensymbols() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: "'( ) 'asdf".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_tokens_eq!(
            [
                TokenType::QuoteParen,
                TokenType::RightParen,
                TokenType::QuoteSymbol(ASDF)
            ],
            tokens
        );

        let input = InputFile {
            name: "<test>".to_string(),
            contents: "'( '@".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));
    }

    #[test]
    fn handle_backquote_paren() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: "`( )".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_tokens_eq!([TokenType::BackquoteParen, TokenType::RightParen], tokens);

        let input = InputFile {
            name: "<test>".to_string(),
            contents: "`( `@".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));
    }

    #[test]
    fn handle_unquoting() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: ",asdf ,( ,@asdf ,@(".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_tokens_eq!(
            [
                TokenType::UnquoteSymbol(ASDF),
                TokenType::UnquoteExprParen,
                TokenType::ListSpliceSymbol(ASDF),
                TokenType::ListSpliceParen
            ],
            tokens
        );

        let input = InputFile {
            name: "<test>".to_string(),
            contents: ",".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));

        let input = InputFile {
            name: "<test>".to_string(),
            contents: ",)".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));

        let input = InputFile {
            name: "<test>".to_string(),
            contents: ",@)".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));

        let input = InputFile {
            name: "<test>".to_string(),
            contents: ",@".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));
    }

    #[test]
    fn handle_strings_and_symbols() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: "\"asdf\" asdf".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_tokens_eq!([TokenType::String(ASDF), TokenType::Symbol(ASDF)], tokens);

        let input = InputFile {
            name: "<test>".to_string(),
            contents: "\"".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));
    }

    #[test]
    fn handle_comments() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: "asdf\n;test\nasdf".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_tokens_eq!([TokenType::Symbol(ASDF), TokenType::Symbol(ASDF)], tokens);
    }

    #[test]
    fn handle_misc_characters() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: "@".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));

        let input = InputFile {
            name: "<test>".to_string(),
            contents: "#".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));

        let input = InputFile {
            name: "<test>".to_string(),
            contents: "#a".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_matches!(tokens, Err(_));
    }

    #[test]
    fn handle_func_reference() {
        let input = InputFile {
            name: "<test>".to_string(),
            contents: "#'asdf".chars().collect(),
        };

        let tokens = tokenize(&input);

        assert_tokens_eq!([TokenType::FuncSymbol(ASDF)], tokens);
    }

    #[test]
    fn symbol_splitting() {
        let input = "asdf fdsa".chars().collect::<Vec<_>>();

        assert_eq!(
            (ASDF, [' ', 'f', 'd', 's', 'a'].as_ref()),
            to_symbol_end(&input)
        );

        let input = "asdf)".chars().collect::<Vec<_>>();

        assert_eq!((ASDF, [')'].as_ref()), to_symbol_end(&input));

        let input = "asdf".chars().collect::<Vec<_>>();

        assert_eq!((ASDF, [].as_ref()), to_symbol_end(&input));
    }
}
