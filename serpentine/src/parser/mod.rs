// parser/mod.rs: provides parsing functions that convert tokens to s-expressions
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

use std::sync::Arc;

use crate::{
    tokenizer::{Token, TokenType},
    Position,
};

/// Represents an error that can crop up when parsing Serpentine programs
#[derive(Debug)]
pub struct ParseError {
    position: Position,
    message: String,
}

impl ParseError {
    /// Retrieve the position of the parse error
    pub fn position(&self) -> &Position {
        &self.position
    }

    /// Retrieve a user facing message for the parse error
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// Represents a borrowed [`SExpression`], where all the actual
/// character data is held by the struct holding file data
///
/// The exception is [`SExpr::String`], as it holds parsed
/// character data to include things such as newline characters
/// and escaped quotes
#[derive(Debug, PartialEq)]
pub enum SExpr<'a> {
    Nil,
    Symbol(&'a [char]),
    Int(i64),
    Float(f64),
    FuncSymbol(&'a [char]),
    String(Arc<str>),
    QuoteSymbol(&'a [char]),
    UnquoteSymbol(&'a [char]),
    ListSpliceSymbol(&'a [char]),
    Expr(Position, Vec<SExpr<'a>>),
    Quote(Position, Vec<SExpr<'a>>),
    Backquote(Position, Vec<SExpr<'a>>),
    UnquoteExpression(Position, Vec<SExpr<'a>>),
    ListSpliceExpr(Position, Vec<SExpr<'a>>),
}

/// Represents an owned S-Expression
///
/// `Arc<str>` is used instead of [`String`], as this is a data type that
/// needs to be cloned frequently and is immutable
#[derive(Debug, PartialEq, Clone)]
pub enum SExpression {
    Nil,
    Symbol(Arc<str>),
    Int(i64),
    Float(f64),
    FuncSymbol(Arc<str>),
    String(Arc<str>),
    QuoteSymbol(Arc<str>),
    UnquoteSymbol(Arc<str>),
    ListSpliceSymbol(Arc<str>),
    Expr(Position, Vec<SExpression>),
    Quote(Position, Vec<SExpression>),
    Backquote(Position, Vec<SExpression>),
    UnquoteExpression(Position, Vec<SExpression>),
    ListSpliceExpr(Position, Vec<SExpression>),
}

impl From<Arc<str>> for SExpression {
    fn from(s: Arc<str>) -> Self {
        Self::String(s)
    }
}

impl From<&str> for SExpression {
    fn from(s: &str) -> Self {
        Self::String(s.into())
    }
}

impl From<f64> for SExpression {
    fn from(f: f64) -> Self {
        Self::Float(f)
    }
}

impl From<i64> for SExpression {
    fn from(i: i64) -> Self {
        Self::Int(i)
    }
}

impl SExpression {
    /// Debugging function used to help generate parse errors
    pub fn get_pretty_name(&self) -> &'static str {
        match self {
            Self::Nil => "Nil",
            Self::Symbol(_) => "Symbol",
            Self::Int(_) => "Int",
            Self::Float(_) => "Float",
            Self::FuncSymbol(_) => "FuncSymbol",
            Self::String(_) => "String",
            Self::QuoteSymbol(_) => "QuoteSymbol",
            Self::UnquoteSymbol(_) => "UnquoteSymbol",
            Self::ListSpliceSymbol(_) => "ListSpliceSymbol",
            Self::Expr(_, _) => "Expression",
            Self::Quote(_, _) => "QuoteExpression",
            Self::Backquote(_, _) => "BackquoteExpression",
            Self::UnquoteExpression(_, _) => "UnquoteExpression",
            Self::ListSpliceExpr(_, _) => "ListSpliceExpression",
        }
    }

    /// Allows for serializing S-Expressions back to plaintext, allowing
    /// for transfering, saving, debugging, etc
    pub fn serialize(&self, _pretty: bool) -> String {
        todo!()
    }
}

fn owned(expr: SExpr<'_>) -> SExpression {
    match expr {
        SExpr::Nil => SExpression::Nil,
        SExpr::Symbol(s) => SExpression::Symbol(Arc::from(s.iter().collect::<String>())),
        SExpr::Int(i) => SExpression::Int(i),
        SExpr::Float(f) => SExpression::Float(f),
        SExpr::FuncSymbol(s) => SExpression::FuncSymbol(Arc::from(s.iter().collect::<String>())),
        SExpr::String(s) => SExpression::String(s),
        SExpr::QuoteSymbol(s) => SExpression::QuoteSymbol(Arc::from(s.iter().collect::<String>())),
        SExpr::UnquoteSymbol(s) => {
            SExpression::UnquoteSymbol(Arc::from(s.iter().collect::<String>()))
        }
        SExpr::ListSpliceSymbol(s) => {
            SExpression::ListSpliceSymbol(Arc::from(s.iter().collect::<String>()))
        }
        SExpr::Expr(p, e) => SExpression::Expr(p, e.into_iter().map(&owned).collect()),
        SExpr::Quote(p, q) => SExpression::Quote(p, q.into_iter().map(&owned).collect()),
        SExpr::Backquote(p, q) => SExpression::Backquote(p, q.into_iter().map(&owned).collect()),
        SExpr::UnquoteExpression(p, u) => {
            SExpression::UnquoteExpression(p, u.into_iter().map(&owned).collect())
        }
        SExpr::ListSpliceExpr(p, l) => {
            SExpression::ListSpliceExpr(p, l.into_iter().map(&owned).collect())
        }
    }
}

impl<'a> From<SExpr<'a>> for SExpression {
    fn from(expr: SExpr<'a>) -> Self {
        owned(expr)
    }
}

/// Takes a list of tokens, and parses the next SExpr, returning unparsed tokens
///
/// If there is an unexpected EOF, it is not detected unless it is a part of the
/// S-Expression being parsed
///
/// ### Panics
///
/// This function assumes the presence of tokens, and will panic if the slice of
/// Tokens is empty
pub fn parse_next<'a, 'b>(
    mut tokens: &'b [Token<'a>],
) -> Result<(SExpr<'a>, &'b [Token<'a>]), ParseError> {
    macro_rules! parse_until_close {
        ($type:tt) => {{
            let mut items = vec![];
            let paren = &tokens[0];
            tokens = &tokens[1..];

            while let Some(token) = tokens.get(0) {
                if let TokenType::RightParen = token.ttype {
                    break;
                }

                let (expr, new_tokens) = parse_next(tokens)?;
                items.push(expr);
                tokens = new_tokens;
            }

            Ok((SExpr::$type(paren.position.clone(), items), &tokens[1..]))
        }};
    }

    match tokens[0].ttype {
        TokenType::QuoteSymbol(symb) => Ok((SExpr::QuoteSymbol(symb), &tokens[1..])),
        TokenType::UnquoteSymbol(symb) => Ok((SExpr::UnquoteSymbol(symb), &tokens[1..])),
        TokenType::ListSpliceSymbol(symb) => Ok((SExpr::ListSpliceSymbol(symb), &tokens[1..])),
        TokenType::String(string) => Ok((
            SExpr::String(Arc::from(
                string
                    .iter()
                    .collect::<String>()
                    .replace("\\\"", "\"")
                    .replace("\\n", "\n"),
            )),
            &tokens[1..],
        )),
        TokenType::FuncSymbol(symb) => Ok((SExpr::FuncSymbol(symb), &tokens[1..])),
        TokenType::Symbol(symb) => {
            let symbstr: String = symb.iter().collect();

            if symbstr == "nil" {
                return Ok((SExpr::Nil, &tokens[1..]));
            }

            if let Ok(num) = symbstr.parse::<i64>() {
                return Ok((SExpr::Int(num), &tokens[1..]));
            }

            if let Ok(num) = symbstr.parse::<f64>() {
                return Ok((SExpr::Float(num), &tokens[1..]));
            }

            Ok((SExpr::Symbol(symb), &tokens[1..]))
        }
        TokenType::RightParen => Err(ParseError {
            position: tokens[0].position.clone(),
            message: "unexpected ) when parsing input".to_string(),
        }),
        TokenType::LeftParen => parse_until_close!(Expr),
        TokenType::QuoteParen => parse_until_close!(Quote),
        TokenType::BackquoteParen => parse_until_close!(Backquote),
        TokenType::UnquoteExprParen => parse_until_close!(UnquoteExpression),
        TokenType::ListSpliceParen => parse_until_close!(ListSpliceExpr),
    }
}

/// Parses all of the provided tokens, returning parsed out S-Expressions.
///
/// In the case of an empty slice of Tokens, this returns an empty Vec
///
/// # Examples
///
/// ```
/// # use serpentine::{SError, parser::{parse, SExpr}, tokenizer::{InputFile, tokenize}};
/// # fn main() -> Result<(), SError> {
/// let input = InputFile { name: "<test>".to_string(), contents: "3 \"a\\\"sdf\"".chars().collect() };
/// let tokens = tokenize(&input)?;
/// let parsed = parse(&tokens)?;
///
/// assert_eq!(parsed[0], SExpr::Int(3));
/// assert_eq!(parsed[1], SExpr::String("a\"sdf".into()));
/// #   Ok(())
/// # }
/// ```
pub fn parse<'a>(tokens: &[Token<'a>]) -> Result<Vec<SExpr<'a>>, ParseError> {
    if tokens.is_empty() {
        return Ok(vec![]);
    }

    let mut tokens_left = tokens;
    let mut exprs = vec![];

    while !tokens_left.is_empty() {
        let (expr, rest) = parse_next(tokens_left)?;
        exprs.push(expr);
        tokens_left = rest;
    }

    Ok(exprs)
}

/// Allows for constructing SExpression structs
///
/// # Examples
///
/// ```
/// # use serpentine::lisp_lit;
/// # use serpentine::parser::SExpression;
/// serpentine::lisp_lit!(()); // SExpression::Nil
/// serpentine::lisp_lit!((quote ([1] [2] [3])));
/// // equivalent to:
/// // SExpression::Quote(<position>, vec![
/// //     1.into(),
/// //     2.into(),
/// //     3.into()
/// // ])
/// serpentine::lisp_lit!(((sym "add-1") {SExpression::Int(1)}));
/// // equivalent to:
/// // SExpression::Expr(<position>, vec![
/// //     SExpression::Symbol("add-1".into()),
/// //     SExpression::Int(1)
/// // ])
/// ```
#[macro_export]
macro_rules! lisp_lit {
    ({$p:expr}; ()) => {
        $crate::parser::SExpression::Nil
    };
    ({$p:expr}; (quote ($($body:tt)*))) => {
        $crate::parser::SExpression::Quote($p.clone(), [
            $(lisp_lit!({$p}; $body),)*
        ].to_vec())
    };
    ({$p:expr}; (quote $name:expr)) => {
        $crate::parser::SExpression::QuoteSymbol($name.into())
    };
    ({$p:expr}; [$val:expr]) => {
        $val.into()
    };
    ({$p:expr}; (sym $val:expr)) => {
        $crate::parser::SExpression::Symbol($val.into())
    };
    ({$p:expr}; {$val:expr}) => {
        $val
    };
    ({$p:expr}; ,@($($body:tt)*)) => {
        $crate::parser::SExpression::ListSpliceExpr($p.clone(), [
            $(lisp_lit!({$p}; $body),)*
        ].to_vec())
    };
    ({$p:expr}; ,@$name:expr) => {
        $crate::parser::SExpression::ListSpliceSymbol($name.into())
    };
    ({$p:expr}; ,($($body:tt)*)) => {
        $crate::parser::SExpression::UnquoteExpression($p.clone(), [
            $(lisp_lit!({$p}; $body),)*
        ].to_vec())
    };
    ({$p:expr}; ,$name:expr) => {
        $crate::parser::SExpression::UnquoteSymbol($name.into())
    };
    ({$p:expr}; ($($body:tt)*)) => {
        $crate::parser::SExpression::Expr($p.clone(), [
            $(lisp_lit!({$p}; $body),)*
        ].to_vec())
    };
    ($($body:tt)*) => {{
        let _position = $crate::Position::new("<lisplit>", 1, 0);
        lisp_lit!({_position}; $($body)*)
    }};
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::tokenizer::tokenize;
    use std::assert_matches::assert_matches;

    struct TestSource {
        input: crate::tokenizer::InputFile,
    }

    impl TestSource {
        pub fn new(source: &str) -> Self {
            Self {
                input: crate::tokenizer::InputFile {
                    name: "<test>".to_string(),
                    contents: source.chars().collect(),
                },
            }
        }

        pub fn tokenize(&self) -> Vec<crate::tokenizer::Token<'_>> {
            tokenize(&self.input).expect("could not tokenize input")
        }
    }

    const ASDF: &[char] = &['a', 's', 'd', 'f'];

    #[test]
    fn parse_single_layer() {
        let source = TestSource::new("()");
        let empty = source.tokenize();

        let parsed = parse_next(&empty).expect("could not parse the input provided");

        assert_matches!(parsed.0, SExpr::Expr(_, _));

        let source = TestSource::new("(asdf)");
        let asdf = source.tokenize();

        let parsed = parse_next(&asdf).expect("could not parse the input provided");

        let SExpr::Expr(_, elems) = parsed.0 else {
            dbg!(parsed);
            panic!("output did not match expected");
        };
        assert_matches!(elems[..], [SExpr::Symbol(ASDF)]);
    }

    #[test]
    fn parse_multiple_layers() {
        let source = TestSource::new("('() ,(  `(\nasdf) ))");
        let source2 = source.tokenize();

        let parsed = parse_next(&source2).expect("could not parse the input provided");

        let SExpr::Expr(_, elems) = parsed.0 else {
            dbg!(parsed);
            panic!("output did not match expected");
        };
        assert_matches!(elems[0], SExpr::Quote(_, _));
    }

    #[test]
    fn parse_numbers() {
        let source = TestSource::new("9 3.14");
        let source2 = source.tokenize();

        let (parsed, source3) = parse_next(&source2).expect("could not parse input 1");
        let (parsed2, _) = parse_next(&source3).expect("could not parse input 2");

        assert_eq!(parsed, SExpr::Int(9));
        assert_eq!(parsed2, SExpr::Float(3.14));
    }

    #[test]
    fn parse_strings() {
        let source = TestSource::new("\"string \\\" 1\" \"string 2\\n\"");
        let source2 = source.tokenize();

        let Ok((SExpr::String(parsed), source3)) = parse_next(&source2) else {
            panic!("could not parse item 1");
        };
        let Ok((SExpr::String(parsed2), _)) = parse_next(&source3) else {
            panic!("could not parse item 2");
        };

        assert_eq!(&*parsed, "string \" 1");
        assert_eq!(&*parsed2, "string 2\n");
    }

    #[test]
    fn parse_multiple() {
        let source = TestSource::new("9 3.14");
        let source2 = source.tokenize();

        let parsed = parse(&source2).expect("could not parse input");

        assert_eq!(parsed, vec![SExpr::Int(9), SExpr::Float(3.14)]);
    }

    #[test]
    fn lisp_lit_into_val() {
        assert_eq!(SExpression::Int(9), lisp_lit! { [9] });
    }

    #[test]
    fn lisp_lit_basic_expr() {
        let SExpression::Expr(_, v) = lisp_lit! { ([1] [2] ["test"]) } else {
            panic!("could not create expression");
        };

        assert_eq!(
            v,
            vec![
                SExpression::Int(1),
                SExpression::Int(2),
                SExpression::String("test".into())
            ]
        );
    }

    #[test]
    fn lisp_lit_quote_symb() {
        assert_eq!(
            SExpression::QuoteSymbol("test".into()),
            lisp_lit! { (quote "test") }
        );
    }

    #[test]
    fn lisp_lit_quote_expr() {
        let SExpression::Quote(_, v) = lisp_lit! { (quote ([1] [2] ["test"])) } else {
            panic!("could not create expression");
        };
        assert_eq!(
            v,
            vec![
                SExpression::Int(1),
                SExpression::Int(2),
                SExpression::String("test".into())
            ]
        );
    }

    #[test]
    fn lisp_lit_unquote() {
        let SExpression::UnquoteExpression(_, v) = lisp_lit! { ,([1] [2] ["test"]) } else {
            panic!("could not create expression");
        };
        assert_eq!(
            v,
            vec![
                SExpression::Int(1),
                SExpression::Int(2),
                SExpression::String("test".into())
            ]
        );

        assert_eq!(
            lisp_lit! { ,"test" },
            SExpression::UnquoteSymbol("test".into())
        );
    }

    #[test]
    fn lisp_lit_splice() {
        let SExpression::ListSpliceExpr(_, v) = lisp_lit! { ,@([1] [2] ["test"]) } else {
            panic!("could not create expression");
        };
        assert_eq!(
            v,
            vec![
                SExpression::Int(1),
                SExpression::Int(2),
                SExpression::String("test".into())
            ]
        );

        assert_eq!(
            lisp_lit! { ,@"test" },
            SExpression::ListSpliceSymbol("test".into())
        );
    }
}
