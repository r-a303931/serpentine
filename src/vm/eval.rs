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

use std::sync::{
    atomic::{AtomicU64, Ordering},
    Arc, RwLock,
};

use async_recursion::async_recursion;

use crate::Position;

use super::{
    error::{add_frame, RuntimeError, RuntimeErrorKind},
    Callable, Environment, EnvironmentBuilder, LispFunc, LispValue, List, SExpression,
    SharedContainer, Symbol,
};

fn eval_quotes<T>(quotes: &[SExpression]) -> List<T> {
    quotes
        .iter()
        .map(|expr| match expr {
            SExpression::Nil => LispValue::Nil,
            SExpression::Int(i) => LispValue::Int(*i),
            SExpression::Float(f) => LispValue::Float(*f),
            SExpression::String(s) => s.into(),
            SExpression::Symbol(s) => LispValue::Symbol(s.into()),
            SExpression::Expr(p, q) => LispValue::List(eval_quotes(&q)),
            SExpression::Quote(p, q) => LispValue::List(
                [
                    LispValue::Symbol("'".into()),
                    LispValue::List(eval_quotes(&q)),
                ]
                .into_iter()
                .collect(),
            ),
            SExpression::Backquote(p, q) => LispValue::List(
                [
                    LispValue::Symbol("`".into()),
                    LispValue::List(eval_quotes(&q)),
                ]
                .into_iter()
                .collect(),
            ),
            SExpression::QuoteSymbol(q) => LispValue::List(
                [
                    LispValue::Symbol("quote".into()),
                    LispValue::Symbol(q.into()),
                ]
                .into_iter()
                .collect(),
            ),
            SExpression::FuncSymbol(q) => LispValue::List(
                [LispValue::Symbol("#'".into()), LispValue::Symbol(q.into())]
                    .into_iter()
                    .collect(),
            ),
            SExpression::UnquoteSymbol(q) => LispValue::List(
                [LispValue::Symbol(",".into()), LispValue::Symbol(q.into())]
                    .into_iter()
                    .collect(),
            ),
            SExpression::ListSpliceSymbol(q) => LispValue::List(
                [LispValue::Symbol(",@".into()), LispValue::Symbol(q.into())]
                    .into_iter()
                    .collect(),
            ),
            SExpression::UnquoteExpression(p, q) => LispValue::List(
                [
                    LispValue::Symbol(",".into()),
                    LispValue::List(eval_quotes(&q)),
                ]
                .into_iter()
                .collect(),
            ),
            SExpression::ListSpliceExpr(p, q) => LispValue::List(
                [
                    LispValue::Symbol(",@".into()),
                    LispValue::List(eval_quotes(&q)),
                ]
                .into_iter()
                .collect(),
            ),
        })
        .map(Arc::new)
        .collect::<List<_>>()
}

#[async_recursion]
async fn eval_backquotes<T: Clone + Send + Sync>(
    ctx: T,
    pos: &Position,
    env: SharedContainer<Environment<T>>,
    quotes: &[SExpression],
) -> Result<List<T>, RuntimeError> {
    macro_rules! ret_simple {
        ($e:expr) => {
            Ok(vec![Arc::new($e)])
        };
    }

    let mut results = Vec::with_capacity(quotes.len());

    for expr in quotes {
        results.extend(
            match expr {
                SExpression::Nil => ret_simple!(LispValue::Nil),
                SExpression::Int(i) => ret_simple!(LispValue::Int(*i)),
                SExpression::Float(f) => ret_simple!(LispValue::Float(*f)),
                SExpression::String(s) => ret_simple!(s.into()),
                SExpression::Symbol(s) => ret_simple!(LispValue::Symbol(s.into())),
                SExpression::Expr(p, q) => ret_simple!(LispValue::List(eval_quotes(&q))),
                SExpression::FuncSymbol(q) => ret_simple!(LispValue::List(
                    [LispValue::Symbol("#'".into()), LispValue::Symbol(q.into()),]
                        .into_iter()
                        .collect(),
                )),
                SExpression::Backquote(p, q) => ret_simple!(LispValue::List(
                    [
                        LispValue::Symbol("`".into()),
                        LispValue::List(eval_quotes(&q)),
                    ]
                    .into_iter()
                    .collect(),
                )),
                SExpression::Quote(p, q) => ret_simple!(LispValue::List(
                    [
                        LispValue::Symbol("'".into()),
                        LispValue::List(eval_quotes(&q)),
                    ]
                    .into_iter()
                    .collect(),
                )),
                SExpression::QuoteSymbol(q) => ret_simple!(LispValue::List(
                    [
                        LispValue::Symbol("quote".into()),
                        LispValue::Symbol(q.into()),
                    ]
                    .into_iter()
                    .collect(),
                )),
                SExpression::UnquoteSymbol(q) => {
                    let envi = Environment::get_env(&env, pos)?;
                    envi.find_variable(&(q.into()), pos)?
                        .ok_or(())
                        .map_err(envi.map_err_kind(
                            |_| RuntimeErrorKind::VariableAccess(Arc::clone(&q)),
                            Some(pos),
                        ))
                        .map(|r| vec![r])
                }
                SExpression::ListSpliceSymbol(s) => {
                    let envi = Environment::get_env(&env, pos)?;
                    envi.find_variable(&(s.into()), pos)?
                        .ok_or(())
                        .map_err(envi.map_err_kind(
                            |_| RuntimeErrorKind::VariableAccess(Arc::clone(&s)),
                            Some(pos),
                        ))
                        .map(|r| match &*r {
                            LispValue::List(l) => l.iter().collect(),
                            other => vec![Arc::clone(&r)],
                        })
                }
                SExpression::UnquoteExpression(p, s) => eval_one(
                    ctx.clone(),
                    pos,
                    env.clone(),
                    &SExpression::Expr(p.clone(), s.to_vec()),
                )
                .await
                .map(|r| vec![r]),
                SExpression::ListSpliceExpr(p, s) => eval_one(
                    ctx.clone(),
                    pos,
                    env.clone(),
                    &SExpression::Expr(p.clone(), s.to_vec()),
                )
                .await
                .map(|r| match &*r {
                    LispValue::List(l) => l.iter().collect(),
                    other => vec![r],
                }),
            }?
            .into_iter(),
        );
    }

    Ok(results.into_iter().collect())
}

fn eval_quote<T>(expr: &SExpression) -> Result<LispValue<T>, RuntimeError> {
    match expr {
        SExpression::Nil => Ok(LispValue::Nil),
        SExpression::Int(i) => Ok(LispValue::Int(*i)),
        SExpression::Float(f) => Ok(LispValue::Float(*f)),
        SExpression::String(s) => Ok(LispValue::String(Arc::clone(&s))),
        SExpression::Symbol(s) => Ok(LispValue::Symbol(s.into())),
        SExpression::Expr(p, q) => Ok(LispValue::List(eval_quotes(&q))),
        SExpression::Quote(p, q) => Ok(LispValue::List(
            [
                LispValue::Symbol("'".into()),
                LispValue::List(eval_quotes(&q)),
            ]
            .into_iter()
            .collect(),
        )),
        SExpression::Backquote(p, q) => Ok(LispValue::List(
            [
                LispValue::Symbol("`".into()),
                LispValue::List(eval_quotes(&q)),
            ]
            .into_iter()
            .collect(),
        )),
        SExpression::QuoteSymbol(q) => Ok(LispValue::List(
            [
                LispValue::Symbol("quote".into()),
                LispValue::Symbol(q.into()),
            ]
            .into_iter()
            .collect(),
        )),
        SExpression::FuncSymbol(q) => Ok(LispValue::List(
            [LispValue::Symbol("#'".into()), LispValue::Symbol(q.into())]
                .into_iter()
                .collect(),
        )),
        SExpression::UnquoteSymbol(q) => Ok(LispValue::List(
            [LispValue::Symbol(",".into()), LispValue::Symbol(q.into())]
                .into_iter()
                .collect(),
        )),
        SExpression::ListSpliceSymbol(q) => Ok(LispValue::List(
            [LispValue::Symbol(",@".into()), LispValue::Symbol(q.into())]
                .into_iter()
                .collect(),
        )),
        SExpression::UnquoteExpression(p, q) => Ok(LispValue::List(
            [
                LispValue::Symbol(",".into()),
                LispValue::List(eval_quotes(&q)),
            ]
            .into_iter()
            .collect(),
        )),
        SExpression::ListSpliceExpr(p, q) => Ok(LispValue::List(
            [
                LispValue::Symbol(",@".into()),
                LispValue::List(eval_quotes(&q)),
            ]
            .into_iter()
            .collect(),
        )),
    }
}

const CURRENT_LAMBDA: AtomicU64 = AtomicU64::new(0);
const CURRENT_UNNAMED_FUNC: AtomicU64 = AtomicU64::new(0);

#[async_recursion]
async fn dispatch_special_form<T: Clone + Send + Sync>(
    name: &str,
    ctx: T,
    pos: &Position,
    env: SharedContainer<Environment<T>>,
    mut args: &[SExpression],
) -> Option<Result<Arc<LispValue<T>>, RuntimeError>> {
    macro_rules! tryy {
        ($val:expr) => {
            match $val {
                Ok(c) => c,
                Err(e) => return Some(Err(e)),
            }
        };
    }

    macro_rules! throw {
        ($($err:tt)*) => {{
            let envi = tryy!(Environment::get_env(&env, pos));
            return Some(envi.generate_err_pos(RuntimeErrorKind::$($err)*, pos.clone()));
        }}
    }

    macro_rules! throw_wta {
        ($n1:expr, $n2:expr) => {
            throw!(WrongTypeArgument($n1.into(), $n2.into()))
        };
    }

    macro_rules! throw_wac {
        ($name:expr) => {
            throw!(WrongArgumentCount {
                fname: $name.into(),
                supplied_count: args.len()
            })
        };
    }

    macro_rules! func {
        ($name:expr, $args:expr, $ty:ident, $env:expr) => {{
            let fargs = match &$args[0] {
                SExpression::Expr(_, v) => v.clone(),
                other => throw_wta!("List", other.get_pretty_name()),
            };

            let (body, docstring) = if $args.len() > 2 {
                match &$args[1] {
                    SExpression::String(ref docs) => (&$args[2..], Some(Arc::clone(docs))),
                    _ => (&$args[1..], None),
                }
            } else {
                (&$args[1..], None)
            };

            Callable::$ty(Arc::new(LispFunc {
                name: $name,
                env: $env,
                args: fargs,
                docstring,
                body: body.to_vec(),
            }))
        }};
    }

    macro_rules! symb {
        ($ind:expr) => {
            match &args[$ind] {
                SExpression::Symbol(s) => Symbol::from(s),
                other => throw_wta!("Symbol", other.get_pretty_name()),
            }
        };
        () => {
            symb!(0)
        };
    }

    macro_rules! fname {
        ($ind:expr) => {
            match &args[$ind] {
                SExpression::Symbol(s) if s.contains(':') => {
                    throw!(InvalidFunctionName(Arc::clone(s)))
                }
                SExpression::Symbol(s) => Symbol::from(s),
                other => throw_wta!("Symbol", other.get_pretty_name()),
            }
        };
        () => {
            fname!(0)
        };
    }

    match name {
        "cond" => {
            for arg in args {
                match arg {
                    SExpression::Expr(p, e) => {
                        if e.len() == 0 {
                            continue;
                        }

                        if e.len() == 1 {
                            return Some(eval_one(ctx, pos, env, &e[0]).await);
                        }

                        let cond = tryy!(eval_one(ctx.clone(), pos, env.clone(), &e[0]).await);

                        if !matches!(*cond, LispValue::Nil) {
                            return Some(eval_one(ctx, pos, env.clone(), &e.last().unwrap()).await);
                        }
                    }
                    other => throw_wta!("Expression", other.get_pretty_name()),
                }
            }

            Some(Ok(Arc::new(LispValue::Nil)))
        }
        "if" => {
            if args.len() < 2 {
                throw_wac!("if");
            }

            let cond = tryy!(eval_one(ctx.clone(), pos, env.clone(), &args[0]).await);

            let body = match *cond {
                LispValue::Nil => match &args[2..].last() {
                    None => return Some(Ok(Arc::new(LispValue::Nil))),
                    Some(l) => l,
                },
                _ => &args[1],
            };

            Some(eval_one(ctx, pos, env, body).await)
        }
        "setq" => {
            if args.len() != 2 {
                throw_wac!("setq");
            }

            let name = symb!();
            let val = tryy!(eval_one(ctx.clone(), pos, env.clone(), &args[1]).await);

            let mut envi = tryy!(Environment::get_env_mut(&env, &pos));
            tryy!(envi.set_variable(name, Arc::clone(&val), &pos));

            Some(Ok(val))
        }
        "quote" => {
            if args.len() != 1 {
                throw_wac!("quote");
            }

            Some(eval_quote(&args[0]).map(Arc::new))
        }
        "function" => {
            if args.len() < 2 {
                throw_wac!("function");
            }

            let fname = format!(
                "func-{}",
                CURRENT_UNNAMED_FUNC.fetch_add(1, Ordering::Relaxed)
            )
            .into();
            let func = func!(fname, &args[0..], Func, None).into();

            Some(Ok(Arc::new(func)))
        }
        "defun" => {
            if args.len() < 2 {
                throw_wac!("defun");
            }

            let name = fname!();
            let func = func!(name.clone(), &args[1..], Func, None);

            {
                let global = tryy!(Environment::get_global(env.clone(), pos));
                let mut envi = tryy!(Environment::get_env_mut(&global, pos));
                envi.set_function(name, func.clone());
            }

            Some(Ok(Arc::new(LispValue::Callable(func))))
        }
        "progn" => {
            let mut last = Arc::new(LispValue::Nil);

            for arg in args {
                last = tryy!(eval_one(ctx.clone(), pos, env.clone(), arg).await);
            }

            Some(Ok(last))
        }
        "defmacro" => {
            if args.len() < 2 {
                throw_wac!("defmacro");
            }

            let name = fname!();
            let func = func!(name.clone(), &args[1..], Macro, None);

            {
                let global = tryy!(Environment::get_global(env.clone(), pos));
                let mut envi = tryy!(Environment::get_env_mut(&global, pos));
                envi.set_function(name.clone(), func.clone());
            }

            Some(Ok(Arc::new(LispValue::Symbol(name))))
        }
        "lambda" => {
            if args.len() < 2 {
                throw_wac!("lambda");
            }

            let fname = format!("lambda-{}", CURRENT_LAMBDA.fetch_add(1, Ordering::Relaxed)).into();
            let func = func!(fname, &args[0..], Func, Some(env.clone()));

            Some(Ok(Arc::new(LispValue::Callable(func))))
        }
        "catch" => {
            if args.len() != 1 {
                throw_wac!("catch");
            }

            match eval_one(ctx.clone(), pos, env.clone(), &args[0]).await {
                Ok(v) => Some(Ok(v)),
                Err(e) => Some(Ok(Arc::new(LispValue::Error(e)))),
            }
        }
        // "error" => None,
        _ => None,
    }
}

#[async_recursion]
async fn execute_callable<T: Clone + Send + Sync>(
    callable: Callable<T>,
    ctx: T,
    pos: &Position,
    env: SharedContainer<Environment<T>>,
    args: &[SExpression],
) -> Result<Arc<LispValue<T>>, RuntimeError> {
    macro_rules! throw {
        ($($err:tt)*) => {{
            let envi = Environment::get_env(&env, pos)?;
            return envi.generate_err_pos(RuntimeErrorKind::$($err)*, pos.clone());
        }}
    }

    macro_rules! eval_args {
        () => {
            async {
                let mut result = Vec::with_capacity(args.len());

                for arg in args {
                    result.push(eval_one(ctx.clone(), pos, env.clone(), &arg).await?);
                }

                Ok(result)
            }
            .await?
        };
    }

    macro_rules! eval_func {
        ($lf:expr, $args:expr) => {{
            let parent_env = $lf
                .env
                .clone()
                .map_or_else(|| Environment::get_global(env.clone(), pos), Ok)?;

            let arg_names: Vec<Symbol> = $lf
                .args
                .iter()
                .map(|a| match a {
                    SExpression::Symbol(s) => Ok(s.into()),
                    other => throw!(InvalidFunctionDefinition(other.get_pretty_name().into())),
                })
                .collect::<Result<_, _>>()?;

            let arg_vars = arg_names.into_iter().zip($args).collect();

            let new_env = EnvironmentBuilder::new_from_parent(
                parent_env,
                Some($lf.name.0.clone()),
                pos.clone(),
            )
            .set_variables(arg_vars)
            .build();
            let new_env = Arc::new(RwLock::new(new_env));

            let mut ret_val = Arc::new(LispValue::Nil);

            for body_expr in &$lf.body {
                ret_val = eval_one(ctx.clone(), pos, new_env.clone(), body_expr)
                    .await
                    .map_err(add_frame(&$lf.name.0.clone(), pos))?;
            }

            ret_val
        }};
    }

    match callable {
        Callable::NativeMacro(_, nm) => {
            let new_code = nm.run((&ctx, pos), env.clone(), args.to_vec().clone())?;
            eval_one(ctx.clone(), pos, env, &new_code).await
        }
        Callable::NativeFunc(_, nf) => {
            let args = eval_args!();
            nf.run((&ctx, pos), env, args)
        }
        Callable::AsyncNativeMacro(_, anm) => {
            let new_code = anm
                .run((&ctx, pos), env.clone(), args.to_vec().clone())
                .await?;
            eval_one(ctx.clone(), pos, env, &new_code).await
        }
        Callable::AsyncNativeFunc(_, anf) => {
            let args = eval_args!();
            anf.run((&ctx, pos), env, args).await
        }
        Callable::Func(lf) => Ok(eval_func!(lf, eval_args!().into_iter().map(RwLock::new))),
        Callable::Macro(lm) => {
            let args = eval_quotes(args);
            let new_ast = eval_func!(lm, args.into_iter().map(RwLock::new));

            match new_ast.serialize(pos, true) {
                None => Ok(new_ast),
                Some(ast) => eval_one(ctx, pos, env, &ast).await,
            }
        }
    }
}

#[async_recursion]
pub async fn eval_one<T: Clone + Send + Sync>(
    ctx: T,
    pos: &Position,
    env: SharedContainer<Environment<T>>,
    arg: &SExpression,
) -> Result<Arc<LispValue<T>>, RuntimeError> {
    match arg {
        SExpression::Nil => Ok(Arc::new(LispValue::Nil)),
        SExpression::Int(i) => Ok(Arc::new(LispValue::Int(*i))),
        SExpression::Float(f) => Ok(Arc::new(LispValue::Float(*f))),
        SExpression::String(s) => Ok(Arc::new(s.into())),
        SExpression::QuoteSymbol(s) => Ok(Arc::new(LispValue::Symbol(s.into()))),
        SExpression::Symbol(s) => {
            let envi = Environment::get_env(&env, pos)?;
            envi.find_variable(&(s.into()), pos)?
                .ok_or(())
                .map_err(envi.map_err_kind(
                    |_| RuntimeErrorKind::VariableAccess(Arc::clone(&s)),
                    Some(pos),
                ))
        }
        SExpression::FuncSymbol(s) => {
            let envi = Environment::get_env(&env, pos)?;
            envi.find_function(&(s.into()), pos)?
                .ok_or(())
                .map_err(envi.map_err_kind(
                    |_| RuntimeErrorKind::VariableAccess(Arc::clone(&s)),
                    Some(pos),
                ))
                .map(LispValue::Callable)
                .map(Arc::new)
        }
        SExpression::Quote(pos, exps) => Ok(Arc::new(LispValue::List(eval_quotes(exps)))),
        SExpression::Backquote(pos, exps) => eval_backquotes(ctx, pos, env, exps)
            .await
            .map(LispValue::List)
            .map(Arc::new),
        SExpression::Expr(pos, exps) if exps.len() == 0 => Ok(Arc::new(LispValue::Nil)),
        SExpression::Expr(pos, exps) => {
            let fname = match &exps[0] {
                SExpression::Symbol(fname) => Ok(fname.clone()),
                notfname => {
                    let envi = Environment::get_env(&env, &pos)?;
                    Err(RuntimeError::new(
                        RuntimeErrorKind::InvalidFunction(notfname.clone()),
                        envi.get_environment_name(pos)?,
                        pos.clone(),
                    ))
                }
            }?;

            if let Some(dispatch) =
                dispatch_special_form(&fname, ctx.clone(), pos, env.clone(), &exps[1..]).await
            {
                return dispatch;
            }

            let func = {
                let envi = Environment::get_env(&env, pos)?;
                envi.find_function(&((&fname).into()), pos)?
                    .ok_or(())
                    .map_err(envi.map_err_kind(
                        |_| RuntimeErrorKind::VariableAccess(Arc::clone(&fname)),
                        Some(pos),
                    ))?
            };

            execute_callable(func, ctx, pos, env, &exps[1..]).await
        }
        _ => Environment::get_env(&env, pos)?
            .generate_err_pos(RuntimeErrorKind::BadContext, pos.clone()),
    }
}

#[cfg(test)]
mod test {
    use std::{
        assert_matches::assert_matches,
        sync::{Arc, Mutex, RwLock},
    };

    use super::*;

    use crate::{
        parser, tokenizer,
        vm::{self, EnvironmentBuilder, LispValue, List, Symbol},
        Position,
    };

    macro_rules! match_next {
        ($next:ident, $($rest:tt)*) => {{
            let val = $next.next().unwrap();
            assert_matches!(&*val, $($rest)*);
            val
        }}
    }

    macro_rules! add_env_value {
        ($ctx:expr, $env:ident, $name:ident, $value:expr, $pos:expr) => {{
            let value = Box::new($value) as Box<dyn std::any::Any>;

            match value.downcast::<&str>() {
                Ok(var) => {
                    let name = format!("<test var {}>", stringify!($name));
                    let input = tokenizer::InputFile {
                        name: name.clone(),
                        contents: var.chars().collect(),
                    };
                    let tokens = tokenizer::tokenize(&input)
                        .expect("could not tokenize input for test variable");
                    let mut parsed =
                        parser::parse(&tokens).expect("could not parse input for test variable");
                    let position = Position {
                        file: Arc::from(name.clone()),
                        line: 1,
                        col: 0,
                    };
                    let parsed = parsed.remove(0);

                    let mut environment = Arc::new(RwLock::new(
                        EnvironmentBuilder::new(name, position.clone()).build(),
                    ));

                    let res = eval_one($ctx, &position, environment.clone(), &parsed.into())
                        .await
                        .expect("could not evaluate input lisp for test variable");

                    let mut envi = Environment::get_env_mut(&$env, &position)
                        .expect("could not get environment to set variable");
                    envi.set_variable(stringify!($name).into(), res, &$pos)
                        .expect("could not set variable during init");
                }
                Err(other_value) => {
                    if let Ok(var) = other_value.downcast::<LispValue<_>>() {
                        match &*var {
                            LispValue::Callable(c) => {
                                let mut envi = Environment::get_env_mut(&$env, &$pos)
                                    .expect("could not get environment to set variable");
                                envi.set_function(stringify!($name).into(), c.clone());
                            }
                            val => {
                                let mut envi = Environment::get_env_mut(&$env, &$pos)
                                    .expect("could not get environment to set variable");
                                envi.set_variable(stringify!($name).into(), Arc::from(var), &$pos)
                                    .expect("could not set variable during init");
                            }
                        };
                    }
                }
            }
        }};
    }

    macro_rules! handle_err {
        ($expr:expr, err) => {
            $expr
        };
        ($expr:expr, $($err:ident)?) => {
            $expr.expect("could not evaluate input lisp")
        };
    }

    macro_rules! handle_err_type {
        (err) => {
            Result<Arc<LispValue<()>>, RuntimeError>
        };
        ($($err:ident)?) => {
            Arc<LispValue<()>>
        };
    }

    macro_rules! generate_match {
        ($eval_res:expr, $out:ident, $name:ident, $val:expr) => {
            let LispValue::$out(ref $name) = *$eval_res else { panic!("did not get expected value (expected {}, but got {})", stringify!($out), $eval_res.get_pretty_name()); };
        };
        ($eval_res:expr, $out:ident, $name:ident, ) => {
            let LispValue::$out = *$eval_res else { panic!("did not get expected value (expected {}, but got {})", stringify!($out), $eval_res.get_pretty_name()); };
        };
    }

    macro_rules! write_eval_test {
        (fn $test_name:ident ($inp:expr => LispValue::$out:ident$(($val:expr))?)) => {
            write_eval_test!(fn $test_name ($inp => eval_res, ()) {
                generate_match!(eval_res, $out, val, $($val)?);
                $(assert_eq!(val, &$val);)?
            });
        };
        (fn $test_name:ident ($inp:expr => LispValue::$out:ident$(($val:expr))?, ($($var_name:ident => $var_value:expr),*))) => {
            write_eval_test!(fn $test_name ($inp => eval_res, ($($var_name => $var_value),*)) {
                generate_match!(eval_res, $out, val, $($val)?);
                $(assert_eq!(val, &$val);)?
            });
        };
        (fn $test_name:ident ($inp:expr => $res:ident) { $($body:tt)* }) => {
            write_eval_test!(fn $test_name ($inp => $res, ()) {
                $($body)*
            });
        };
        (fn $test_name:ident $($err:ident)? ($inp:expr => $res:ident, ($($var_name:ident => $var_value:expr),*)) { $($body:tt)* }) => {
            write_eval_test!(fn $test_name $($err)? ($inp => $res, ($($var_name => $var_value),*), env, position) { $($body)* });
        };
        (fn $test_name:ident $($err:ident)? ($inp:expr => $res:ident, ($($var_name:ident => $var_value:expr),*), $env_name:ident, $pos_name:ident) { $($body:tt)* }) => {
            write_eval_test!(fn $test_name $($err)? (ctx, (); $inp => $res, ($($var_name => $var_value),*), $env_name, $pos_name) { $($body)* });
        };
        (fn $test_name:ident $($err:ident)? ($ctx_name:ident, $ctx:expr; $inp:expr => $res:ident, ($($var_name:ident => $var_value:expr),*), $env_name:ident, $pos_name:ident) { $($body:tt)* }) => {
            #[tokio::test]
            async fn $test_name() {
                let input = tokenizer::InputFile {
                    name: "<test>".to_string(),
                    contents: $inp.chars().collect()
                };
                let tokens = tokenizer::tokenize(&input).expect("could not tokenize input");
                let mut parsed = parser::parse(&tokens).expect("could not parse input");
                let $pos_name = Position { file: "<test>".into(), line: 1, col: 0 };
                let parsed = parsed.remove(0);

                let mut $env_name = Arc::new(RwLock::new(EnvironmentBuilder::new("<test>", $pos_name.clone()).build()));

                $(add_env_value!($ctx, $env_name, $var_name, $var_value, $pos_name);)*

                let $ctx_name = $ctx;

                let $res = handle_err!(eval_one(
                    $ctx_name.clone(),
                    &$pos_name,
                    $env_name.clone(),
                    &parsed.into()
                ).await, $($err)?);

                $($body)*
            }
        };
    }

    write_eval_test!(fn test_eval_nil ("nil" => LispValue::Nil));
    write_eval_test!(fn test_eval_empty ("()" => LispValue::Nil));
    write_eval_test!(fn test_eval_int ("1" => LispValue::Int(1)));
    write_eval_test!(fn test_eval_float ("3.14" => LispValue::Float(3.14)));
    write_eval_test!(fn test_eval_string ("\"str\"" => LispValue::String("str".into())));
    write_eval_test!(fn test_eval_symbol ("'symb" => LispValue::Symbol("symb".into())));

    write_eval_test!(fn test_eval_quotes ("'(symb 1 2.3 \"asdf\" nil)" => eval_res) {
        let LispValue::List(ref items) = *eval_res else { panic!("did not convert to a list"); };

        let mut items = items.iter();

        match_next!(items, LispValue::Symbol(_));
        match_next!(items, LispValue::Int(1));
        match_next!(items, LispValue::Float(2.3));
        match_next!(items, LispValue::String(_));
        match_next!(items, LispValue::Nil);
    });

    write_eval_test!(fn test_eval_variable ("symb" => LispValue::Int(1), (
        symb => "1"
    )));

    write_eval_test!(fn test_eval_quote_list ("'('symb)" => eval_res) {
        let LispValue::List(ref items) = *eval_res else { panic!("did not convert to a list"); };

        let mut items = items.iter();

        let ql = match_next!(items, LispValue::List(_));

        let LispValue::List(ref items2) = *ql else { panic!("did not convert to a list"); };
        let mut items2 = items2.iter();

        match_next!(items2, LispValue::Symbol(_));
        match_next!(items2, LispValue::Symbol(_));
    });

    write_eval_test!(fn test_eval_backquotes ("`(symb ,@var ,var ,@list ,list)" => eval_res, (
        var => "3.14",
        list => "'(1 2 3)"
    )) {
        let LispValue::List(ref items) = *eval_res else { panic!("did not convert to a list"); };

        let mut items = items.iter();

        match_next!(items, LispValue::Symbol(_));
        match_next!(items, LispValue::Float(3.14));
        match_next!(items, LispValue::Float(3.14));
        match_next!(items, LispValue::Int(1));
        match_next!(items, LispValue::Int(2));
        match_next!(items, LispValue::Int(3));
        match_next!(items, LispValue::List(_));
    });

    write_eval_test!(fn test_invalid_fname err ("(())" => eval_res, ()) {
        let Err(err) = eval_res else { panic!("did not error"); };
        assert_matches!(err.kind(), RuntimeErrorKind::InvalidFunction(_));
    });

    lispfn_macro::declare_lisp_func!(local ret_1 "ret-1" (_pos, _env) LispValue::Int(1).into());
    write_eval_test!(fn test_eval_func ("(ret_1)" => LispValue::Int(1), (
        ret_1 => LispValue::Callable(ret_1::new())
    )));

    write_eval_test!(fn test_eval_quote ("(quote asdf)" => LispValue::Symbol("asdf".into())));
    write_eval_test!(fn test_eval_if ("(if 1 1 2)" => LispValue::Int(1)));
    write_eval_test!(fn test_eval_if2 ("(if nil 1 2)" => LispValue::Int(2)));
    write_eval_test!(fn test_eval_if3 ("(if nil 1 2 3)" => LispValue::Int(3)));
    write_eval_test!(fn test_eval_if4 ("(if (ret_1) (ret_1) 2 3)" => LispValue::Int(1), (
        ret_1 => LispValue::Callable(ret_1::new())
    )));

    lispfn_macro::declare_lisp_func!(local inc_1 "inc-1" (ctx: Arc<Mutex<u8>>, _pos, _env) {
        let mut inner = ctx.lock().expect("could not get counter");
        *inner += 1;
        LispValue::Int((*inner).into()).into()
    });
    write_eval_test!(fn test_eval_if5 (ctx, Arc::new(Mutex::new(1u8)); "(if (inc_1) (inc_1) (inc_1) (inc_1))" => eval_res, (
        inc_1 => LispValue::Callable(inc_1::new())
    ), env, pos) {
        let LispValue::Int(ref val) = *eval_res else { panic!("did not get expected value (expected Int, but got {})", eval_res.get_pretty_name()); };
        assert_eq!(val, &3);

        let inner = ctx.lock().expect("could not get counter");
        assert_eq!(*inner, 3);
    });

    write_eval_test!(fn test_eval_setq ("(setq asdf 1)" => eval_res, (), env, pos) {
        let LispValue::Int(ref val) = *eval_res else { panic!("did not get expected value (expected Int, but got {})", eval_res.get_pretty_name()); };
        assert_eq!(val, &1);

        let var = Environment::get_env(&env, &pos)
            .expect("could not get env")
            .find_variable(&("asdf".into()), &pos)
            .expect("could not find variable")
            .expect("could not find variable");

        let LispValue::Int(ref val) = *var else { panic!("did not get expected value (expected Int, but got {})", eval_res.get_pretty_name()); };
        assert_eq!(val, &1);
    });

    write_eval_test!(fn test_eval_cond ("(cond (1 2) ('t 3))" => LispValue::Int(2)));
    write_eval_test!(fn test_eval_cond2 ("(cond (1) ('t 3))" => LispValue::Int(1)));
    write_eval_test!(fn test_eval_cond3 ("(cond)" => LispValue::Nil));
    write_eval_test!(fn test_eval_cond4 ("(cond (nil 2) ('t 3))" => LispValue::Int(3)));
    write_eval_test!(fn test_eval_cond5 ("(cond ())" => LispValue::Nil));
    write_eval_test!(fn test_eval_cond6 ("(cond (nil 2) ('t 3 4))" => LispValue::Int(4)));

    write_eval_test!(fn test_eval_progn ("(progn 1 2 3)" => LispValue::Int(3)));

    write_eval_test!(fn test_catch ("(catch (notafunc))" => eval_res) {
        assert_matches!(&*eval_res, &LispValue::Error(_));
    });

    write_eval_test!(fn test_defun_call ("(progn (defun test () 3) (test))" => LispValue::Int(3)));

    lispfn_macro::declare_lisp_func!(local add_1 "add_1" (_pos, _env, arg: Int) {
        LispValue::Int(arg + 1).into()
    });
    write_eval_test!(fn test_macro_call ("(progn \n\
        (defmacro callfunc (f) `(,f 3)) \n\
        (callfunc add_1))" => LispValue::Int(4), (
        add_1 => LispValue::Callable(add_1::new())
    )));
}
