// vm/mod.rs: contains data types used at runtime and defines modules and environments
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

use std::{
    collections::HashMap,
    fmt::{self, Debug},
    hash::Hash,
    iter::{FromIterator, IntoIterator},
    path::PathBuf,
    sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard},
};

use crate::{lisp_lit, parser::SExpression, Position};

pub mod error;
pub mod eval;

use error::{convert_to_error, man_convert_to_err, RuntimeError, RuntimeErrorKind};

/// Alias for the type of container used to share environments between different
/// executions of lisp functions
pub type SharedContainer<T> = Arc<RwLock<T>>;

/// Refers to a mutable reference to a variable. LispValues are immutable, so they
/// a mutable reference just means it can change which immutable value it points to
pub type MutVarRef<T> = RwLock<Arc<LispValue<T>>>;

/// Likewise for [`MutVarRef`], but for functions
pub type MutFuncRef<T> = RwLock<Callable<T>>;

/// Represents the List data structure in the Lisp environment
pub struct List<T> {
    head: Option<Arc<ListItem<T>>>,
}

/// Holds the reference to an item in the lisp list, as well as potentially to the
/// rest of the list
pub struct ListItem<T> {
    cons: Arc<LispValue<T>>,
    cdr: Option<Arc<ListItem<T>>>,
}

impl<T> List<T> {
    /// Converts a List into an Iterator with shared references
    pub fn iter(&self) -> ListIter<T> {
        ListIter {
            head: self.head.clone(),
        }
    }
}

impl<T, In: Into<Arc<LispValue<T>>>> FromIterator<In> for List<T> {
    fn from_iter<I: IntoIterator<Item = In>>(iter: I) -> Self {
        let mut item_stack = iter.into_iter().collect::<Vec<_>>();

        let mut head = None;

        while let Some(item) = item_stack.pop() {
            head = Some(Arc::new(ListItem {
                cons: item.into(),
                cdr: head,
            }))
        }

        List { head }
    }
}

impl<T> Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

pub struct ListIter<T> {
    head: Option<Arc<ListItem<T>>>,
}

impl<T> Iterator for ListIter<T> {
    type Item = Arc<LispValue<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.head.as_ref() {
            None => None,
            Some(val) => {
                let cons = Arc::clone(&val.cons);
                self.head = val.cdr.clone();
                Some(cons)
            }
        }
    }
}

pub struct LispFunc<T> {
    name: Symbol,
    env: Option<SharedContainer<Environment<T>>>,
    args: Vec<SExpression>,
    docstring: Option<Arc<str>>,
    // declarations: ???,
    body: Vec<SExpression>,
}

impl<T> Clone for LispFunc<T> {
    fn clone(&self) -> Self {
        LispFunc {
            name: self.name.clone(),
            env: self.env.clone(),
            args: self.args.clone(),
            docstring: self.docstring.clone(),
            body: self.body.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Symbol(Arc<str>);

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol(s.into())
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Self {
        Symbol(s.into())
    }
}

impl From<Arc<str>> for Symbol {
    fn from(s: Arc<str>) -> Self {
        Symbol(s)
    }
}

impl From<&Arc<str>> for Symbol {
    fn from(s: &Arc<str>) -> Self {
        Symbol(Arc::clone(s))
    }
}

pub trait LispNativeMacro<T>: Debug {
    fn run(
        &self,
        ctx: (&T, &Position),
        env: SharedContainer<Environment<T>>,
        args: Vec<SExpression>,
    ) -> Result<SExpression, RuntimeError>;

    fn docs(&self) -> Option<Arc<str>>;
}

pub trait LispNativeFunc<T>: Debug {
    fn run(
        &self,
        ctx: (&T, &Position),
        env: SharedContainer<Environment<T>>,
        args: Vec<Arc<LispValue<T>>>,
    ) -> Result<Arc<LispValue<T>>, RuntimeError>;

    fn docs(&self) -> Option<Arc<str>>;
}

#[async_trait::async_trait]
pub trait LispAsyncNativeMacro<T>: Debug {
    async fn run(
        &self,
        ctx: (&T, &Position),
        env: SharedContainer<Environment<T>>,
        args: Vec<SExpression>,
    ) -> Result<SExpression, RuntimeError>;

    fn docs(&self) -> Option<Arc<str>>;
}

#[async_trait::async_trait]
pub trait LispAsyncNativeFunc<T>: Debug {
    async fn run(
        &self,
        ctx: (&T, &Position),
        env: SharedContainer<Environment<T>>,
        args: Vec<Arc<LispValue<T>>>,
    ) -> Result<Arc<LispValue<T>>, RuntimeError>;

    fn docs(&self) -> Option<Arc<str>>;
}

pub enum Callable<T> {
    Macro(Arc<LispFunc<T>>),
    Func(Arc<LispFunc<T>>),
    NativeFunc(&'static str, Arc<dyn LispNativeFunc<T> + Send + Sync>),
    AsyncNativeFunc(&'static str, Arc<dyn LispAsyncNativeFunc<T> + Send + Sync>),
    NativeMacro(&'static str, Arc<dyn LispNativeMacro<T> + Send + Sync>),
    AsyncNativeMacro(&'static str, Arc<dyn LispAsyncNativeMacro<T> + Send + Sync>),
}

impl<T> Clone for Callable<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Macro(f) => Self::Macro(Arc::clone(f)),
            Self::Func(f) => Self::Func(Arc::clone(f)),
            Self::NativeFunc(n, f) => Self::NativeFunc(n, Arc::clone(f)),
            Self::AsyncNativeFunc(n, f) => Self::AsyncNativeFunc(n, Arc::clone(f)),
            Self::NativeMacro(n, f) => Self::NativeMacro(n, Arc::clone(f)),
            Self::AsyncNativeMacro(n, f) => Self::AsyncNativeMacro(n, Arc::clone(f)),
        }
    }
}

impl<T> Callable<T> {
    pub fn is_macro(&self) -> bool {
        matches!(&self, Callable::Macro(_))
            || matches!(&self, Callable::NativeMacro(..))
            || matches!(&self, Callable::AsyncNativeMacro(..))
    }
}

pub trait ForeignObject: std::any::Any + Debug {}

pub enum LispValue<T> {
    Nil,
    Symbol(Symbol),
    Int(i64),
    Float(f64),
    String(Arc<str>),
    List(List<T>),
    Callable(Callable<T>),
    Error(RuntimeError),
    Foreign(Box<dyn ForeignObject + Send + Sync>),
}

impl<T> LispValue<T> {
    pub fn get_pretty_name(&self) -> &'static str {
        match self {
            LispValue::Nil => "Nil",
            LispValue::Symbol(_) => "Symbol",
            LispValue::Int(_) => "Int",
            LispValue::Float(_) => "Float",
            LispValue::String(_) => "String",
            LispValue::List(_) => "List",
            LispValue::Callable(c) if c.is_macro() => "Macro",
            LispValue::Callable(_) => "Func",
            LispValue::Error(_) => "Error",
            LispValue::Foreign(_) => "Foreign",
        }
    }

    pub fn remove_nil(&self) -> Option<&Self> {
        if let LispValue::Nil = &self {
            None
        } else {
            Some(self)
        }
    }

    fn serialize_internal(&self, p: &Position, quoted: bool) -> Option<SExpression> {
        Some(match self {
            LispValue::Nil => SExpression::Nil,
            LispValue::Symbol(s) => SExpression::Symbol(Arc::clone(&s.0)),
            LispValue::Int(i) => SExpression::Int(*i),
            LispValue::Float(f) => SExpression::Float(*f),
            LispValue::String(s) => SExpression::String(Arc::clone(s)),
            LispValue::List(l) => {
                if quoted {
                    SExpression::Expr(
                        p.clone(),
                        l.iter()
                            .filter_map(|i| i.serialize_internal(p, true))
                            .collect(),
                    )
                } else {
                    SExpression::Quote(
                        p.clone(),
                        l.iter()
                            .filter_map(|i| i.serialize_internal(p, true))
                            .collect(),
                    )
                }
            }
            LispValue::Callable(c) => match c {
                Callable::NativeFunc(n, _) | Callable::AsyncNativeFunc(n, _) => {
                    SExpression::Expr(p.clone(), [SExpression::Symbol((*n).into())].to_vec())
                }
                Callable::Func(f) if f.env.is_none() => SExpression::Expr(
                    p.clone(),
                    [
                        &[
                            SExpression::Symbol("function".into()),
                            SExpression::Expr(p.clone(), f.args.clone()),
                        ][..],
                        &f.body.clone(),
                    ]
                    .concat()
                    .to_vec(),
                ),
                Callable::Func(_) => None?,
                Callable::Macro(_) => None?,
                Callable::NativeMacro(..) | Callable::AsyncNativeMacro(..) => None?,
            },
            LispValue::Error(err) => lisp_lit! {
                {p};
                ((sym "error")
                 {match err.kind() {
                     RuntimeErrorKind::InvalidArgument(_) => None?,
                     _ => None?
                 }}
                 {SExpression::Expr(
                     p.clone(),
                     err.stack_trace()
                         .iter()
                         .map(|sf| {
                             lisp_lit!{ {p};
                                 ((sym sf.name_clone())
                                  ([sf.position().file_clone()]
                                   {SExpression::Int(sf.position().line().try_into().unwrap())}
                                   {SExpression::Int(sf.position().col().try_into().unwrap())}))
                             }
                         })
                         .collect(),
                 )})
            },
            LispValue::Foreign(_) => None?,
        })
    }

    pub fn serialize(&self, p: &Position, direct: bool) -> Option<SExpression> {
        self.serialize_internal(p, direct)
    }
}

impl<T> From<Symbol> for LispValue<T> {
    fn from(s: Symbol) -> Self {
        Self::Symbol(s)
    }
}

impl<T> From<i64> for LispValue<T> {
    fn from(i: i64) -> Self {
        Self::Int(i)
    }
}

impl<T> From<f64> for LispValue<T> {
    fn from(f: f64) -> Self {
        Self::Float(f)
    }
}

impl<T> From<String> for LispValue<T> {
    fn from(s: String) -> Self {
        Self::String(s.into())
    }
}

impl<T> From<&str> for LispValue<T> {
    fn from(s: &str) -> Self {
        Self::String(s.into())
    }
}

impl<T> From<&Arc<str>> for LispValue<T> {
    fn from(s: &Arc<str>) -> Self {
        Self::String(Arc::clone(s))
    }
}

impl<T> From<Arc<str>> for LispValue<T> {
    fn from(s: Arc<str>) -> Self {
        Self::String(s)
    }
}

impl<T> From<List<T>> for LispValue<T> {
    fn from(l: List<T>) -> Self {
        Self::List(l)
    }
}

impl<T> FromIterator<LispValue<T>> for LispValue<T> {
    fn from_iter<I: IntoIterator<Item = LispValue<T>>>(iter: I) -> Self {
        Self::List(iter.into_iter().collect())
    }
}

impl<T> FromIterator<Arc<LispValue<T>>> for LispValue<T> {
    fn from_iter<I: IntoIterator<Item = Arc<LispValue<T>>>>(iter: I) -> Self {
        Self::List(iter.into_iter().collect())
    }
}

impl<T> From<RuntimeError> for LispValue<T> {
    fn from(e: RuntimeError) -> Self {
        Self::Error(e)
    }
}

impl<T> From<Callable<T>> for LispValue<T> {
    fn from(c: Callable<T>) -> Self {
        Self::Callable(c)
    }
}

impl<T> Debug for LispValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut st = f.debug_struct("LispValue");
        match self {
            LispValue::Nil => st.field("nil", &()).finish(),
            LispValue::Symbol(s) => st.field("symbol", s).finish(),
            LispValue::Int(i) => st.field("int", i).finish(),
            LispValue::Float(fl) => st.field("float", fl).finish(),
            LispValue::String(s) => st.field("string", s).finish(),
            LispValue::List(l) => st.field("list", l).finish(),
            LispValue::Callable(_) => st.field("function", &()).finish(),
            LispValue::Error(e) => st.field("error", e).finish(),
            LispValue::Foreign(_) => st.field("foreign_value", &()).finish(),
        }
    }
}

pub struct EnvironmentBuilder<T> {
    name: Option<Arc<str>>,
    parent: Option<SharedContainer<Environment<T>>>,
    variables: Option<HashMap<Symbol, MutVarRef<T>>>,
    functions: Option<HashMap<Symbol, MutFuncRef<T>>>,
    entry_position: Position,
    modules: Option<HashMap<Symbol, Environment<T>>>,
    source_file_location: Option<PathBuf>,
    documentation: Option<Arc<str>>,
    is_global: bool,
}

impl<T> EnvironmentBuilder<T> {
    pub fn new<N: Into<Arc<str>>>(name: N, entry_position: Position) -> Self {
        EnvironmentBuilder {
            name: Some(name.into()),
            parent: None,
            entry_position,
            variables: None,
            functions: None,
            modules: None,
            source_file_location: None,
            documentation: None,
            is_global: true,
        }
    }

    pub fn new_from_parent<N: Into<Arc<str>>>(
        env: SharedContainer<Environment<T>>,
        name: Option<N>,
        entry_position: Position,
    ) -> Self {
        EnvironmentBuilder {
            name: name.map(N::into),
            parent: Some(env),
            entry_position,
            variables: None,
            functions: None,
            modules: None,
            source_file_location: None,
            documentation: None,
            is_global: false,
        }
    }

    pub fn set_variables(mut self, variables: HashMap<Symbol, MutVarRef<T>>) -> Self {
        self.variables = Some(variables);
        self
    }

    pub fn set_functions(mut self, functions: HashMap<Symbol, MutFuncRef<T>>) -> Self {
        self.functions = Some(functions);
        self
    }

    pub fn set_modules(mut self, modules: HashMap<Symbol, Environment<T>>) -> Self {
        self.modules = Some(modules);
        self
    }

    pub fn set_source_file_location(mut self, source_file_location: PathBuf) -> Self {
        self.source_file_location = Some(source_file_location);
        self
    }

    pub fn set_documentation<IS: Into<Arc<str>>>(mut self, documentation: IS) -> Self {
        self.documentation = Some(documentation.into());
        self
    }

    pub fn set_is_global(mut self, is_global: bool) -> Self {
        self.is_global = is_global;
        self
    }

    pub fn build(self) -> Environment<T> {
        assert!(
            !(self.is_global && self.parent.is_some()),
            "environment cannot be global and the child of another environment"
        );

        Environment {
            name: self.name,
            parent: self.parent,
            variables: self.variables.unwrap_or_default(),
            functions: self.functions.unwrap_or_default(),
            entry_position: self.entry_position,
            modules: self.modules.unwrap_or_default(),
            source_file_location: self.source_file_location,
            documentation: self.documentation,
            is_global: self.is_global,
        }
    }
}

pub struct Environment<T> {
    name: Option<Arc<str>>,
    parent: Option<SharedContainer<Environment<T>>>,
    variables: HashMap<Symbol, MutVarRef<T>>,
    functions: HashMap<Symbol, MutFuncRef<T>>,
    entry_position: Position,
    modules: HashMap<Symbol, Environment<T>>,
    source_file_location: Option<PathBuf>,
    documentation: Option<Arc<str>>,
    is_global: bool,
}

impl<'a, T: 'a> Environment<T> {
    pub fn get_env(
        lock: &'a SharedContainer<Environment<T>>,
        pos: &Position,
    ) -> Result<RwLockReadGuard<'a, Environment<T>>, RuntimeError> {
        lock.read()
            .map_err(convert_to_error(&"<internal: get_env>", pos))
    }

    pub fn get_env_mut(
        lock: &'a SharedContainer<Environment<T>>,
        pos: &Position,
    ) -> Result<RwLockWriteGuard<'a, Environment<T>>, RuntimeError> {
        lock.write()
            .map_err(convert_to_error(&"<internal: get_env>", pos))
    }

    pub fn get_global(
        env: SharedContainer<Environment<T>>,
        pos: &Position,
    ) -> Result<SharedContainer<Environment<T>>, RuntimeError> {
        let envinner = Self::get_env(&env, pos)?;

        if envinner.is_global {
            drop(envinner);
            return Ok(env);
        }

        let fname = envinner.get_environment_name(pos)?;

        if let Some(parent) = &envinner.parent {
            let parent_lock = parent.read().map_err(convert_to_error(&fname, pos))?;

            if parent_lock.is_global {
                return Ok(Arc::clone(parent));
            }

            return Self::get_global(Arc::clone(parent), pos);
        }

        panic!("environment constructed without a chain to the global environment");
    }
}

impl<T> Environment<T> {
    fn find_variable_internal(
        &self,
        arg_name: &Symbol,
        frame_name: &Arc<str>,
        call_position: &Position,
    ) -> Result<Option<Arc<LispValue<T>>>, RuntimeError> {
        if let Some(var) = self.variables.get(arg_name) {
            let var_int =
                var.read()
                    .map_err(man_convert_to_err(frame_name, call_position, &|_| {
                        error::RuntimeErrorKind::VariableAccess(arg_name.0.to_owned())
                    }))?;

            Ok(Some(var_int.clone()))
        } else if let Some(parent) = &self.parent {
            let parent =
                parent
                    .read()
                    .map_err(man_convert_to_err(frame_name, call_position, &|_| {
                        error::RuntimeErrorKind::VariableAccess(arg_name.0.to_owned())
                    }))?;

            parent.find_variable_internal(arg_name, frame_name, call_position)
        } else {
            Ok(None)
        }
    }

    pub fn find_variable(
        &self,
        arg_name: &Symbol,
        call_position: &Position,
    ) -> Result<Option<Arc<LispValue<T>>>, RuntimeError> {
        let frame_name = self.get_environment_name(call_position)?;
        self.find_variable_internal(arg_name, &frame_name, call_position)
    }

    fn find_function_internal(
        &self,
        arg_name: &Symbol,
        frame_name: &Arc<str>,
        call_position: &Position,
    ) -> Result<Option<Callable<T>>, RuntimeError> {
        if let Some((mod_name, fn_name)) = arg_name.0.split_once("::") {
            if let Some(module) = self.modules.get(&Symbol(mod_name.into())) {
                module.find_function_internal(&Symbol(fn_name.into()), frame_name, call_position)
            } else {
                Ok(None)
            }
        } else if let Some(var) = self.functions.get(arg_name) {
            let var_int =
                var.read()
                    .map_err(man_convert_to_err(frame_name, call_position, &|_| {
                        error::RuntimeErrorKind::FunctionAccess(arg_name.0.to_owned())
                    }))?;

            Ok(Some(var_int.clone()))
        } else if let Some(parent) = &self.parent {
            let parent =
                parent
                    .read()
                    .map_err(man_convert_to_err(frame_name, call_position, &|_| {
                        error::RuntimeErrorKind::FunctionAccess(arg_name.0.to_owned())
                    }))?;

            parent.find_function_internal(arg_name, frame_name, call_position)
        } else {
            Ok(None)
        }
    }

    pub fn find_function(
        &self,
        arg_name: &Symbol,
        call_position: &Position,
    ) -> Result<Option<Callable<T>>, RuntimeError> {
        let frame_name = self.get_environment_name(call_position)?;
        self.find_function_internal(arg_name, &frame_name, call_position)
    }

    pub fn get_environment_name(&self, pos: &Position) -> Result<Arc<str>, RuntimeError> {
        match (&self.name, &self.parent) {
            (Some(name), _) => Ok(name.clone()),
            (_, Some(parent)) => parent
                .read()
                .map_err(convert_to_error(&"<internal: get_environment_name>", pos))?
                .get_environment_name(pos),
            _ => Ok("*global*".into()),
        }
    }

    pub fn generate_err<U, I: Into<error::RuntimeErrorKind>>(
        &self,
        err: I,
    ) -> Result<U, RuntimeError> {
        let name = self.get_environment_name(&self.entry_position)?;

        Err(RuntimeError::new(
            err.into(),
            name,
            self.entry_position.clone(),
        ))
    }

    pub fn generate_err_pos<U, I: Into<error::RuntimeErrorKind>>(
        &self,
        err: I,
        pos: Position,
    ) -> Result<U, RuntimeError> {
        let name = self.get_environment_name(&self.entry_position)?;

        Err(RuntimeError::new(err.into(), name, pos))
    }

    pub fn convert_err_kind<'a, I: Into<error::RuntimeErrorKind> + 'a>(
        &'a self,
        pos: Option<&'a Position>,
    ) -> impl Fn(I) -> RuntimeError + 'a {
        self.map_err_kind(I::into, pos)
    }

    pub fn map_err_kind<'a, E, F: Fn(E) -> error::RuntimeErrorKind + 'a>(
        &'a self,
        mapper: F,
        pos: Option<&'a Position>,
    ) -> impl Fn(E) -> RuntimeError + 'a {
        let pos_ref = pos.unwrap_or(&self.entry_position);

        move |e| {
            let name = match self.get_environment_name(pos_ref) {
                Ok(n) => n,
                Err(e) => return e,
            };

            RuntimeError::new((mapper)(e), name, pos_ref.clone())
        }
    }

    pub fn set_function(&mut self, name: Symbol, func: Callable<T>) {
        self.functions.insert(name, RwLock::new(func));
    }

    fn set_variable_internal(
        &mut self,
        name: &Symbol,
        value: &Arc<LispValue<T>>,
        frame_name: &Arc<str>,
        call_position: &Position,
    ) -> Result<bool, RuntimeError> {
        if let Some(var) = self.variables.get(name) {
            let mut var_int =
                var.write()
                    .map_err(man_convert_to_err(frame_name, call_position, &|_| {
                        error::RuntimeErrorKind::SetVariableAccess(name.0.to_owned())
                    }))?;

            *var_int = Arc::clone(value);

            Ok(true)
        } else if let Some(parent) = &self.parent {
            let mut parent =
                parent
                    .write()
                    .map_err(man_convert_to_err(frame_name, call_position, &|_| {
                        error::RuntimeErrorKind::SetVariableAccess(name.0.to_owned())
                    }))?;

            parent.set_variable_internal(name, value, frame_name, call_position)
        } else {
            Ok(false)
        }
    }

    pub fn set_variable(
        &mut self,
        name: Symbol,
        value: Arc<LispValue<T>>,
        call_position: &Position,
    ) -> Result<(), RuntimeError> {
        let frame_name = self.get_environment_name(call_position)?;

        if !self.set_variable_internal(&name, &value, &frame_name, call_position)? {
            self.variables.insert(name, RwLock::new(value));
        }

        Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub enum VmSExpr<'a> {
    Nil,
    Symbol(&'a str),
    Int(i64),
    Float(f64),
    FuncSymbol(&'a str),
    String(&'a str),
    QuoteSymbol(&'a str),
    UnquoteSymbol(&'a str),
    ListSpliceSymbol(&'a str),
    Expr(&'a [SExpression]),
    Quote(&'a [SExpression]),
    Backquote(&'a [SExpression]),
    UnquoteExpression(&'a [SExpression]),
    ListSpliceExpr(&'a [SExpression]),
}

pub fn as_matcher(sexpr: &SExpression) -> VmSExpr<'_> {
    match sexpr {
        SExpression::Nil => VmSExpr::Nil,
        SExpression::Symbol(s) => VmSExpr::Symbol(s),
        SExpression::Int(i) => VmSExpr::Int(*i),
        SExpression::Float(f) => VmSExpr::Float(*f),
        SExpression::FuncSymbol(f) => VmSExpr::FuncSymbol(f),
        SExpression::String(s) => VmSExpr::String(s),
        SExpression::QuoteSymbol(s) => VmSExpr::QuoteSymbol(s),
        SExpression::UnquoteSymbol(s) => VmSExpr::UnquoteSymbol(s),
        SExpression::ListSpliceSymbol(s) => VmSExpr::ListSpliceSymbol(s),
        SExpression::Expr(_, e) => VmSExpr::Expr(e),
        SExpression::Quote(_, e) => VmSExpr::Quote(e),
        SExpression::Backquote(_, e) => VmSExpr::Backquote(e),
        SExpression::UnquoteExpression(_, e) => VmSExpr::UnquoteExpression(e),
        SExpression::ListSpliceExpr(_, e) => VmSExpr::ListSpliceExpr(e),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use serpentine_macro::declare_lisp_func;

    #[test]
    fn macro_expansions() {
        declare_lisp_func!(local get_ctx_2 "get-ctx-2" (ctx: u8, _pos, _env) {
            LispValue::Int((*ctx).into()).into()
        });

        declare_lisp_func!(local ignore_ctx "ignore-ctx" (_pos, _env) LispValue::Nil.into());

        declare_lisp_func!(local do_the_thing_2 "do-the-thing-2" (_pos, _env, arg1: Int) {
            let res = arg1 + 3;

            LispValue::Int(res).into()
        });

        declare_lisp_func!(local count_args "count-args" (_pos, _env, &rest args) {
            LispValue::Int(args.len().try_into().unwrap()).into()
        });

        declare_lisp_func!(local get_ctx "get-ctx" (ctx: u8, _pos, _env, &rest _args) {
            LispValue::Int((*ctx).into()).into()
        });

        declare_lisp_func!(local do_the_thing "do-the-thing" (_pos, _env, arg1: Int) {
            let res = arg1 + 3;

            LispValue::Int(res).into()
        });

        declare_lisp_func!(local async async_thing "async-thing" (_pos, _env) {
            _ = tokio::time::sleep(std::time::Duration::from_millis(100)).await;

            LispValue::Nil.into()
        });

        declare_lisp_func!(local docs_string "docs-string" (_pos, _env) "Here are some docs" LispValue::Nil.into());
        let Callable::NativeFunc(_, docs_string_2) = docs_string::new() else {
            panic!("Expected native func");
        };
        assert_eq!(&*docs_string_2.docs().unwrap(), "Here are some docs");
    }
}
