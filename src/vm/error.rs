use std::sync::Arc;

use crate::{vm::SExpression, Position};

#[derive(Debug)]
pub enum RuntimeErrorKind {
    Io(std::io::Error),
    InvalidArgument(Arc<str>),
    PoisonError,
    BorrowError,
    BorrowMutError,
    VariableAccess(Arc<str>),
    SetVariableAccess(Arc<str>),
    FunctionAccess(Arc<str>),
    InvalidFunction(SExpression),
    WrongArgumentCount {
        fname: Arc<str>,
        supplied_count: usize,
    },
    BadContext,
    WrongTypeArgument(Arc<str>, Arc<str>),
    InvalidFunctionName(Arc<str>),
    InvalidFunctionDefinition(Arc<str>)
}

impl From<std::io::Error> for RuntimeErrorKind {
    fn from(err: std::io::Error) -> Self {
        RuntimeErrorKind::Io(err)
    }
}

impl<T> From<std::sync::PoisonError<T>> for RuntimeErrorKind {
    fn from(_: std::sync::PoisonError<T>) -> Self {
        RuntimeErrorKind::PoisonError
    }
}

impl From<std::cell::BorrowMutError> for RuntimeErrorKind {
    fn from(_: std::cell::BorrowMutError) -> Self {
        RuntimeErrorKind::BorrowMutError
    }
}

impl From<std::cell::BorrowError> for RuntimeErrorKind {
    fn from(_: std::cell::BorrowError) -> Self {
        RuntimeErrorKind::BorrowError
    }
}

#[derive(Debug)]
pub struct StackTraceFrame {
    name: Arc<str>,
    position: Position,
}

impl StackTraceFrame {
    pub fn new(name: Arc<str>, position: Position) -> Self {
        Self { name, position }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn name_clone(&self) -> Arc<str> {
        Arc::clone(&self.name)
    }

    pub fn position(&self) -> &Position {
        &self.position
    }
}

#[derive(Debug)]
pub struct RuntimeError {
    kind: RuntimeErrorKind,
    stack_trace: Vec<StackTraceFrame>,
}

impl RuntimeError {
    pub fn new(kind: RuntimeErrorKind, frame_name: Arc<str>, position: Position) -> Self {
        RuntimeError {
            kind,
            stack_trace: vec![StackTraceFrame::new(frame_name, position)],
        }
    }

    pub fn kind(&self) -> &RuntimeErrorKind {
        &self.kind
    }

    pub fn stack_trace(&self) -> &[StackTraceFrame] {
        &self.stack_trace
    }

    pub(crate) fn inject_frame(&mut self, frame: StackTraceFrame) {
        self.stack_trace.push(frame);
    }
}

pub fn convert_to_error<'a, IS, E>(
    frame_name: &'a IS,
    pos: &'a Position,
) -> impl Fn(E) -> RuntimeError + 'a
where
    IS: Clone + Into<Arc<str>> + 'a,
    E: Into<RuntimeErrorKind>,
{
    |e| RuntimeError {
        kind: e.into(),
        stack_trace: vec![StackTraceFrame::new(frame_name.clone().into(), pos.clone())],
    }
}

pub fn man_convert_to_err<
    'a,
    IS: Clone + Into<Arc<str>> + 'a,
    T,
    F: Fn(T) -> RuntimeErrorKind + 'a,
>(
    frame_name: &'a IS,
    pos: &'a Position,
    mapper: &'a F,
) -> impl Fn(T) -> RuntimeError + 'a {
    |e| RuntimeError {
        kind: (mapper)(e),
        stack_trace: vec![StackTraceFrame::new(frame_name.clone().into(), pos.clone())],
    }
}

pub fn add_frame<'a>(
    frame_name: &'a Arc<str>,
    pos: &'a Position,
) -> impl Fn(RuntimeError) -> RuntimeError + 'a {
    |mut e| {
        e.stack_trace
            .push(StackTraceFrame::new(frame_name.clone().into(), pos.clone()));
        e
    }
}

#[macro_export]
macro_rules! throw_lisp {
    ($pos:expr, $err:expr) => {{
        return Err(RuntimeError {
            position: $pos.clone(),
            kind: $err,
        });
    }};
}
