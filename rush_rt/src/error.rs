use rush_pat::range::{Range};
use val::{Val, IntoVal};

#[derive(Debug, Clone, PartialEq, IntoVal)]
pub enum RuntimeError {
    ParseError(::rush_parser::parse::ParseError),
    InvalidRange(Range, &'static str),
    InvalidRangeVal(Box<Val>, &'static str),
    InvalidRegex(String, &'static str),
    InvalidRegexVal(Box<Val>, &'static str),
    BadValType(Box<Val>, &'static str),
    IndexOutOfRange{len: usize, idx: i64},
    InvalidIndex(Box<Val>, &'static str),
    KeyNotFound{keys: Vec<String>, idx: String},
    UnboundVariable(String),
    InvalidIdentifier(String),
    CustomError(Vec<Val>),
}

pub type Res<T> = Result<T, RuntimeError>;
