use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub error: Box<dyn std::error::Error>,
}

impl Error {
    pub fn new(kind: ErrorKind, error: impl Into<Box<dyn std::error::Error>>) -> Error {
        Error {
            kind,
            error: error.into(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    IncorrectType,
    ValueNotDefined,
    NotAFunction,
    NoPackageForSymbol,
    IncorrectParams,
}

impl std::error::Error for Error {}

impl Display for Error {
    fn fmt(&self, formatter: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        Display::fmt(&self.error, formatter)
    }
}

pub type Result<T> = std::result::Result<T, Error>;
