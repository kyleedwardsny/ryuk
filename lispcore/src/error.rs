use super::value::*;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub struct Error {
    pub kind: ValueQualifiedSymbol,
    pub fields: HashMap<ValueQualifiedSymbol, Value>,
}

impl Error {
    pub fn new(kind: ValueQualifiedSymbol, fields: HashMap<ValueQualifiedSymbol, Value>) -> Self {
        Self { kind, fields }
    }
}

impl std::error::Error for Error {}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "<ERROR {}:{}>", self.kind.package, self.kind.name)
    }
}

impl PartialEq<Error> for Error {
    fn eq(&self, rhs: &Error) -> bool {
        self.kind == rhs.kind && self.fields == rhs.fields
    }
}

impl Eq for Error {}

pub type Result<T> = std::result::Result<T, Error>;

#[macro_export]
macro_rules! e_std_cond {
    ($name:expr) => {
        $crate::error::Error {
            kind: $crate::value::ValueQualifiedSymbol {
                package: "std".into(),
                name: $name.into(),
            },
            fields: ::std::collections::HashMap::new(),
        }
    };
}

#[macro_export]
macro_rules! e_program_error {
    () => {
        e_std_cond!("program-error")
    };
}

#[macro_export]
macro_rules! e_type_error {
    () => {
        e_std_cond!("type-error")
    };
}

#[macro_export]
macro_rules! e_unbound_variable {
    () => {
        e_std_cond!("unbound-variable")
    };
}

#[macro_export]
macro_rules! e_undefined_function {
    () => {
        e_std_cond!("undefined-function")
    };
}
