use super::value::*;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub struct Error<T>
where
    T: ValueTypes + ?Sized,
{
    pub kind: ValueQualifiedSymbol<T::StringTypes>,
    pub fields: HashMap<ValueQualifiedSymbol<T::StringTypes>, Value<T>>,
}

impl<T> Error<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn new(
        kind: ValueQualifiedSymbol<T::StringTypes>,
        fields: HashMap<ValueQualifiedSymbol<T::StringTypes>, Value<T>>,
    ) -> Self {
        Self { kind, fields }
    }
}

impl<T> std::error::Error for Error<T> where T: ValueTypes + ?Sized {}

impl<T> Display for Error<T>
where
    T: ValueTypes + ?Sized,
{
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "<ERROR {}:{}>", self.kind.package, self.kind.name)
    }
}

impl<T> PartialEq<Error<T>> for Error<T>
where
    T: ValueTypes + ?Sized,
{
    fn eq(&self, rhs: &Error<T>) -> bool {
        self.kind == rhs.kind && self.fields == rhs.fields
    }
}

impl<T> Eq for Error<T> where T: ValueTypes + ?Sized {}

pub type Result<T, ET> = std::result::Result<T, Error<ET>>;

#[macro_export]
macro_rules! e_std_cond {
    ($t:ident, $name:expr) => {
        $crate::error::Error::<$t> {
            kind: $crate::value::ValueQualifiedSymbol::<<$t as $crate::value::ValueTypes>::StringTypes> {
                package:
                    <<$t as $crate::value::ValueTypes>::StringTypes as $crate::value::StringTypes>::string_ref_from_static_str(
                        "std",
                    ),
                name: <<$t as $crate::value::ValueTypes>::StringTypes as $crate::value::StringTypes>::string_ref_from_static_str(
                    $name,
                ),
            },
            fields: ::std::collections::HashMap::new(),
        }
    };
}

#[macro_export]
macro_rules! e_program_error {
    ($t:ident) => {
        e_std_cond!($t, "program-error")
    };
}

#[macro_export]
macro_rules! e_type_error {
    ($t:ident) => {
        e_std_cond!($t, "type-error")
    };
}

#[macro_export]
macro_rules! e_unbound_variable {
    ($t:ident) => {
        e_std_cond!($t, "unbound-variable")
    };
}

#[macro_export]
macro_rules! e_undefined_function {
    ($t:ident) => {
        e_std_cond!($t, "undefined-function")
    };
}
