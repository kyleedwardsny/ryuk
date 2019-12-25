use std::borrow::{Cow, ToOwned};
use std::convert::TryFrom;
use std::fmt::Formatter;
use std::rc::Rc;

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub error: Box<dyn std::error::Error>,
}

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    IncorrectType,
}

impl Error {
    pub fn new<E>(kind: ErrorKind, error: E) -> Error
    where
        E: Into<Box<dyn std::error::Error>>,
    {
        Error {
            kind,
            error: error.into(),
        }
    }
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        self.error.fmt(formatter)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

// Workaround for a bug in rustc. See
// https://github.com/rust-lang/rust/issues/47032.
#[derive(Debug)]
pub struct SizedHolder<T>(pub T);

impl<T: Clone> Clone for SizedHolder<T> {
    fn clone(&self) -> SizedHolder<T> {
        SizedHolder(self.0.clone())
    }
}

#[derive(Debug, PartialEq)]
pub struct ValueSymbol(pub Cow<'static, str>);

impl Clone for ValueSymbol {
    fn clone(&self) -> ValueSymbol {
        ValueSymbol(self.0.clone())
    }
}

#[derive(Debug)]
pub struct ValueCons {
    pub car: SizedHolder<ValueRef>,
    pub cdr: SizedHolder<ValueRef>,
}

impl Clone for ValueCons {
    fn clone(&self) -> ValueCons {
        ValueCons {
            car: self.car.clone(),
            cdr: self.cdr.clone(),
        }
    }
}

impl PartialEq for ValueCons {
    fn eq(&self, other: &Self) -> bool {
        *self.car.0 == *other.car.0 && *self.cdr.0 == *other.cdr.0
    }
}

#[derive(Copy, Debug, PartialEq)]
pub struct ValueBool(pub bool);

impl Clone for ValueBool {
    fn clone(&self) -> ValueBool {
        ValueBool(self.0)
    }
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Nil,
    Symbol(ValueSymbol),
    Cons(ValueCons),
    Bool(ValueBool),
}

impl ToOwned for Value {
    type Owned = Rc<Value>;

    fn to_owned(&self) -> Self::Owned {
        Rc::new(match self {
            Value::Nil => Value::Nil,
            Value::Symbol(ValueSymbol(name)) => Value::Symbol(ValueSymbol(name.clone())),
            Value::Cons(ValueCons { car, cdr }) => Value::Cons(ValueCons {
                car: SizedHolder(car.0.clone()),
                cdr: SizedHolder(cdr.0.clone()),
            }),
            Value::Bool(b) => Value::Bool(*b),
        })
    }
}

pub type ValueRef = Cow<'static, Value>;

impl From<ValueSymbol> for ValueRef {
    fn from(s: ValueSymbol) -> ValueRef {
        ValueRef::Owned(Rc::new(Value::Symbol(s)))
    }
}

impl From<ValueCons> for ValueRef {
    fn from(c: ValueCons) -> ValueRef {
        ValueRef::Owned(Rc::new(Value::Cons(c)))
    }
}

impl From<ValueBool> for ValueRef {
    fn from(b: ValueBool) -> ValueRef {
        match b.0 {
            true => ValueRef::Borrowed(&Value::Bool(ValueBool(true))),
            false => ValueRef::Borrowed(&Value::Bool(ValueBool(false))),
        }
    }
}

impl TryFrom<ValueRef> for ValueSymbol {
    type Error = Error;

    fn try_from(value: ValueRef) -> Result<Self> {
        match &*value {
            Value::Symbol(s) => Result::Ok(s.clone()),
            _ => Result::Err(Error::new(
                ErrorKind::IncorrectType,
                "Incorrect type".to_string(),
            )),
        }
    }
}

impl TryFrom<ValueRef> for ValueCons {
    type Error = Error;

    fn try_from(value: ValueRef) -> Result<Self> {
        match &*value {
            Value::Cons(c) => Result::Ok(c.clone()),
            _ => Result::Err(Error::new(
                ErrorKind::IncorrectType,
                "Incorrect type".to_string(),
            )),
        }
    }
}

impl TryFrom<ValueRef> for ValueBool {
    type Error = Error;

    fn try_from(value: ValueRef) -> Result<Self> {
        match &*value {
            Value::Bool(b) => Result::Ok(b.clone()),
            _ => Result::Err(Error::new(
                ErrorKind::IncorrectType,
                "Incorrect type".to_string(),
            )),
        }
    }
}

#[macro_export]
macro_rules! nil {
    () => {
        $crate::ValueRef::Borrowed(&$crate::Value::Nil)
    };
}

#[macro_export]
macro_rules! sym {
    ($name:literal) => {
        $crate::ValueRef::Borrowed(&$crate::Value::Symbol($crate::ValueSymbol(Cow::Borrowed(
            $name,
        ))))
    };
}

#[macro_export]
macro_rules! cons {
    ($car:expr, $cdr:expr) => {
        $crate::ValueRef::Owned(::std::rc::Rc::new($crate::Value::Cons($crate::ValueCons {
            car: $crate::SizedHolder($car),
            cdr: $crate::SizedHolder($cdr),
        })))
    };
}

#[macro_export]
macro_rules! bool {
    ($b:literal) => {
        $crate::ValueRef::Borrowed(&$crate::Value::Bool($crate::ValueBool($b)))
    };
}

#[macro_export]
macro_rules! list {
    () => { nil!() };
    ($e:expr) => { cons!($e, nil!()) };
    ($e:expr, $($es:expr),+) => { cons!($e, list!($($es),*)) };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nil_macro() {
        let nil = nil!();
        match nil {
            Cow::Borrowed(v) => assert_eq!(*v, Value::Nil),
            _ => panic!("Expected a borrowed Value"),
        }
    }

    #[test]
    fn test_sym_macro() {
        let sym = sym!("sym");
        match sym {
            Cow::Borrowed(v) => match v {
                Value::Symbol(s) => match s.0 {
                    Cow::Borrowed(name) => assert_eq!(name, "sym"),
                    _ => panic!("Expected a borrowed str"),
                },
                _ => panic!("Expected a Value::Symbol"),
            },
            _ => panic!("Expected a borrowed Value"),
        }
    }

    #[test]
    fn test_cons_macro() {
        let cons = cons!(sym!("sym"), nil!());
        match cons {
            Cow::Owned(v) => match &*v {
                Value::Cons(c) => {
                    match c.car {
                        SizedHolder(Cow::Borrowed(car)) => match car {
                            Value::Symbol(s) => assert_eq!(s.0, "sym"),
                            _ => panic!("Expected a Value::Symbol"),
                        },
                        _ => panic!("Expected a borrowed Value"),
                    }
                    match c.cdr {
                        SizedHolder(Cow::Borrowed(cdr)) => assert_eq!(*cdr, Value::Nil),
                        _ => panic!("Expected a borrowed Value"),
                    }
                }
                _ => panic!("Expected a Value::Cons"),
            },
            _ => panic!("Expected an owned Value"),
        }
    }

    #[test]
    fn test_bool_macro() {
        let b = bool!(true);
        match b {
            Cow::Borrowed(v) => match &*v {
                Value::Bool(b) => assert_eq!(b.0, true),
                _ => panic!("Expected a Value::Bool"),
            },
            _ => panic!("Expected a borrowed Value"),
        }
        let b = bool!(false);
        match b {
            Cow::Borrowed(v) => match &*v {
                Value::Bool(b) => assert_eq!(b.0, false),
                _ => panic!("Expected a Value::Bool"),
            },
            _ => panic!("Expected a borrowed Value"),
        }
    }

    #[test]
    fn test_list_macro() {
        let l = list!();
        match l {
            Cow::Borrowed(v) => assert_eq!(*v, Value::Nil),
            _ => panic!("Expected a borrowed Value"),
        }

        let l = list!(sym!("sym1"));
        match l {
            Cow::Owned(v) => match &*v {
                Value::Cons(c) => {
                    match c.car {
                        SizedHolder(Cow::Borrowed(car)) => match car {
                            Value::Symbol(s) => assert_eq!(s.0, "sym1"),
                            _ => panic!("Expected a Value::Symbol"),
                        },
                        _ => panic!("Expected a borrowed Value"),
                    }
                    match c.cdr {
                        SizedHolder(Cow::Borrowed(cdr)) => assert_eq!(*cdr, Value::Nil),
                        _ => panic!("Expected a borrowed Value"),
                    }
                }
                _ => panic!("Expected a Value::Cons"),
            },
            _ => panic!("Expected a borrowed Value"),
        }

        let l = list!(sym!("sym1"), sym!("sym2"));
        match l {
            Cow::Owned(v) => match &*v {
                Value::Cons(c) => {
                    match c.car {
                        SizedHolder(Cow::Borrowed(car)) => match &*car {
                            Value::Symbol(s) => assert_eq!(s.0, "sym1"),
                            _ => panic!("Expected a Value::Symbol"),
                        },
                        _ => panic!("Expected a borrowed Value"),
                    }
                    match &c.cdr {
                        SizedHolder(Cow::Owned(cdr)) => match &**cdr {
                            Value::Cons(c) => {
                                match c.car {
                                    SizedHolder(Cow::Borrowed(car)) => match &*car {
                                        Value::Symbol(s) => assert_eq!(s.0, "sym2"),
                                        _ => panic!("Expected a Value::Symbol"),
                                    },
                                    _ => panic!("Expected a borrowed Value"),
                                }
                                match c.cdr {
                                    SizedHolder(Cow::Borrowed(cdr)) => assert_eq!(*cdr, Value::Nil),
                                    _ => panic!("Expected a borrowed Value"),
                                }
                            }
                            _ => panic!("Expected a Value::Cons"),
                        },
                        _ => panic!("Expected an owned Value"),
                    }
                }
                _ => panic!("Expected a Value::Cons"),
            },
            _ => panic!("Expected a borrowed Value"),
        }

        let l = list!(sym!("sym1"), sym!("sym2"), sym!("sym3"));
        match l {
            Cow::Owned(v) => match &*v {
                Value::Cons(c) => {
                    match c.car {
                        SizedHolder(Cow::Borrowed(car)) => match &*car {
                            Value::Symbol(s) => assert_eq!(s.0, "sym1"),
                            _ => panic!("Expected a Value::Symbol"),
                        },
                        _ => panic!("Expected a borrowed Value"),
                    }
                    match &c.cdr {
                        SizedHolder(Cow::Owned(cdr)) => match &**cdr {
                            Value::Cons(c) => {
                                match c.car {
                                    SizedHolder(Cow::Borrowed(car)) => match &*car {
                                        Value::Symbol(s) => assert_eq!(s.0, "sym2"),
                                        _ => panic!("Expected a Value::Symbol"),
                                    },
                                    _ => panic!("Expected a borrowed Value"),
                                }
                                match &c.cdr {
                                    SizedHolder(Cow::Owned(cdr)) => match &**cdr {
                                        Value::Cons(c) => {
                                            match c.car {
                                                SizedHolder(Cow::Borrowed(car)) => match &*car {
                                                    Value::Symbol(s) => assert_eq!(s.0, "sym3"),
                                                    _ => panic!("Expected a Value::Symbol"),
                                                },
                                                _ => panic!("Expected a borrowed Value"),
                                            }
                                            match c.cdr {
                                                SizedHolder(Cow::Borrowed(cdr)) => {
                                                    assert_eq!(*cdr, Value::Nil)
                                                }
                                                _ => panic!("Expected a borrowed Value"),
                                            }
                                        }
                                        _ => panic!("Expected a Value::Cons"),
                                    },
                                    _ => panic!("Expected an owned Value"),
                                }
                            }
                            _ => panic!("Expected a Value::Cons"),
                        },
                        _ => panic!("Expected an owned Value"),
                    }
                }
                _ => panic!("Expected a Value::Cons"),
            },
            _ => panic!("Expected a borrowed Value"),
        }
    }
}
