use std::fmt::Formatter;
use std::ops::Deref;

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

#[derive(Debug)]
pub struct ValueSymbol<S: Deref<Target = str>>(pub S);

impl<S1, S2> PartialEq<ValueSymbol<S2>> for ValueSymbol<S1>
where
    S1: Deref<Target = str>,
    S2: Deref<Target = str>,
{
    fn eq(&self, rhs: &ValueSymbol<S2>) -> bool {
        *self.0 == *rhs.0
    }
}

#[derive(Debug)]
pub struct ValueCons<V, S>
where
    V: Deref<Target = Value<V, S>>,
    S: Deref<Target = str>,
{
    pub car: V,
    pub cdr: V,
}

impl<V1, S1, V2, S2> PartialEq<ValueCons<V2, S2>> for ValueCons<V1, S1>
where
    V1: Deref<Target = Value<V1, S1>>,
    S1: Deref<Target = str>,
    V2: Deref<Target = Value<V2, S2>>,
    S2: Deref<Target = str>,
{
    fn eq(&self, other: &ValueCons<V2, S2>) -> bool {
        *self.car == *other.car && *self.cdr == *other.cdr
    }
}

#[derive(Copy, Debug, PartialEq)]
pub struct ValueBool(pub bool);

impl Clone for ValueBool {
    fn clone(&self) -> ValueBool {
        ValueBool(self.0)
    }
}

#[derive(Debug)]
pub enum Value<V, S>
where
    V: Deref<Target = Value<V, S>>,
    S: Deref<Target = str>,
{
    Nil,
    Symbol(ValueSymbol<S>),
    Cons(ValueCons<V, S>),
    Bool(ValueBool),
}

impl<V1, S1, V2, S2> PartialEq<Value<V2, S2>> for Value<V1, S1>
where
    V1: Deref<Target = Value<V1, S1>>,
    S1: Deref<Target = str>,
    V2: Deref<Target = Value<V2, S2>>,
    S2: Deref<Target = str>,
{
    fn eq(&self, rhs: &Value<V2, S2>) -> bool {
        match self {
            Value::Nil => match rhs {
                Value::Nil => true,
                _ => false,
            },
            Value::Symbol(s1) => match rhs {
                Value::Symbol(s2) => *s1 == *s2,
                _ => false,
            },
            Value::Cons(c1) => match rhs {
                Value::Cons(c2) => *c1 == *c2,
                _ => false,
            },
            Value::Bool(b1) => match rhs {
                Value::Bool(b2) => *b1 == *b2,
                _ => false,
            },
        }
    }
}

pub type ValueStatic = Value<ValueStaticRef, &'static str>;

#[derive(Debug)]
pub struct ValueStaticRef(pub &'static ValueStatic);

impl Deref for ValueStaticRef {
    type Target = Value<ValueStaticRef, &'static str>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

#[macro_export]
macro_rules! nil {
    () => {
        $crate::ValueStaticRef(&$crate::Value::Nil)
    };
}

#[macro_export]
macro_rules! sym {
    ($name:expr) => {
        $crate::ValueStaticRef(&$crate::Value::Symbol($crate::ValueSymbol($name)))
    };
}

#[macro_export]
macro_rules! cons {
    ($car:expr, $cdr:expr) => {
        $crate::ValueStaticRef(&$crate::Value::Cons($crate::ValueCons {
            car: $car,
            cdr: $cdr,
        }))
    };
}

#[macro_export]
macro_rules! bool {
    ($b:expr) => {
        $crate::ValueStaticRef(&$crate::Value::Bool($crate::ValueBool($b)))
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
    #[test]
    fn test_nil_macro() {
        const NIL: super::ValueStaticRef = nil!();
        assert_eq!(*NIL, super::ValueStatic::Nil);
    }

    #[test]
    fn test_sym_macro() {
        const SYM: super::ValueStaticRef = sym!("sym");
        match &*SYM {
            super::Value::Symbol(s) => assert_eq!(s.0, "sym"),
            _ => panic!("Expected a Value::Symbol"),
        }
    }

    #[test]
    fn test_cons_macro() {
        const CONS: super::ValueStaticRef = cons!(sym!("sym"), nil!());
        match &*CONS {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::Symbol(s) => assert_eq!(s.0, "sym"),
                    _ => panic!("Expected a Value::Symbol"),
                }
                assert_eq!(*c.cdr, super::ValueStatic::Nil);
            }
            _ => panic!("Expected a Value::Cons"),
        }
    }

    #[test]
    fn test_bool_macro() {
        const B1: super::ValueStaticRef = bool!(true);
        match &*B1 {
            super::Value::Bool(b) => assert_eq!(b.0, true),
            _ => panic!("Expected a Value::Bool"),
        }
        const B2: super::ValueStaticRef = bool!(false);
        match &*B2 {
            super::Value::Bool(b) => assert_eq!(b.0, false),
            _ => panic!("Expected a Value::Bool"),
        }
    }

    #[test]
    fn test_list_macro() {
        const LIST1: super::ValueStaticRef = list!();
        assert_eq!(*LIST1, super::ValueStatic::Nil);

        const LIST2: super::ValueStaticRef = list!(sym!("sym1"));
        match &*LIST2 {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::Symbol(s) => assert_eq!(s.0, "sym1"),
                    _ => panic!("Expected a Value::Symbol"),
                }
                assert_eq!(*c.cdr, super::ValueStatic::Nil);
            }
            _ => panic!("Expected a Value::Cons"),
        }

        const LIST3: super::ValueStaticRef = list!(sym!("sym1"), sym!("sym2"));
        match &*LIST3 {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::Symbol(s) => assert_eq!(s.0, "sym1"),
                    _ => panic!("Expected a Value::Symbol"),
                }
                match &*c.cdr {
                    super::Value::Cons(c) => {
                        match &*c.car {
                            super::Value::Symbol(s) => assert_eq!(s.0, "sym2"),
                            _ => panic!("Expected a Value::Symbol"),
                        }
                        assert_eq!(*c.cdr, super::ValueStatic::Nil);
                    }
                    _ => panic!("Expected a Value::Cons"),
                }
            }
            _ => panic!("Expected a Value::Cons"),
        }

        const LIST4: super::ValueStaticRef = list!(sym!("sym1"), sym!("sym2"), sym!("sym3"));
        match &*LIST4 {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::Symbol(s) => assert_eq!(s.0, "sym1"),
                    _ => panic!("Expected a Value::Symbol"),
                }
                match &*c.cdr {
                    super::Value::Cons(c) => {
                        match &*c.car {
                            super::Value::Symbol(s) => assert_eq!(s.0, "sym2"),
                            _ => panic!("Expected a Value::Symbol"),
                        }
                        match &*c.cdr {
                            super::Value::Cons(c) => {
                                match &*c.car {
                                    super::Value::Symbol(s) => assert_eq!(s.0, "sym3"),
                                    _ => panic!("Expected a Value::Symbol"),
                                }
                                assert_eq!(*c.cdr, super::ValueStatic::Nil);
                            }
                            _ => panic!("Expected a Value::Cons"),
                        }
                    }
                    _ => panic!("Expected a Value::Cons"),
                }
            }
            _ => panic!("Expected a Value::Cons"),
        }
    }
}
