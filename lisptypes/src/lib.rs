use std::fmt::{Debug, Formatter};
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
        std::fmt::Display::fmt(&self.error, formatter)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub trait ValueTypes {
    type ValueRef: Deref<Target = Value<Self>> + Debug;
    type StringRef: Deref<Target = str>;
}

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
pub struct ValueCons<T>
where
    T: ValueTypes + ?Sized,
{
    pub car: T::ValueRef,
    pub cdr: T::ValueRef,
}

impl<T1, T2> PartialEq<ValueCons<T2>> for ValueCons<T1>
where
    T1: ValueTypes,
    T2: ValueTypes,
{
    fn eq(&self, other: &ValueCons<T2>) -> bool {
        *self.car == *other.car && *self.cdr == *other.cdr
    }
}

#[derive(Debug, PartialEq)]
pub struct ValueBool(pub bool);

#[derive(Debug)]
pub struct ValueString<S: Deref<Target = str>>(pub S);

impl<S1, S2> PartialEq<ValueString<S2>> for ValueString<S1>
where
    S1: Deref<Target = str>,
    S2: Deref<Target = str>,
{
    fn eq(&self, rhs: &ValueString<S2>) -> bool {
        *self.0 == *rhs.0
    }
}

#[derive(Debug)]
pub enum Value<T>
where
    T: ValueTypes + ?Sized,
{
    Nil,
    Symbol(ValueSymbol<T::StringRef>),
    Cons(ValueCons<T>),
    Bool(ValueBool),
    String(ValueString<T::StringRef>),
}

impl<T1, T2> PartialEq<Value<T2>> for Value<T1>
where
    T1: ValueTypes,
    T2: ValueTypes,
{
    fn eq(&self, rhs: &Value<T2>) -> bool {
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
            Value::String(s1) => match rhs {
                Value::String(s2) => *s1 == *s2,
                _ => false,
            },
        }
    }
}

#[derive(Debug)]
pub struct ValueTypesStatic;

impl ValueTypes for ValueTypesStatic {
    type ValueRef = &'static Value<Self>;
    type StringRef = &'static str;
}

#[macro_export]
macro_rules! nil {
    () => {{
        const N: &$crate::Value<$crate::ValueTypesStatic> = &$crate::Value::Nil;
        N
    }};
}

#[macro_export]
macro_rules! sym {
    ($name:expr) => {{
        const S: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::Symbol($crate::ValueSymbol($name));
        S
    }};
}

#[macro_export]
macro_rules! cons {
    ($car:expr, $cdr:expr) => {{
        const C: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::Cons($crate::ValueCons {
                car: $car,
                cdr: $cdr,
            });
        C
    }};
}

#[macro_export]
macro_rules! bool {
    ($b:expr) => {{
        const B: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::Bool($crate::ValueBool($b));
        B
    }};
}

#[macro_export]
macro_rules! str {
    ($s:expr) => {{
        const S: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::String($crate::ValueString($s));
        S
    }};
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
        const NIL: &super::Value<super::ValueTypesStatic> = nil!();
        assert_eq!(*NIL, super::Value::<super::ValueTypesStatic>::Nil);
    }

    #[test]
    fn test_sym_macro() {
        const SYM: &super::Value<super::ValueTypesStatic> = sym!("sym");
        match &*SYM {
            super::Value::Symbol(s) => assert_eq!(s.0, "sym"),
            _ => panic!("Expected a Value::Symbol"),
        }
    }

    #[test]
    fn test_cons_macro() {
        const CONS: &super::Value<super::ValueTypesStatic> = cons!(sym!("sym"), nil!());
        match &*CONS {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::Symbol(s) => assert_eq!(s.0, "sym"),
                    _ => panic!("Expected a Value::Symbol"),
                }
                assert_eq!(*c.cdr, super::Value::<super::ValueTypesStatic>::Nil);
            }
            _ => panic!("Expected a Value::Cons"),
        }
    }

    #[test]
    fn test_bool_macro() {
        const B1: &super::Value<super::ValueTypesStatic> = bool!(true);
        match &*B1 {
            super::Value::Bool(b) => assert_eq!(b.0, true),
            _ => panic!("Expected a Value::Bool"),
        }
        const B2: &super::Value<super::ValueTypesStatic> = bool!(false);
        match &*B2 {
            super::Value::Bool(b) => assert_eq!(b.0, false),
            _ => panic!("Expected a Value::Bool"),
        }
    }

    #[test]
    fn test_str_macro() {
        const S: &super::Value<super::ValueTypesStatic> = str!("str");
        match &*S {
            super::Value::String(s) => assert_eq!(s.0, "str"),
            _ => panic!("Expected a Value::String"),
        }
    }

    #[test]
    fn test_list_macro() {
        const LIST1: &super::Value<super::ValueTypesStatic> = list!();
        assert_eq!(*LIST1, super::Value::<super::ValueTypesStatic>::Nil);

        const LIST2: &super::Value<super::ValueTypesStatic> = list!(sym!("sym1"));
        match &*LIST2 {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::Symbol(s) => assert_eq!(s.0, "sym1"),
                    _ => panic!("Expected a Value::Symbol"),
                }
                assert_eq!(*c.cdr, super::Value::<super::ValueTypesStatic>::Nil);
            }
            _ => panic!("Expected a Value::Cons"),
        }

        const LIST3: &super::Value<super::ValueTypesStatic> = list!(sym!("sym1"), sym!("sym2"));
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
                        assert_eq!(*c.cdr, super::Value::<super::ValueTypesStatic>::Nil);
                    }
                    _ => panic!("Expected a Value::Cons"),
                }
            }
            _ => panic!("Expected a Value::Cons"),
        }

        const LIST4: &super::Value<super::ValueTypesStatic> =
            list!(sym!("sym1"), sym!("sym2"), sym!("sym3"));
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
                                assert_eq!(*c.cdr, super::Value::<super::ValueTypesStatic>::Nil);
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

    #[test]
    fn test_eq() {
        use std::marker::PhantomData;

        #[derive(Debug)]
        struct ValueTypesString<'a> {
            phantom_lifetime: PhantomData<&'a ()>,
        }

        impl<'a> super::ValueTypes for ValueTypesString<'a> {
            type ValueRef = &'a super::Value<Self>;
            type StringRef = String;
        }

        assert_eq!(nil!(), nil!());
        assert_ne!(nil!(), sym!("sym"));

        assert_eq!(sym!("sym"), sym!("sym"));
        assert_eq!(
            sym!("sym"),
            &super::Value::<ValueTypesString>::Symbol(super::ValueSymbol("sym".to_string()))
        );
        assert_ne!(sym!("sym1"), sym!("sym2"));
        assert_ne!(
            sym!("sym1"),
            &super::Value::<ValueTypesString>::Symbol(super::ValueSymbol("sym2".to_string()))
        );
        assert_ne!(sym!("sym"), str!("sym"));
        assert_ne!(sym!("sym"), nil!());

        assert_eq!(cons!(sym!("sym"), nil!()), cons!(sym!("sym"), nil!()));
        assert_ne!(cons!(sym!("sym1"), nil!()), cons!(sym!("sym2"), nil!()));
        assert_ne!(cons!(sym!("sym"), nil!()), cons!(nil!(), nil!()));
        assert_ne!(cons!(sym!("sym"), nil!()), cons!(sym!("sym"), sym!("sym")));
        assert_ne!(cons!(sym!("sym"), nil!()), nil!());

        assert_eq!(bool!(true), bool!(true));
        assert_ne!(bool!(true), bool!(false));
        assert_ne!(bool!(true), nil!());

        assert_eq!(str!("str"), str!("str"));
        assert_eq!(
            str!("str"),
            &super::Value::<ValueTypesString>::String(super::ValueString("str".to_string()))
        );
        assert_ne!(str!("str1"), str!("str2"));
        assert_ne!(
            str!("str1"),
            &super::Value::<ValueTypesString>::String(super::ValueString("str2".to_string()))
        );
        assert_ne!(str!("str"), sym!("str"));
        assert_ne!(str!("str"), nil!());
    }
}
