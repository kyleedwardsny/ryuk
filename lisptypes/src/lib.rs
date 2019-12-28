use std::borrow::{Borrow, BorrowMut};
use std::convert::TryFrom;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub error: Box<dyn std::error::Error>,
}

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    IncorrectType,
    ValueNotDefined,
    NotAFunction,
    NoPackageForValue,
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
    type ValueRef: Borrow<Value<Self>> + Debug;
    type StringRef: Borrow<str>;
    type FnRef: Fn(&mut (dyn Environment<Self> + 'static), Self::ValueRef) -> Result<Self::ValueRef>;
}

pub trait Environment<T>
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
{
    fn get_value(&self, s: &ValueSymbol<T::StringRef>) -> Result<T::ValueRef>;

    fn set_value(&mut self, s: &ValueSymbol<T::StringRef>, v: T::ValueRef) -> Result<()>;
}

pub trait Evaluator<T>
where
    T: ValueTypes + ?Sized,
{
    fn evaluate(&mut self, v: T::ValueRef) -> Result<T::ValueRef>;
}

impl<T, E> Evaluator<T> for E
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
    E: Environment<T> + 'static,
{
    fn evaluate(&mut self, v: T::ValueRef) -> Result<T::ValueRef> {
        (self as &mut dyn Environment<T>).evaluate(v)
    }
}

impl<T> Evaluator<T> for dyn Environment<T>
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
{
    fn evaluate(&mut self, v: T::ValueRef) -> Result<T::ValueRef> {
        match v.borrow() {
            Value::Symbol(s) => self.get_value(s),
            Value::Cons(c) => self.call_function(c),
            _ => Result::Ok(v),
        }
    }
}

impl<T> dyn Environment<T>
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
{
    fn call_function(&mut self, c: &ValueCons<T>) -> Result<T::ValueRef> {
        match self.evaluate(c.car.clone())?.borrow() {
            Value::Function(f) => (f.function)(self, c.cdr.clone()),
            _ => Result::Err(Error::new(ErrorKind::NotAFunction, "Not a function")),
        }
    }
}

pub trait LayeredEnvironmentTypes {
    type EnvironmentLayerRef: BorrowMut<dyn EnvironmentLayer<Self>>;
    type ValueTypes: ValueTypes;
}

pub struct LayeredEnvironment<T>
where
    T: LayeredEnvironmentTypes + ?Sized,
{
    pub layers: Vec<T::EnvironmentLayerRef>,
}

impl<T> Environment<T::ValueTypes> for LayeredEnvironment<T>
where
    T: LayeredEnvironmentTypes + ?Sized,
    <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef: Clone,
{
    fn get_value(
        &self,
        s: &ValueSymbol<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef>,
    ) -> Result<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef> {
        for layer in &self.layers {
            if let Option::Some(result) = layer.borrow().get_value(&s) {
                return Result::Ok(result);
            }
        }

        Result::Err(Error::new(ErrorKind::ValueNotDefined, "Value not defined"))
    }

    fn set_value(
        &mut self,
        s: &ValueSymbol<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef>,
        v: <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef,
    ) -> Result<()> {
        for layer in &mut self.layers {
            if layer.borrow_mut().set_value(s, v.clone())? {
                return Result::Ok(());
            }
        }

        Result::Err(Error::new(
            ErrorKind::NoPackageForValue,
            "No package for value",
        ))
    }
}

pub trait EnvironmentLayer<T>
where
    T: LayeredEnvironmentTypes + ?Sized,
{
    fn get_value(
        &self,
        s: &ValueSymbol<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef>,
    ) -> Option<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef>;

    fn set_value(
        &mut self,
        s: &ValueSymbol<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef>,
        v: <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef,
    ) -> Result<bool>;
}

#[derive(Debug)]
pub struct ValueSymbol<S: Borrow<str>>(pub S);

impl<S1, S2> PartialEq<ValueSymbol<S2>> for ValueSymbol<S1>
where
    S1: Borrow<str>,
    S2: Borrow<str>,
{
    fn eq(&self, rhs: &ValueSymbol<S2>) -> bool {
        self.0.borrow() == rhs.0.borrow()
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
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
{
    fn eq(&self, other: &ValueCons<T2>) -> bool {
        self.car.borrow() == other.car.borrow() && self.cdr.borrow() == other.cdr.borrow()
    }
}

#[derive(Debug, PartialEq)]
pub struct ValueBool(pub bool);

#[derive(Debug)]
pub struct ValueString<S>(pub S)
where
    S: Borrow<str>;

impl<S1, S2> PartialEq<ValueString<S2>> for ValueString<S1>
where
    S1: Borrow<str>,
    S2: Borrow<str>,
{
    fn eq(&self, rhs: &ValueString<S2>) -> bool {
        self.0.borrow() == rhs.0.borrow()
    }
}

pub struct ValueFunction<T>
where
    T: ValueTypes + ?Sized,
{
    pub id: u32, // Needed to test for equality
    pub function: T::FnRef,
}

impl<T1, T2> PartialEq<ValueFunction<T2>> for ValueFunction<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
{
    fn eq(&self, rhs: &ValueFunction<T2>) -> bool {
        self.id == rhs.id
    }
}

impl<T> Debug for ValueFunction<T>
where
    T: ValueTypes + ?Sized,
{
    fn fmt(&self, _fmt: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        std::result::Result::Ok(())
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
    Function(ValueFunction<T>),
}

macro_rules! try_from_value {
    ($l:lifetime, $t:ident, $out:ty, $match:pat => $result:expr) => {
        impl<$l, $t> TryFrom<&$l Value<$t>> for $out
        where
            $t: ValueTypes + ?Sized,
        {
            type Error = Error;

            fn try_from(v: &$l Value<$t>) -> Result<Self> {
                match v {
                    $match => Result::Ok($result),
                    _ => Result::Err(Error::new(ErrorKind::IncorrectType, "Incorrect type")),
                }
            }
        }
    };

    ($t:ident, $out:ty, $match:pat => $result:expr) => {
        try_from_value!('a, $t, &'a $out, $match => $result);
    };
}

try_from_value!('a, T, (), Value::Nil => ());
try_from_value!(T, ValueSymbol<T::StringRef>, Value::Symbol(s) => s);
try_from_value!(T, ValueCons<T>, Value::Cons(c) => c);
try_from_value!(T, ValueBool, Value::Bool(b) => b);
try_from_value!(T, ValueString<T::StringRef>, Value::String(s) => s);
try_from_value!(T, ValueFunction<T>, Value::Function(f) => f);

macro_rules! from_value_type {
    ($t:ident, $in:ty, $param:ident -> $result:expr) => {
        impl<$t> From<$in> for Value<$t>
        where
            $t: ValueTypes + ?Sized,
        {
            fn from($param: $in) -> Self {
                $result
            }
        }
    };
}

from_value_type!(T, (), _n -> Value::Nil);
from_value_type!(T, ValueSymbol<T::StringRef>, s -> Value::Symbol(s));
from_value_type!(T, ValueCons<T>, c -> Value::Cons(c));
from_value_type!(T, ValueBool, b -> Value::Bool(b));
from_value_type!(T, ValueString<T::StringRef>, s -> Value::String(s));
from_value_type!(T, ValueFunction<T>, f -> Value::Function(f));

macro_rules! eq_match {
    ($lhs: expr, $rhs:expr, { $(($lpat:pat, $rpat:pat) => $result:expr,)* }) => {
        match $lhs {
            $($lpat => match $rhs {
                $rpat => $result,
                _ => false,
            },)*
        }
    };
}

impl<T1, T2> PartialEq<Value<T2>> for Value<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
{
    fn eq(&self, rhs: &Value<T2>) -> bool {
        eq_match!(self, rhs, {
            (Value::Nil, Value::Nil) => true,
            (Value::Symbol(s1), Value::Symbol(s2)) => s1 == s2,
            (Value::Cons(c1), Value::Cons(c2)) => c1 == c2,
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::String(s1), Value::String(s2)) => s1 == s2,
            (Value::Function(f1), Value::Function(f2)) => f1 == f2,
        })
    }
}

impl<T1, T2> From<&Value<T1>> for Value<T2>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    Value<T2>: Into<<T2 as ValueTypes>::ValueRef>,
    T1::StringRef: Into<T2::StringRef> + Clone,
{
    fn from(v: &Value<T1>) -> Self {
        match v.borrow() {
            Value::Nil => Value::Nil,
            Value::Symbol(ValueSymbol(s)) => Value::Symbol(ValueSymbol((*s).clone().into())),
            Value::Cons(ValueCons { car, cdr }) => Value::Cons(ValueCons {
                car: Into::<Value<T2>>::into(car.borrow()).into(),
                cdr: Into::<Value<T2>>::into(cdr.borrow()).into(),
            }),
            Value::Bool(ValueBool(b)) => Value::Bool(ValueBool(*b)),
            Value::String(ValueString(s)) => Value::String(ValueString((*s).clone().into())),
            Value::Function(_) => panic!("Cannot move functions across value type boundaries"),
        }
    }
}

pub fn value_type_convert<T1, T2>(v: T1::ValueRef) -> T2::ValueRef
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    T1::ValueRef: Into<Value<T2>>,
    Value<T2>: Into<<T2 as ValueTypes>::ValueRef>,
{
    Into::<Value<T2>>::into(v).into()
}

pub struct LispList<T>
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
{
    ptr: T::ValueRef,
}

impl<T> LispList<T>
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
{
    pub fn new(ptr: T::ValueRef) -> Self {
        Self { ptr }
    }

    pub fn take(self) -> T::ValueRef {
        self.ptr
    }
}

impl<T> Iterator for LispList<T>
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
{
    type Item = Result<T::ValueRef>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.ptr.borrow() {
            Value::Nil => Option::None,
            Value::Cons(c) => {
                let car = c.car.clone();
                let cdr = c.cdr.clone();
                self.ptr = cdr;
                Option::Some(Result::Ok(car))
            }
            _ => Option::Some(Result::Err(Error::new(
                ErrorKind::IncorrectType,
                "Incorrect type",
            ))),
        }
    }
}

#[derive(Debug)]
pub struct ValueTypesRc;

impl ValueTypes for ValueTypesRc {
    type ValueRef = Rc<Value<Self>>;
    type StringRef = String;
    type FnRef = Box<
        dyn Fn(&mut (dyn Environment<Self> + 'static), Self::ValueRef) -> Result<Self::ValueRef>,
    >;
}

pub struct LayeredEnvironmentTypesRc;

impl LayeredEnvironmentTypes for LayeredEnvironmentTypesRc {
    type EnvironmentLayerRef = Box<dyn EnvironmentLayer<Self>>;
    type ValueTypes = ValueTypesRc;
}

#[derive(Debug)]
pub struct ValueTypesStatic;

impl ValueTypes for ValueTypesStatic {
    type ValueRef = &'static Value<Self>;
    type StringRef = &'static str;
    type FnRef = &'static dyn Fn(
        &mut (dyn Environment<Self> + 'static),
        Self::ValueRef,
    ) -> Result<Self::ValueRef>;
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

    fn static_f1(
        _: &mut (dyn super::Environment<super::ValueTypesRc> + 'static),
        _: <super::ValueTypesRc as super::ValueTypes>::ValueRef,
    ) -> super::Result<<super::ValueTypesRc as super::ValueTypes>::ValueRef> {
        super::Result::Ok(super::Rc::new(super::Value::Nil))
    }

    fn static_f2(
        _: &mut (dyn super::Environment<super::ValueTypesRc> + 'static),
        _: <super::ValueTypesRc as super::ValueTypes>::ValueRef,
    ) -> super::Result<<super::ValueTypesRc as super::ValueTypes>::ValueRef> {
        super::Result::Ok(super::Rc::new(super::Value::String(super::ValueString(
            "str".to_string(),
        ))))
    }

    #[test]
    fn test_eq() {
        assert_eq!(nil!(), nil!());
        assert_ne!(nil!(), sym!("sym"));

        assert_eq!(sym!("sym"), sym!("sym"));
        assert_eq!(
            sym!("sym"),
            &super::Value::<super::ValueTypesRc>::Symbol(super::ValueSymbol("sym".to_string()))
        );
        assert_ne!(sym!("sym1"), sym!("sym2"));
        assert_ne!(
            sym!("sym1"),
            &super::Value::<super::ValueTypesRc>::Symbol(super::ValueSymbol("sym2".to_string()))
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
            &super::Value::<super::ValueTypesRc>::String(super::ValueString("str".to_string()))
        );
        assert_ne!(str!("str1"), str!("str2"));
        assert_ne!(
            str!("str1"),
            &super::Value::<super::ValueTypesRc>::String(super::ValueString("str2".to_string()))
        );
        assert_ne!(str!("str"), sym!("str"));
        assert_ne!(str!("str"), nil!());

        let v11 = super::Rc::new(super::Value::<super::ValueTypesRc>::Function(
            super::ValueFunction {
                id: 1,
                function: Box::new(static_f1),
            },
        ));
        let v12 = super::Rc::new(super::Value::<super::ValueTypesRc>::Function(
            super::ValueFunction {
                id: 1,
                function: Box::new(static_f2),
            },
        ));
        let v21 = super::Rc::new(super::Value::<super::ValueTypesRc>::Function(
            super::ValueFunction {
                id: 2,
                function: Box::new(static_f1),
            },
        ));
        let v22 = super::Rc::new(super::Value::<super::ValueTypesRc>::Function(
            super::ValueFunction {
                id: 2,
                function: Box::new(static_f2),
            },
        ));
        assert_eq!(v11, v11);
        assert_eq!(v11, v12);
        assert_ne!(v11, v21);
        assert_ne!(v11, v22);
        assert_ne!(v11, super::Rc::new(super::Value::Nil));
    }

    #[test]
    fn test_value_type_convert() {
        use super::*;

        let l: <ValueTypesRc as ValueTypes>::ValueRef =
            value_type_convert::<ValueTypesStatic, ValueTypesRc>(list!(
                sym!("sym"),
                bool!(true),
                str!("str")
            ));
        match l.borrow() {
            Value::Cons(c) => {
                match c.car.borrow() {
                    Value::Symbol(s) => assert_eq!(s.0, "sym"),
                    _ => panic!("Expected a Value::Symbol"),
                }
                match c.cdr.borrow() {
                    Value::Cons(c) => {
                        match c.car.borrow() {
                            Value::Bool(b) => assert_eq!(b.0, true),
                            _ => panic!("Expected a Value::Bool"),
                        }
                        match c.cdr.borrow() {
                            Value::Cons(c) => {
                                match c.car.borrow() {
                                    Value::String(s) => assert_eq!(s.0, "str"),
                                    _ => panic!("Expected a Value::String"),
                                }
                                assert_eq!(*c.cdr, *nil!());
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
    fn test_try_into_value_type() {
        use super::*;
        use std::convert::TryInto;

        let v = nil!();
        assert_eq!(TryInto::<()>::try_into(v).unwrap(), ());
        assert_eq!(
            TryInto::<&ValueString<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = sym!("sym");
        assert_eq!(
            TryInto::<&ValueSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap(),
            &ValueSymbol("sym")
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = cons!(nil!(), nil!());
        assert_eq!(
            TryInto::<&ValueCons<ValueTypesStatic>>::try_into(v).unwrap(),
            &ValueCons::<ValueTypesStatic> {
                car: nil!(),
                cdr: nil!()
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = bool!(true);
        assert_eq!(
            TryInto::<&ValueBool>::try_into(v).unwrap(),
            &ValueBool(true)
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = str!("str");
        assert_eq!(
            TryInto::<&ValueString<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap(),
            &ValueString("str")
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = Value::<ValueTypesRc>::Function(ValueFunction::<ValueTypesRc> {
            id: 1,
            function: Box::new(static_f1),
        });
        assert_eq!(
            TryInto::<&ValueFunction<ValueTypesRc>>::try_into(&v).unwrap(),
            &ValueFunction::<ValueTypesRc> {
                id: 1,
                function: Box::new(static_f1)
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );
    }

    #[test]
    fn test_into_value() {
        use super::*;

        let v: Value<ValueTypesStatic> = ().into();
        assert_eq!(&v, nil!());

        let v: Value<ValueTypesStatic> = ValueSymbol("sym").into();
        assert_eq!(&v, sym!("sym"));

        let v: Value<ValueTypesStatic> = ValueCons {
            car: nil!(),
            cdr: nil!(),
        }
        .into();
        assert_eq!(&v, cons!(nil!(), nil!()));

        let v: Value<ValueTypesStatic> = ValueBool(true).into();
        assert_eq!(&v, bool!(true));

        let v: Value<ValueTypesStatic> = ValueString("str").into();
        assert_eq!(&v, str!("str"));

        let v: Value<ValueTypesRc> = ValueFunction::<ValueTypesRc> {
            id: 1,
            function: Box::new(static_f1),
        }
        .into();
        assert_eq!(
            v,
            Value::<ValueTypesRc>::Function(ValueFunction {
                id: 1,
                function: Box::new(static_f1)
            })
        );
    }

    #[test]
    fn test_lisp_list() {
        use super::*;

        let mut i = LispList::<ValueTypesStatic>::new(list!(sym!("sym"), bool!(true), str!("str")));
        assert_eq!(i.next().unwrap().unwrap(), sym!("sym"));
        assert_eq!(i.next().unwrap().unwrap(), bool!(true));
        assert_eq!(i.next().unwrap().unwrap(), str!("str"));
        assert!(i.next().is_none());

        let mut i = LispList::<ValueTypesStatic>::new(cons!(sym!("sym"), bool!(true)));
        assert_eq!(i.next().unwrap().unwrap(), sym!("sym"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let mut i = LispList::<ValueTypesStatic>::new(list!(sym!("sym"), bool!(true), str!("str")));
        assert_eq!(i.next().unwrap().unwrap(), sym!("sym"));
        assert_eq!(i.take(), list!(bool!(true), str!("str")));
    }

    struct SimpleLayer {
        name: &'static str,
        value: <super::ValueTypesRc as super::ValueTypes>::ValueRef,
    }

    impl super::EnvironmentLayer<super::LayeredEnvironmentTypesRc> for SimpleLayer {
        fn get_value(
            &self,
            s: &super::ValueSymbol<String>,
        ) -> Option<<super::ValueTypesRc as super::ValueTypes>::ValueRef> {
            if s.0 == self.name {
                Option::Some(self.value.clone())
            } else {
                Option::None
            }
        }

        fn set_value(
            &mut self,
            s: &super::ValueSymbol<String>,
            v: <super::ValueTypesRc as super::ValueTypes>::ValueRef,
        ) -> super::Result<bool> {
            if s.0 == self.name {
                self.value = v;
                Result::Ok(true)
            } else {
                Result::Ok(false)
            }
        }
    }

    fn make_test_env() -> super::LayeredEnvironment<super::LayeredEnvironmentTypesRc> {
        use super::*;
        use std::convert::TryInto;

        fn concat(
            env: &mut (dyn Environment<ValueTypesRc> + 'static),
            args: <ValueTypesRc as ValueTypes>::ValueRef,
        ) -> Result<<ValueTypesRc as ValueTypes>::ValueRef> {
            let mut result = String::new();

            for try_item in LispList::<ValueTypesRc>::new(args) {
                let item = env.evaluate(try_item?)?;
                let s: &ValueString<String> =
                    Borrow::<Value<ValueTypesRc>>::borrow(&item).try_into()?;
                result += &s.0;
            }

            Result::Ok(Rc::new(Value::String(ValueString(result))))
        }

        let layers: Vec<Box<dyn EnvironmentLayer<LayeredEnvironmentTypesRc>>> = vec![
            Box::new(SimpleLayer {
                name: "a",
                value: Rc::new(Value::String(ValueString("Hello".to_string()))),
            }),
            Box::new(SimpleLayer {
                name: "b",
                value: Rc::new(Value::Symbol(ValueSymbol("sym".to_string()))),
            }),
            Box::new(SimpleLayer {
                name: "a",
                value: Rc::new(Value::String(ValueString("world!".to_string()))),
            }),
            Box::new(SimpleLayer {
                name: "concat",
                value: Rc::new(Value::Function(ValueFunction {
                    id: 1,
                    function: Box::new(concat),
                })),
            }),
        ];
        LayeredEnvironment { layers }
    }

    #[test]
    fn test_layered_environment_get_value() {
        use super::*;

        let env = make_test_env();
        assert_eq!(
            *env.get_value(&ValueSymbol("a".to_string())).unwrap(),
            *str!("Hello")
        );
        assert_eq!(
            *env.get_value(&ValueSymbol("b".to_string())).unwrap(),
            *sym!("sym")
        );
        assert_eq!(
            env.get_value(&ValueSymbol("c".to_string()))
                .unwrap_err()
                .kind,
            ErrorKind::ValueNotDefined
        );
    }

    #[test]
    fn test_layered_environment_set_value() {
        use super::*;

        let mut env = make_test_env();
        assert_eq!(
            *env.layers[0]
                .get_value(&ValueSymbol("a".to_string()))
                .unwrap(),
            *str!("Hello")
        );
        assert_eq!(
            *env.layers[1]
                .get_value(&ValueSymbol("b".to_string()))
                .unwrap(),
            *sym!("sym")
        );
        assert_eq!(
            *env.layers[2]
                .get_value(&ValueSymbol("a".to_string()))
                .unwrap(),
            *str!("world!")
        );

        assert!(env
            .set_value(
                &ValueSymbol("a".to_string()),
                Rc::new(Value::Bool(ValueBool(true)))
            )
            .is_ok());
        assert_eq!(
            *env.layers[0]
                .get_value(&ValueSymbol("a".to_string()))
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value(&ValueSymbol("b".to_string()))
                .unwrap(),
            *sym!("sym")
        );
        assert_eq!(
            *env.layers[2]
                .get_value(&ValueSymbol("a".to_string()))
                .unwrap(),
            *str!("world!")
        );

        assert!(env
            .set_value(
                &ValueSymbol("b".to_string()),
                Rc::new(Value::Bool(ValueBool(false)))
            )
            .is_ok());
        assert_eq!(
            *env.layers[0]
                .get_value(&ValueSymbol("a".to_string()))
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value(&ValueSymbol("b".to_string()))
                .unwrap(),
            *bool!(false)
        );
        assert_eq!(
            *env.layers[2]
                .get_value(&ValueSymbol("a".to_string()))
                .unwrap(),
            *str!("world!")
        );

        assert_eq!(
            env.set_value(
                &ValueSymbol("c".to_string()),
                Rc::new(Value::Bool(ValueBool(true)))
            )
            .unwrap_err()
            .kind,
            ErrorKind::NoPackageForValue
        );
        assert_eq!(
            *env.layers[0]
                .get_value(&ValueSymbol("a".to_string()))
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value(&ValueSymbol("b".to_string()))
                .unwrap(),
            *bool!(false)
        );
        assert_eq!(
            *env.layers[2]
                .get_value(&ValueSymbol("a".to_string()))
                .unwrap(),
            *str!("world!")
        );
    }

    #[test]
    fn test_environment_evaluate() {
        use super::*;

        let mut env = make_test_env();
        let function_call = value_type_convert::<ValueTypesStatic, ValueTypesRc>(list!(
            sym!("concat"),
            sym!("a"),
            str!(", world!")
        ));
        assert_eq!(
            *env.evaluate(function_call).unwrap(),
            *str!("Hello, world!")
        );
    }
}
