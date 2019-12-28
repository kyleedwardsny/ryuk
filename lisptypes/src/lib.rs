use std::borrow::{Borrow, BorrowMut};
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub error: Box<dyn std::error::Error>,
}

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
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
    T::ValueRef: Clone,
{
    fn evaluate(&mut self, v: T::ValueRef) -> Result<T::ValueRef>;

    fn call_function(&mut self, c: &ValueCons<T>) -> Result<T::ValueRef>;
}

impl<T, E> Evaluator<T> for E
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
    E: Environment<T> + 'static,
{
    fn evaluate(&mut self, v: T::ValueRef) -> Result<T::ValueRef> {
        match v.borrow() {
            Value::Symbol(s) => self.get_value(s),
            Value::Cons(c) => self.call_function(c),
            _ => Result::Ok(v),
        }
    }

    fn call_function(&mut self, c: &ValueCons<T>) -> Result<T::ValueRef> {
        match self.evaluate(c.car.clone())?.borrow() {
            Value::Function(f) => {
                (f.function)(self as &mut (dyn Environment<T> + 'static), c.cdr.clone())
            }
            _ => Result::Err(Error::new(ErrorKind::NotAFunction, "Not a function")),
        }
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
    T1: ValueTypes,
    T2: ValueTypes,
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
            Value::Function(f1) => match rhs {
                Value::Function(f2) => f1.id == f2.id,
                _ => false,
            },
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

        let f1 = |_: &mut (dyn super::Environment<super::ValueTypesRc> + 'static),
                  _: <super::ValueTypesRc as super::ValueTypes>::ValueRef| {
            super::Result::Ok(super::Rc::new(super::Value::Nil))
        };
        let f2 = |_: &mut (dyn super::Environment<super::ValueTypesRc> + 'static),
                  _: <super::ValueTypesRc as super::ValueTypes>::ValueRef| {
            super::Result::Ok(super::Rc::new(super::Value::String(super::ValueString(
                "str".to_string(),
            ))))
        };
        let v11 = super::Rc::new(super::Value::<super::ValueTypesRc>::Function(
            super::ValueFunction {
                id: 1,
                function: Box::new(f1),
            },
        ));
        let v12 = super::Rc::new(super::Value::<super::ValueTypesRc>::Function(
            super::ValueFunction {
                id: 1,
                function: Box::new(f2),
            },
        ));
        let v21 = super::Rc::new(super::Value::<super::ValueTypesRc>::Function(
            super::ValueFunction {
                id: 2,
                function: Box::new(f1),
            },
        ));
        let v22 = super::Rc::new(super::Value::<super::ValueTypesRc>::Function(
            super::ValueFunction {
                id: 2,
                function: Box::new(f2),
            },
        ));
        assert_eq!(v11, v11);
        assert_eq!(v11, v12);
        assert_ne!(v11, v21);
        assert_ne!(v11, v22);
        assert_ne!(v11, super::Rc::new(super::Value::Nil));
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

        fn concat(
            env: &mut (dyn Environment<ValueTypesRc> + 'static),
            args: <ValueTypesRc as ValueTypes>::ValueRef,
        ) -> Result<<ValueTypesRc as ValueTypes>::ValueRef> {
            let mut arg = args;
            let mut result = String::new();

            while let Value::Cons(c) = &*arg {
                if let Value::String(s) = &*env.evaluate(c.car.clone())? {
                    result += &s.0;
                }
                arg = c.cdr.clone();
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
        let function_call = Rc::new(Value::Cons(ValueCons {
            car: Rc::new(Value::Symbol(ValueSymbol("concat".to_string()))),
            cdr: Rc::new(Value::Cons(ValueCons {
                car: Rc::new(Value::Symbol(ValueSymbol("a".to_string()))),
                cdr: Rc::new(Value::Cons(ValueCons {
                    car: Rc::new(Value::String(ValueString(", world!".to_string()))),
                    cdr: Rc::new(Value::Nil),
                })),
            })),
        }));
        assert_eq!(
            *env.evaluate(function_call).unwrap(),
            *str!("Hello, world!")
        );
    }
}
