use std::borrow::{Borrow, BorrowMut};
use std::cmp::Ordering;
use std::convert::{TryFrom, TryInto};
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
    NoPackageForSymbol,
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

pub trait ValueTypes
where
    for<'a> &'a <Self::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    type ValueRef: Borrow<Value<Self>> + Debug;
    type StringRef: Borrow<str>;
    type Proc: Fn(&mut (dyn Environment<Self> + 'static), Self::ValueRef) -> Result<Self::ValueRef>
        + ?Sized;
    type ProcRef: Borrow<Self::Proc>;
    type SemverTypes: SemverTypes;
}

pub trait Environment<T>
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn as_dyn_mut(&mut self) -> &mut (dyn Environment<T> + 'static);

    fn resolve_symbol(
        &self,
        s: &ValueUnqualifiedSymbol<T::StringRef>,
    ) -> Result<ValueQualifiedSymbol<T::StringRef>>;

    fn get_value_unqualified(
        &self,
        s: &ValueUnqualifiedSymbol<T::StringRef>,
    ) -> Result<T::ValueRef> {
        let s = self.resolve_symbol(s)?;
        self.get_value_qualified(&s)
    }

    fn get_value_qualified(&self, s: &ValueQualifiedSymbol<T::StringRef>) -> Result<T::ValueRef>;

    fn set_value_unqualified(
        &mut self,
        s: &ValueUnqualifiedSymbol<T::StringRef>,
        v: T::ValueRef,
    ) -> Result<()> {
        let s = self.resolve_symbol(s)?;
        self.set_value_qualified(&s, v)
    }

    fn set_value_qualified(
        &mut self,
        s: &ValueQualifiedSymbol<T::StringRef>,
        v: T::ValueRef,
    ) -> Result<()>;

    fn evaluate(&mut self, v: T::ValueRef) -> Result<T::ValueRef> {
        match v.borrow() {
            Value::UnqualifiedSymbol(s) => self.get_value_unqualified(s),
            Value::QualifiedSymbol(s) => self.get_value_qualified(s),
            Value::Cons(c) => self.call_function(c),
            _ => Result::Ok(v),
        }
    }

    fn call_function(&mut self, c: &ValueCons<T>) -> Result<T::ValueRef> {
        match self.evaluate(c.car.clone())?.borrow() {
            Value::Procedure(p) => p.proc.borrow()(self.as_dyn_mut(), c.cdr.clone()),
            _ => Result::Err(Error::new(ErrorKind::NotAFunction, "Not a function")),
        }
    }
}

impl<T> dyn Environment<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::ValueRef: Clone,
{
    pub fn map_evaluate<'a, V>(&'a mut self) -> (impl FnMut(Result<V>) -> Result<T::ValueRef> + 'a)
    where
        V: Into<T::ValueRef>,
    {
        move |v| self.evaluate(v?.into())
    }
}

pub trait LayeredEnvironmentTypes
where
    for<'a> &'a <<Self::ValueTypes as ValueTypes>::SemverTypes as SemverTypes>::Semver:
        IntoIterator<Item = &'a u64>,
{
    type EnvironmentLayerRef: BorrowMut<dyn EnvironmentLayer<Self>>;
    type ValueTypes: ValueTypes;
}

pub struct LayeredEnvironment<T>
where
    T: LayeredEnvironmentTypes + ?Sized,
    for<'a> &'a <<T::ValueTypes as ValueTypes>::SemverTypes as SemverTypes>::Semver:
        IntoIterator<Item = &'a u64>,
{
    pub layers: Vec<T::EnvironmentLayerRef>,
}

impl<T> Environment<T::ValueTypes> for LayeredEnvironment<T>
where
    T: LayeredEnvironmentTypes + ?Sized + 'static,
    for<'a> &'a <<T::ValueTypes as ValueTypes>::SemverTypes as SemverTypes>::Semver:
        IntoIterator<Item = &'a u64>,
    <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef: Clone,
{
    fn as_dyn_mut(&mut self) -> &mut (dyn Environment<T::ValueTypes> + 'static) {
        self as &mut dyn Environment<T::ValueTypes>
    }

    fn resolve_symbol(
        &self,
        s: &ValueUnqualifiedSymbol<
            <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef,
        >,
    ) -> Result<
        ValueQualifiedSymbol<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef>,
    > {
        for layer in &self.layers {
            if let Option::Some(result) = layer.borrow().resolve_symbol(s) {
                return Result::Ok(result);
            }
        }

        Result::Err(Error::new(
            ErrorKind::NoPackageForSymbol,
            "No package for symbol",
        ))
    }

    fn get_value_qualified(
        &self,
        s: &ValueQualifiedSymbol<
            <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef,
        >,
    ) -> Result<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef> {
        for layer in &self.layers {
            if let Option::Some(result) = layer.borrow().get_value_qualified(s) {
                return Result::Ok(result);
            }
        }

        Result::Err(Error::new(ErrorKind::ValueNotDefined, "Value not defined"))
    }

    fn set_value_qualified(
        &mut self,
        s: &ValueQualifiedSymbol<
            <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef,
        >,
        v: <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef,
    ) -> Result<()> {
        for layer in &mut self.layers {
            if layer.borrow_mut().set_value_qualified(s, v.clone())? {
                return Result::Ok(());
            }
        }

        Result::Err(Error::new(
            ErrorKind::NoPackageForSymbol,
            "No package for symbol",
        ))
    }
}

pub trait EnvironmentLayer<T>
where
    T: LayeredEnvironmentTypes + ?Sized,
    for<'a> &'a <<T::ValueTypes as ValueTypes>::SemverTypes as SemverTypes>::Semver:
        IntoIterator<Item = &'a u64>,
{
    fn resolve_symbol(
        &self,
        s: &ValueUnqualifiedSymbol<
            <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef,
        >,
    ) -> Option<
        ValueQualifiedSymbol<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef>,
    >;

    fn get_value_qualified(
        &self,
        s: &ValueQualifiedSymbol<
            <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef,
        >,
    ) -> Option<<<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef>;

    fn set_value_qualified(
        &mut self,
        s: &ValueQualifiedSymbol<
            <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::StringRef,
        >,
        v: <<T as LayeredEnvironmentTypes>::ValueTypes as ValueTypes>::ValueRef,
    ) -> Result<bool>;
}

#[derive(Debug)]
pub struct ValueUnqualifiedSymbol<S>(pub S)
where
    S: Borrow<str>;

impl<S> Clone for ValueUnqualifiedSymbol<S>
where
    S: Borrow<str> + Clone,
{
    fn clone(&self) -> Self {
        ValueUnqualifiedSymbol(self.0.clone())
    }
}

impl<S1, S2> PartialEq<ValueUnqualifiedSymbol<S2>> for ValueUnqualifiedSymbol<S1>
where
    S1: Borrow<str>,
    S2: Borrow<str>,
{
    fn eq(&self, rhs: &ValueUnqualifiedSymbol<S2>) -> bool {
        self.0.borrow() == rhs.0.borrow()
    }
}

#[derive(Debug)]
pub struct ValueQualifiedSymbol<S>
where
    S: Borrow<str>,
{
    pub package: S,
    pub name: S,
}

impl<S> Clone for ValueQualifiedSymbol<S>
where
    S: Borrow<str> + Clone,
{
    fn clone(&self) -> Self {
        ValueQualifiedSymbol {
            package: self.package.clone(),
            name: self.name.clone(),
        }
    }
}

impl<S1, S2> PartialEq<ValueQualifiedSymbol<S2>> for ValueQualifiedSymbol<S1>
where
    S1: Borrow<str>,
    S2: Borrow<str>,
{
    fn eq(&self, rhs: &ValueQualifiedSymbol<S2>) -> bool {
        self.package.borrow() == rhs.package.borrow() && self.name.borrow() == rhs.name.borrow()
    }
}

#[derive(Debug)]
pub struct ValueCons<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub car: T::ValueRef,
    pub cdr: T::ValueRef,
}

impl<T> Clone for ValueCons<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::ValueRef: Clone,
{
    fn clone(&self) -> Self {
        ValueCons {
            car: self.car.clone(),
            cdr: self.cdr.clone(),
        }
    }
}

impl<T1, T2> PartialEq<ValueCons<T2>> for ValueCons<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn eq(&self, other: &ValueCons<T2>) -> bool {
        self.car.borrow() == other.car.borrow() && self.cdr.borrow() == other.cdr.borrow()
    }
}

#[derive(Debug, PartialEq)]
pub struct ValueBool(pub bool);

impl Clone for ValueBool {
    fn clone(&self) -> Self {
        ValueBool(self.0)
    }
}

#[derive(Debug)]
pub struct ValueString<S>(pub S)
where
    S: Borrow<str>;

impl<S> Clone for ValueString<S>
where
    S: Borrow<str> + Clone,
{
    fn clone(&self) -> Self {
        ValueString(self.0.clone())
    }
}

impl<S1, S2> PartialEq<ValueString<S2>> for ValueString<S1>
where
    S1: Borrow<str>,
    S2: Borrow<str>,
{
    fn eq(&self, rhs: &ValueString<S2>) -> bool {
        self.0.borrow() == rhs.0.borrow()
    }
}

pub struct ValueProcedure<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub id: u32, // Needed to test for equality
    pub proc: T::ProcRef,
}

impl<T> Clone for ValueProcedure<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::ProcRef: Clone,
{
    fn clone(&self) -> Self {
        ValueProcedure {
            id: self.id,
            proc: self.proc.clone(),
        }
    }
}

impl<T1, T2> PartialEq<ValueProcedure<T2>> for ValueProcedure<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn eq(&self, rhs: &ValueProcedure<T2>) -> bool {
        self.id == rhs.id
    }
}

impl<T> Debug for ValueProcedure<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn fmt(&self, fmt: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        fmt.debug_struct("ValueProcedure")
            .field("id", &self.id)
            .finish()
    }
}

pub trait SemverTypes
where
    for<'a> &'a Self::Semver: IntoIterator<Item = &'a u64>,
{
    type Semver: ?Sized;
    type SemverRef: Borrow<Self::Semver> + Debug;
}

#[derive(Debug)]
pub struct ValueSemver<T>(pub T::SemverRef)
where
    T: SemverTypes + ?Sized,
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>;

impl<T> Clone for ValueSemver<T>
where
    T: SemverTypes + ?Sized,
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>,
    T::SemverRef: Clone,
{
    fn clone(&self) -> Self {
        ValueSemver(self.0.clone())
    }
}

impl<T1, T2> PartialEq<ValueSemver<T2>> for ValueSemver<T1>
where
    T1: SemverTypes + ?Sized,
    T2: SemverTypes + ?Sized,
    for<'a> &'a T1::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a T2::Semver: IntoIterator<Item = &'a u64>,
{
    fn eq(&self, other: &ValueSemver<T2>) -> bool {
        self.partial_cmp(other) == Option::Some(Ordering::Equal)
    }
}

impl<T1, T2> PartialOrd<ValueSemver<T2>> for ValueSemver<T1>
where
    T1: SemverTypes + ?Sized,
    T2: SemverTypes + ?Sized,
    for<'a> &'a T1::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a T2::Semver: IntoIterator<Item = &'a u64>,
{
    fn partial_cmp(&self, other: &ValueSemver<T2>) -> Option<Ordering> {
        let mut v1 = self.0.borrow().into_iter();
        let mut v2 = other.0.borrow().into_iter();
        loop {
            match (v1.next(), v2.next()) {
                (Option::Some(c1), Option::Some(c2)) => {
                    match c1.borrow().partial_cmp(c2.borrow()) {
                        Option::Some(Ordering::Equal) => (),
                        r => return r,
                    }
                }
                (Option::Some(_), Option::None) => return Option::Some(Ordering::Greater),
                (Option::None, Option::Some(_)) => return Option::Some(Ordering::Less),
                (Option::None, Option::None) => return Option::Some(Ordering::Equal),
            }
        }
    }
}

#[derive(Debug)]
pub enum Value<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    Nil,
    UnqualifiedSymbol(ValueUnqualifiedSymbol<T::StringRef>),
    QualifiedSymbol(ValueQualifiedSymbol<T::StringRef>),
    Cons(ValueCons<T>),
    Bool(ValueBool),
    String(ValueString<T::StringRef>),
    Semver(ValueSemver<T::SemverTypes>),
    Procedure(ValueProcedure<T>),
}

macro_rules! try_from_value {
    ($l:lifetime, $t:ident, $out:ty, ($($ct:ty: $constraint:path),*), $match:pat => $result:expr) => {
        impl<$l, $t> TryFrom<&$l Value<$t>> for $out
        where
            $t: ValueTypes + ?Sized,
            for<'b> &'b <$t::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
            $($ct: $constraint),*
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

    ($t:ident, $out:ty, ($($ct:ty: $constraint:path),*), $match:pat => $result:expr) => {
        try_from_value!('a, $t, $out, ($($ct: $constraint),*), $match => $result);
    }
}

macro_rules! try_from_value_ref {
    ($t:ident, $out:ty, $match:pat => $result:expr) => {
        try_from_value!('a, $t, &'a $out, (), $match => $result);
    };
}

try_from_value!(T, (), (), Value::Nil => ());
try_from_value!(
    T, ValueUnqualifiedSymbol<T::StringRef>,
    (ValueUnqualifiedSymbol<T::StringRef>: Clone),
    Value::UnqualifiedSymbol(s) => (*s).clone()
);
try_from_value_ref!(T, ValueUnqualifiedSymbol<T::StringRef>, Value::UnqualifiedSymbol(s) => s);
try_from_value!(
    T,
    ValueQualifiedSymbol<T::StringRef>,
    (ValueQualifiedSymbol<T::StringRef>: Clone),
    Value::QualifiedSymbol(s) => (*s).clone()
);
try_from_value_ref!(T, ValueQualifiedSymbol<T::StringRef>, Value::QualifiedSymbol(s) => s);
try_from_value!(T, ValueCons<T>, (ValueCons<T>: Clone), Value::Cons(c) => (*c).clone());
try_from_value_ref!(T, ValueCons<T>, Value::Cons(c) => c);
try_from_value!(T, ValueBool, (), Value::Bool(b) => (*b).clone());
try_from_value_ref!(T, ValueBool, Value::Bool(b) => b);
try_from_value!(
    T, ValueString<T::StringRef>,
    (ValueString<T::StringRef>: Clone),
    Value::String(s) => (*s).clone()
);
try_from_value_ref!(T, ValueString<T::StringRef>, Value::String(s) => s);
try_from_value!(
    T, ValueSemver<T::SemverTypes>,
    (ValueSemver<T::SemverTypes>: Clone),
    Value::Semver(v) => (*v).clone()
);
try_from_value_ref!(T, ValueSemver<T::SemverTypes>, Value::Semver(v) => v);
try_from_value!(
    T, ValueProcedure<T>,
    (ValueProcedure<T>: Clone),
    Value::Procedure(p) => (*p).clone()
);
try_from_value_ref!(T, ValueProcedure<T>, Value::Procedure(p) => p);

macro_rules! from_value_type {
    ($t:ident, $in:ty, $param:ident -> $result:expr) => {
        impl<$t> From<$in> for Value<$t>
        where
            $t: ValueTypes + ?Sized,
            for<'b> &'b <$t::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
        {
            fn from($param: $in) -> Self {
                $result
            }
        }
    };
}

from_value_type!(T, (), _n -> Value::Nil);
from_value_type!(T, ValueUnqualifiedSymbol<T::StringRef>, s -> Value::UnqualifiedSymbol(s));
from_value_type!(T, ValueQualifiedSymbol<T::StringRef>, s -> Value::QualifiedSymbol(s));
from_value_type!(T, ValueCons<T>, c -> Value::Cons(c));
from_value_type!(T, ValueBool, b -> Value::Bool(b));
from_value_type!(T, ValueString<T::StringRef>, s -> Value::String(s));
from_value_type!(T, ValueSemver<T::SemverTypes>, v -> Value::Semver(v));
from_value_type!(T, ValueProcedure<T>, p -> Value::Procedure(p));

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
    for<'b> &'b <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    for<'b> &'b <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
{
    fn eq(&self, rhs: &Value<T2>) -> bool {
        eq_match!(self, rhs, {
            (Value::Nil, Value::Nil) => true,
            (Value::UnqualifiedSymbol(s1), Value::UnqualifiedSymbol(s2)) => s1 == s2,
            (Value::QualifiedSymbol(s1), Value::QualifiedSymbol(s2)) => s1 == s2,
            (Value::Cons(c1), Value::Cons(c2)) => c1 == c2,
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::String(s1), Value::String(s2)) => s1 == s2,
            (Value::Semver(v1), Value::Semver(v2)) => v1 == v2,
            (Value::Procedure(p1), Value::Procedure(p2)) => p1 == p2,
        })
    }
}

impl<T1, T2> From<&Value<T1>> for Value<T2>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'b> &'b <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    for<'b> &'b <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    Value<T2>: Into<<T2 as ValueTypes>::ValueRef>,
    T1::StringRef: Into<T2::StringRef> + Clone,
    <T1::SemverTypes as SemverTypes>::SemverRef:
        Into<<T2::SemverTypes as SemverTypes>::SemverRef> + Clone,
{
    fn from(v: &Value<T1>) -> Self {
        match v.borrow() {
            Value::Nil => Value::Nil,
            Value::UnqualifiedSymbol(ValueUnqualifiedSymbol(s)) => {
                Value::UnqualifiedSymbol(ValueUnqualifiedSymbol((*s).clone().into()))
            }
            Value::QualifiedSymbol(ValueQualifiedSymbol { name, package }) => {
                Value::QualifiedSymbol(ValueQualifiedSymbol {
                    name: (*name).clone().into(),
                    package: (*package).clone().into(),
                })
            }
            Value::Cons(ValueCons { car, cdr }) => Value::Cons(ValueCons {
                car: Into::<Value<T2>>::into(car.borrow()).into(),
                cdr: Into::<Value<T2>>::into(cdr.borrow()).into(),
            }),
            Value::Bool(ValueBool(b)) => Value::Bool(ValueBool(*b)),
            Value::String(ValueString(s)) => Value::String(ValueString((*s).clone().into())),
            Value::Semver(ValueSemver(v)) => Value::Semver(ValueSemver((*v).clone().into())),
            Value::Procedure(_) => panic!("Cannot move procedures across value type boundaries"),
        }
    }
}

pub fn value_type_convert<T1, T2>(v: T1::ValueRef) -> T2::ValueRef
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'b> &'b <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    for<'b> &'b <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    T1::ValueRef: Into<Value<T2>>,
    Value<T2>: Into<<T2 as ValueTypes>::ValueRef>,
{
    Into::<Value<T2>>::into(v).into()
}

pub struct LispList<T>
where
    T: ValueTypes + ?Sized,
    for<'b> &'b <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    T::ValueRef: Clone,
{
    ptr: T::ValueRef,
}

impl<T> LispList<T>
where
    T: ValueTypes + ?Sized,
    for<'b> &'b <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
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
    for<'b> &'b <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
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

pub fn map_try_into<T, V, R>(v: Result<V>) -> Result<R>
where
    T: ValueTypes + ?Sized,
    for<'b> &'b <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    V: Borrow<Value<T>>,
    for<'a> &'a Value<T>: TryInto<R, Error = Error>,
{
    let v = v?;
    let vb = v.borrow();
    let o = vb.try_into()?;
    std::result::Result::Ok(o)
}

#[derive(Debug)]
pub struct SemverTypesVec;

impl SemverTypes for SemverTypesVec {
    type Semver = Vec<u64>;
    type SemverRef = Self::Semver;
}

#[derive(Debug)]
pub struct ValueTypesRc;

impl ValueTypes for ValueTypesRc {
    type ValueRef = Rc<Value<Self>>;
    type StringRef = String;
    type Proc =
        dyn Fn(&mut (dyn Environment<Self> + 'static), Self::ValueRef) -> Result<Self::ValueRef>;
    type ProcRef = Rc<Self::Proc>;
    type SemverTypes = SemverTypesVec;
}

pub struct LayeredEnvironmentTypesRc;

impl LayeredEnvironmentTypes for LayeredEnvironmentTypesRc {
    type EnvironmentLayerRef = Box<dyn EnvironmentLayer<Self>>;
    type ValueTypes = ValueTypesRc;
}

#[derive(Debug)]
pub struct SemverTypesStatic;

impl SemverTypes for SemverTypesStatic {
    type Semver = [u64];
    type SemverRef = &'static Self::Semver;
}

#[derive(Debug)]
pub struct ValueTypesStatic;

impl ValueTypes for ValueTypesStatic {
    type ValueRef = &'static Value<Self>;
    type StringRef = &'static str;
    type Proc = &'static dyn Fn(
        &mut (dyn Environment<Self> + 'static),
        Self::ValueRef,
    ) -> Result<Self::ValueRef>;
    type ProcRef = Self::Proc;
    type SemverTypes = SemverTypesStatic;
}

#[macro_export]
macro_rules! nil {
    () => {{
        const N: &$crate::Value<$crate::ValueTypesStatic> = &$crate::Value::Nil;
        N
    }};
}

#[macro_export]
macro_rules! uqsym {
    ($name:expr) => {{
        const S: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::UnqualifiedSymbol($crate::ValueUnqualifiedSymbol($name));
        S
    }};
}

#[macro_export]
macro_rules! qsym {
    ($package:expr, $name:expr) => {{
        const S: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::QualifiedSymbol($crate::ValueQualifiedSymbol {
                package: $package,
                name: $name,
            });
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
macro_rules! vref {
    ($v:expr) => {{
        const V: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::Semver($crate::ValueSemver($v as &[u64]));
        V
    }};
}

#[macro_export]
macro_rules! v {
    [$($c:expr),*] => {
        vref!(&[$($c as u64),*])
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
        const NIL: &super::Value<super::ValueTypesStatic> = nil!();
        assert_eq!(*NIL, super::Value::<super::ValueTypesStatic>::Nil);
    }

    #[test]
    fn test_uqsym_macro() {
        const UQSYM: &super::Value<super::ValueTypesStatic> = uqsym!("uqsym");
        match &*UQSYM {
            super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym"),
            _ => panic!("Expected a Value::Symbol"),
        }
    }

    #[test]
    fn test_qsym_macro() {
        const UQSYM: &super::Value<super::ValueTypesStatic> = qsym!("package", "qsym");
        match &*UQSYM {
            super::Value::QualifiedSymbol(s) => {
                assert_eq!(s.package, "package");
                assert_eq!(s.name, "qsym");
            }
            _ => panic!("Expected a Value::UnqualifiedSymbol"),
        }
    }

    #[test]
    fn test_cons_macro() {
        const CONS: &super::Value<super::ValueTypesStatic> = cons!(uqsym!("uqsym"), nil!());
        match &*CONS {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym"),
                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                }
                assert_eq!(*c.cdr, super::Value::<super::ValueTypesStatic>::Nil);
            }
            _ => panic!("Expected a Value::Cons"),
        }
    }

    #[test]
    fn test_bool_macro() {
        const BOOL1: &super::Value<super::ValueTypesStatic> = bool!(true);
        match &*BOOL1 {
            super::Value::Bool(b) => assert_eq!(b.0, true),
            _ => panic!("Expected a Value::Bool"),
        }
        const BOOL2: &super::Value<super::ValueTypesStatic> = bool!(false);
        match &*BOOL2 {
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
    fn test_vref_macro() {
        const V1: &super::Value<super::ValueTypesStatic> = vref!(&[1u64, 0u64]);
        match &*V1 {
            super::Value::Semver(v) => assert_eq!(v.0, &[1, 0]),
            _ => panic!("Expected a Value::Semver"),
        }
    }

    #[test]
    fn test_v_macro() {
        const V1: &super::Value<super::ValueTypesStatic> = v![2, 1];
        match &*V1 {
            super::Value::Semver(v) => assert_eq!(v.0, &[2, 1]),
            _ => panic!("Expected a Value::Semver"),
        }

        const V2: &super::Value<super::ValueTypesStatic> = v![3];
        match &*V2 {
            super::Value::Semver(v) => assert_eq!(v.0, &[3]),
            _ => panic!("Expected a Value::Semver"),
        }
    }

    #[test]
    fn test_list_macro() {
        const LIST1: &super::Value<super::ValueTypesStatic> = list!();
        assert_eq!(*LIST1, super::Value::<super::ValueTypesStatic>::Nil);

        const LIST2: &super::Value<super::ValueTypesStatic> = list!(uqsym!("uqsym1"));
        match &*LIST2 {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                }
                assert_eq!(*c.cdr, super::Value::<super::ValueTypesStatic>::Nil);
            }
            _ => panic!("Expected a Value::Cons"),
        }

        const LIST3: &super::Value<super::ValueTypesStatic> =
            list!(uqsym!("uqsym1"), uqsym!("uqsym2"));
        match &*LIST3 {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                }
                match &*c.cdr {
                    super::Value::Cons(c) => {
                        match &*c.car {
                            super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym2"),
                            _ => panic!("Expected a Value::UnqualifiedSymbol"),
                        }
                        assert_eq!(*c.cdr, super::Value::<super::ValueTypesStatic>::Nil);
                    }
                    _ => panic!("Expected a Value::Cons"),
                }
            }
            _ => panic!("Expected a Value::Cons"),
        }

        const LIST4: &super::Value<super::ValueTypesStatic> =
            list!(uqsym!("uqsym1"), uqsym!("uqsym2"), uqsym!("uqsym3"));
        match &*LIST4 {
            super::Value::Cons(c) => {
                match &*c.car {
                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                }
                match &*c.cdr {
                    super::Value::Cons(c) => {
                        match &*c.car {
                            super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym2"),
                            _ => panic!("Expected a Value::UnqualifiedSymbol"),
                        }
                        match &*c.cdr {
                            super::Value::Cons(c) => {
                                match &*c.car {
                                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym3"),
                                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
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
    fn test_v_cmp() {
        use super::*;
        use more_asserts::*;

        assert_eq!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64] as &[u64]),
        );

        assert_ne!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64, 0u64] as &[u64]),
        );

        assert_lt!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64, 0u64] as &[u64]),
        );

        assert_lt!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 1u64] as &[u64]),
        );

        assert_lt!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 1u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[2u64, 0u64] as &[u64]),
        );

        assert_lt!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 1u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[2u64] as &[u64]),
        );

        assert_ne!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64, 0u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64] as &[u64]),
        );

        assert_gt!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64, 0u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64] as &[u64]),
        );

        assert_gt!(
            ValueSemver::<SemverTypesStatic>(&[1u64, 1u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 0u64] as &[u64]),
        );

        assert_gt!(
            ValueSemver::<SemverTypesStatic>(&[2u64, 0u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 1u64] as &[u64]),
        );

        assert_gt!(
            ValueSemver::<SemverTypesStatic>(&[2u64] as &[u64]),
            ValueSemver::<SemverTypesStatic>(&[1u64, 1u64] as &[u64]),
        );
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
        assert_ne!(nil!(), uqsym!("uqsym"));

        assert_eq!(uqsym!("uqsym"), uqsym!("uqsym"));
        assert_eq!(
            uqsym!("uqsym"),
            &super::Value::<super::ValueTypesRc>::UnqualifiedSymbol(super::ValueUnqualifiedSymbol(
                "uqsym".to_string()
            ))
        );
        assert_ne!(uqsym!("uqsym1"), uqsym!("uqsym2"));
        assert_ne!(
            uqsym!("uqsym1"),
            &super::Value::<super::ValueTypesRc>::UnqualifiedSymbol(super::ValueUnqualifiedSymbol(
                "uqsym2".to_string()
            ))
        );
        assert_ne!(uqsym!("uqsym"), str!("uqsym"));
        assert_ne!(uqsym!("uqsym"), nil!());

        assert_eq!(qsym!("p", "qsym"), qsym!("p", "qsym"));
        assert_eq!(
            qsym!("p", "qsym"),
            &super::Value::<super::ValueTypesRc>::QualifiedSymbol(super::ValueQualifiedSymbol {
                package: "p".to_string(),
                name: "qsym".to_string()
            })
        );
        assert_ne!(qsym!("p1", "qsym"), qsym!("p2", "qsym"));
        assert_ne!(qsym!("p", "qsym1"), qsym!("p", "qsym2"));
        assert_ne!(qsym!("p", "qsym"), uqsym!("qsym"));
        assert_ne!(qsym!("p", "qsym"), str!("p:qsym"));
        assert_ne!(qsym!("p", "qsym"), str!("p"));
        assert_ne!(qsym!("p", "qsym"), str!("qsym"));
        assert_ne!(qsym!("p", "qsym"), nil!());

        assert_eq!(
            cons!(uqsym!("uqsym"), nil!()),
            cons!(uqsym!("uqsym"), nil!())
        );
        assert_ne!(
            cons!(uqsym!("uqsym1"), nil!()),
            cons!(uqsym!("uqsym2"), nil!())
        );
        assert_ne!(cons!(uqsym!("uqsym"), nil!()), cons!(nil!(), nil!()));
        assert_ne!(
            cons!(uqsym!("uqsym"), nil!()),
            cons!(uqsym!("uqsym"), uqsym!("uqsym"))
        );
        assert_ne!(cons!(uqsym!("uqsym"), nil!()), nil!());

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
        assert_ne!(str!("str"), uqsym!("str"));
        assert_ne!(str!("str"), nil!());

        assert_eq!(v![1, 0], v![1, 0]);
        assert_ne!(v![1, 0], v![1, 1]);
        assert_ne!(v![1, 0], nil!());

        let v11 = super::Rc::new(super::Value::<super::ValueTypesRc>::Procedure(
            super::ValueProcedure {
                id: 1,
                proc: super::Rc::new(static_f1),
            },
        ));
        let v12 = super::Rc::new(super::Value::<super::ValueTypesRc>::Procedure(
            super::ValueProcedure {
                id: 1,
                proc: super::Rc::new(static_f2),
            },
        ));
        let v21 = super::Rc::new(super::Value::<super::ValueTypesRc>::Procedure(
            super::ValueProcedure {
                id: 2,
                proc: super::Rc::new(static_f1),
            },
        ));
        let v22 = super::Rc::new(super::Value::<super::ValueTypesRc>::Procedure(
            super::ValueProcedure {
                id: 2,
                proc: super::Rc::new(static_f2),
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
                uqsym!("uqsym"),
                bool!(true),
                str!("str")
            ));
        match l.borrow() {
            Value::Cons(c) => {
                match c.car.borrow() {
                    Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym"),
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
    fn test_try_into_value_type_ref() {
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

        let v = uqsym!("uqsym");
        assert_eq!(
            TryInto::<&ValueUnqualifiedSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap(),
            &ValueUnqualifiedSymbol("uqsym")
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = qsym!("p", "qsym");
        assert_eq!(
            TryInto::<&ValueQualifiedSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap(),
            &ValueQualifiedSymbol { package: "p", name: "qsym" }
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

        let v = v![1, 0];
        assert_eq!(
            TryInto::<&ValueSemver<<ValueTypesStatic as ValueTypes>::SemverTypes>>::try_into(v)
                .unwrap(),
            &ValueSemver::<<ValueTypesStatic as ValueTypes>::SemverTypes>(&[1u64, 0u64] as &[u64])
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = Value::<ValueTypesRc>::Procedure(ValueProcedure::<ValueTypesRc> {
            id: 1,
            proc: Rc::new(static_f1),
        });
        assert_eq!(
            TryInto::<&ValueProcedure<ValueTypesRc>>::try_into(&v).unwrap(),
            &ValueProcedure::<ValueTypesRc> {
                id: 1,
                proc: Rc::new(static_f1)
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );
    }

    #[test]
    fn test_try_into_value_type() {
        use super::*;
        use std::convert::TryInto;

        let v = nil!();
        assert_eq!(TryInto::<()>::try_into(v).unwrap(), ());
        assert_eq!(
            TryInto::<ValueString<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = uqsym!("uqsym");
        assert_eq!(
            TryInto::<ValueUnqualifiedSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap(),
            ValueUnqualifiedSymbol("uqsym")
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = qsym!("p", "qsym");
        assert_eq!(
            TryInto::<ValueQualifiedSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(
                v
            )
            .unwrap(),
            ValueQualifiedSymbol {
                package: "p",
                name: "qsym"
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = cons!(nil!(), nil!());
        assert_eq!(
            TryInto::<ValueCons<ValueTypesStatic>>::try_into(v).unwrap(),
            ValueCons::<ValueTypesStatic> {
                car: nil!(),
                cdr: nil!()
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = bool!(true);
        assert_eq!(TryInto::<ValueBool>::try_into(v).unwrap(), ValueBool(true));
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = str!("str");
        assert_eq!(
            TryInto::<ValueString<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap(),
            ValueString("str")
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v![1, 0];
        assert_eq!(
            TryInto::<ValueSemver<<ValueTypesStatic as ValueTypes>::SemverTypes>>::try_into(v)
                .unwrap(),
            ValueSemver::<<ValueTypesStatic as ValueTypes>::SemverTypes>(&[1u64, 0u64] as &[u64])
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = Value::<ValueTypesRc>::Procedure(ValueProcedure::<ValueTypesRc> {
            id: 1,
            proc: Rc::new(static_f1),
        });
        assert_eq!(
            TryInto::<ValueProcedure<ValueTypesRc>>::try_into(&v).unwrap(),
            ValueProcedure::<ValueTypesRc> {
                id: 1,
                proc: Rc::new(static_f1)
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

        let v: Value<ValueTypesStatic> = ValueUnqualifiedSymbol("uqsym").into();
        assert_eq!(&v, uqsym!("uqsym"));

        let v: Value<ValueTypesStatic> = ValueQualifiedSymbol {
            package: "p",
            name: "qsym",
        }
        .into();
        assert_eq!(&v, qsym!("p", "qsym"));

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

        let v: Value<ValueTypesRc> = ValueProcedure::<ValueTypesRc> {
            id: 1,
            proc: Rc::new(static_f1),
        }
        .into();
        assert_eq!(
            v,
            Value::<ValueTypesRc>::Procedure(ValueProcedure {
                id: 1,
                proc: Rc::new(static_f1)
            })
        );
    }

    #[test]
    fn test_lisp_list() {
        use super::*;

        let mut i =
            LispList::<ValueTypesStatic>::new(list!(uqsym!("uqsym"), bool!(true), str!("str")));
        assert_eq!(i.next().unwrap().unwrap(), uqsym!("uqsym"));
        assert_eq!(i.next().unwrap().unwrap(), bool!(true));
        assert_eq!(i.next().unwrap().unwrap(), str!("str"));
        assert!(i.next().is_none());

        let mut i = LispList::<ValueTypesStatic>::new(cons!(uqsym!("uqsym"), bool!(true)));
        assert_eq!(i.next().unwrap().unwrap(), uqsym!("uqsym"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let mut i =
            LispList::<ValueTypesStatic>::new(list!(uqsym!("uqsym"), bool!(true), str!("str")));
        assert_eq!(i.next().unwrap().unwrap(), uqsym!("uqsym"));
        assert_eq!(i.take(), list!(bool!(true), str!("str")));
    }

    struct SimpleLayer {
        package: &'static str,
        name: &'static str,
        value: <super::ValueTypesRc as super::ValueTypes>::ValueRef,
    }

    impl super::EnvironmentLayer<super::LayeredEnvironmentTypesRc> for SimpleLayer {
        fn resolve_symbol(
            &self,
            s: &super::ValueUnqualifiedSymbol<String>,
        ) -> Option<super::ValueQualifiedSymbol<String>> {
            if s.0 == self.name {
                Option::Some(super::ValueQualifiedSymbol {
                    package: self.package.to_string(),
                    name: s.0.clone(),
                })
            } else {
                Option::None
            }
        }

        fn get_value_qualified(
            &self,
            s: &super::ValueQualifiedSymbol<String>,
        ) -> Option<<super::ValueTypesRc as super::ValueTypes>::ValueRef> {
            if s.package == self.package && s.name == self.name {
                Option::Some(self.value.clone())
            } else {
                Option::None
            }
        }

        fn set_value_qualified(
            &mut self,
            s: &super::ValueQualifiedSymbol<String>,
            v: <super::ValueTypesRc as super::ValueTypes>::ValueRef,
        ) -> super::Result<bool> {
            if s.package == self.package && s.name == self.name {
                self.value = v;
                Result::Ok(true)
            } else {
                Result::Ok(false)
            }
        }
    }

    struct PackageOnlyLayer {
        package: &'static str,
        name: &'static str,
    }

    impl super::EnvironmentLayer<super::LayeredEnvironmentTypesRc> for PackageOnlyLayer {
        fn resolve_symbol(
            &self,
            s: &super::ValueUnqualifiedSymbol<String>,
        ) -> Option<super::ValueQualifiedSymbol<String>> {
            if s.0 == self.name {
                Option::Some(super::ValueQualifiedSymbol {
                    package: self.package.to_string(),
                    name: s.0.clone(),
                })
            } else {
                Option::None
            }
        }

        fn get_value_qualified(
            &self,
            _s: &super::ValueQualifiedSymbol<String>,
        ) -> Option<<super::ValueTypesRc as super::ValueTypes>::ValueRef> {
            Option::None
        }

        fn set_value_qualified(
            &mut self,
            _s: &super::ValueQualifiedSymbol<String>,
            _v: <super::ValueTypesRc as super::ValueTypes>::ValueRef,
        ) -> super::Result<bool> {
            Result::Ok(false)
        }
    }

    fn make_test_env() -> super::LayeredEnvironment<super::LayeredEnvironmentTypesRc> {
        use super::*;

        fn concat(
            env: &mut (dyn Environment<ValueTypesRc> + 'static),
            args: <ValueTypesRc as ValueTypes>::ValueRef,
        ) -> Result<<ValueTypesRc as ValueTypes>::ValueRef> {
            let mut result = String::new();

            for try_item in LispList::<ValueTypesRc>::new(args)
                .map(env.map_evaluate())
                .map(map_try_into::<ValueTypesRc, _, ValueString<String>>)
            {
                let item = try_item?;
                result += &item.0;
            }

            Result::Ok(Rc::new(Value::String(ValueString(result))))
        }

        let layers: Vec<Box<dyn EnvironmentLayer<LayeredEnvironmentTypesRc>>> = vec![
            Box::new(SimpleLayer {
                package: "p1",
                name: "a",
                value: Rc::new(Value::String(ValueString("Hello".to_string()))),
            }),
            Box::new(SimpleLayer {
                package: "p2",
                name: "b",
                value: Rc::new(Value::UnqualifiedSymbol(ValueUnqualifiedSymbol(
                    "uqsym".to_string(),
                ))),
            }),
            Box::new(SimpleLayer {
                package: "p2",
                name: "a",
                value: Rc::new(Value::String(ValueString("world!".to_string()))),
            }),
            Box::new(SimpleLayer {
                package: "p1",
                name: "concat",
                value: Rc::new(Value::Procedure(ValueProcedure {
                    id: 1,
                    proc: Rc::new(concat),
                })),
            }),
            Box::new(PackageOnlyLayer {
                package: "p1",
                name: "d",
            }),
        ];
        LayeredEnvironment { layers }
    }

    #[test]
    fn test_layered_environment_get_value_unqualified() {
        use super::*;

        let env = make_test_env();
        assert_eq!(
            *env.get_value_unqualified(&ValueUnqualifiedSymbol("a".to_string()))
                .unwrap(),
            *str!("Hello")
        );
        assert_eq!(
            *env.get_value_unqualified(&ValueUnqualifiedSymbol("b".to_string()))
                .unwrap(),
            *uqsym!("uqsym")
        );
        assert_eq!(
            env.get_value_unqualified(&ValueUnqualifiedSymbol("c".to_string()))
                .unwrap_err()
                .kind,
            ErrorKind::NoPackageForSymbol
        );
        assert_eq!(
            env.get_value_unqualified(&ValueUnqualifiedSymbol("d".to_string()))
                .unwrap_err()
                .kind,
            ErrorKind::ValueNotDefined
        );
    }

    #[test]
    fn test_layered_environment_get_value_qualified() {
        use super::*;

        let env = make_test_env();
        assert_eq!(
            *env.get_value_qualified(&ValueQualifiedSymbol {
                package: "p1".to_string(),
                name: "a".to_string()
            })
            .unwrap(),
            *str!("Hello")
        );
        assert_eq!(
            *env.get_value_qualified(&ValueQualifiedSymbol {
                package: "p2".to_string(),
                name: "a".to_string()
            })
            .unwrap(),
            *str!("world!")
        );
        assert_eq!(
            *env.get_value_qualified(&ValueQualifiedSymbol {
                package: "p2".to_string(),
                name: "b".to_string()
            })
            .unwrap(),
            *uqsym!("uqsym")
        );
        assert_eq!(
            env.get_value_qualified(&ValueQualifiedSymbol {
                package: "p1".to_string(),
                name: "c".to_string()
            })
            .unwrap_err()
            .kind,
            ErrorKind::ValueNotDefined
        );
    }

    #[test]
    fn test_layered_environment_set_value_unqualified() {
        use super::*;

        let mut env = make_test_env();
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("Hello")
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *uqsym!("uqsym")
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("world!")
        );

        assert!(env
            .set_value_unqualified(
                &ValueUnqualifiedSymbol("a".to_string()),
                Rc::new(Value::Bool(ValueBool(true)))
            )
            .is_ok());
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *uqsym!("uqsym")
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("world!")
        );

        assert!(env
            .set_value_unqualified(
                &ValueUnqualifiedSymbol("b".to_string()),
                Rc::new(Value::Bool(ValueBool(false)))
            )
            .is_ok());
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *bool!(false)
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("world!")
        );

        assert_eq!(
            env.set_value_unqualified(
                &ValueUnqualifiedSymbol("c".to_string()),
                Rc::new(Value::Bool(ValueBool(true)))
            )
            .unwrap_err()
            .kind,
            ErrorKind::NoPackageForSymbol
        );
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *bool!(false)
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("world!")
        );
    }

    #[test]
    fn test_layered_environment_set_value_qualified() {
        use super::*;

        let mut env = make_test_env();
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("Hello")
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *uqsym!("uqsym")
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("world!")
        );

        assert!(env
            .set_value_qualified(
                &ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                },
                Rc::new(Value::Bool(ValueBool(true)))
            )
            .is_ok());
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *uqsym!("uqsym")
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("world!")
        );

        assert!(env
            .set_value_qualified(
                &ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                },
                Rc::new(Value::Bool(ValueBool(false)))
            )
            .is_ok());
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *bool!(false)
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *str!("world!")
        );

        assert!(env
            .set_value_qualified(
                &ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                },
                Rc::new(Value::Bool(ValueBool(true)))
            )
            .is_ok());
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *bool!(false)
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );

        assert_eq!(
            env.set_value_qualified(
                &ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "c".to_string()
                },
                Rc::new(Value::Bool(ValueBool(true)))
            )
            .unwrap_err()
            .kind,
            ErrorKind::NoPackageForSymbol
        );
        assert_eq!(
            *env.layers[0]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p1".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );
        assert_eq!(
            *env.layers[1]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "b".to_string()
                })
                .unwrap(),
            *bool!(false)
        );
        assert_eq!(
            *env.layers[2]
                .get_value_qualified(&ValueQualifiedSymbol {
                    package: "p2".to_string(),
                    name: "a".to_string()
                })
                .unwrap(),
            *bool!(true)
        );
    }

    #[test]
    fn test_environment_evaluate() {
        use super::*;

        let mut env = make_test_env();

        let function_call = value_type_convert::<ValueTypesStatic, ValueTypesRc>(list!(
            uqsym!("concat"),
            uqsym!("a"),
            str!(", "),
            qsym!("p2", "a")
        ));
        assert_eq!(
            *env.evaluate(function_call).unwrap(),
            *str!("Hello, world!")
        );

        let function_call = value_type_convert::<ValueTypesStatic, ValueTypesRc>(list!(
            uqsym!("concat"),
            uqsym!("a"),
            str!(", "),
            bool!(true)
        ));
        assert_eq!(
            env.evaluate(function_call).unwrap_err().kind,
            ErrorKind::IncorrectType
        );
    }
}
