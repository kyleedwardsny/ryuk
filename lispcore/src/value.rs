use super::env::*;
use super::error::*;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::convert::TryFrom;
use std::fmt::Debug;
use std::rc::Rc;

pub trait StringTypes: Debug {
    type StringRef: Clone + Debug;

    fn string_ref_to_str(s: &Self::StringRef) -> &str;

    fn string_ref_from_static_str(s: &'static str) -> Self::StringRef;
}

pub trait StringTypesMut: StringTypes {
    fn string_ref_from_str(s: &str) -> Self::StringRef;

    fn string_ref_from_string(s: String) -> Self::StringRef;
}

pub trait SemverTypes: Debug {
    type SemverIter: Iterator<Item = u64>;
    type SemverRef: Clone + Debug;

    fn semver_ref_to_iter(v: &Self::SemverRef) -> Self::SemverIter;
}

pub trait SemverTypesMut: SemverTypes {
    fn semver_ref_extend<T>(v: &mut Self::SemverRef, iter: T)
    where
        T: IntoIterator<Item = u64>;

    fn semver_ref_from_iter<T>(iter: T) -> Self::SemverRef
    where
        T: IntoIterator<Item = u64>;

    fn semver_ref_default() -> Self::SemverRef;
}

pub trait ValueTypes: Debug {
    type ConsRef: Clone + Debug;
    type ValueRef: Clone + Debug;
    type StringTypes: StringTypes + ?Sized;
    type SemverTypes: SemverTypes + ?Sized;

    fn cons_ref_to_cons(c: &Self::ConsRef) -> &Cons<Self>;

    fn value_ref_to_value(v: &Self::ValueRef) -> &Value<Self>;
}

pub trait ValueTypesMut: ValueTypes
where
    Self::StringTypes: StringTypesMut,
    Self::SemverTypes: SemverTypesMut,
{
    fn cons_ref_from_cons(c: Cons<Self>) -> Self::ConsRef;

    fn value_ref_from_value(v: Value<Self>) -> Self::ValueRef;
}

#[derive(Debug)]
pub struct ValueList<T>(pub Option<T::ConsRef>)
where
    T: ValueTypes + ?Sized;

impl<T> ValueList<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn convert<T2>(&self) -> ValueList<T2>
    where
        T2: ValueTypesMut + ?Sized,
        T2::StringTypes: StringTypesMut,
        T2::SemverTypes: SemverTypesMut,
    {
        ValueList(match &self.0 {
            Option::Some(c) => {
                let cons = c.borrow();
                Option::Some(T2::cons_ref_from_cons(Cons {
                    car: T::cons_ref_to_cons(cons).car.convert::<T2>(),
                    cdr: T::cons_ref_to_cons(cons).cdr.convert::<T2>(),
                }))
            }
            Option::None => Option::None,
        })
    }

    fn list_eq<T2>(&self, other: &ValueList<T2>) -> bool
    where
        T2: ValueTypes + ?Sized,
    {
        match (&self.0, &other.0) {
            (Option::Some(c1), Option::Some(c2)) => {
                T::cons_ref_to_cons(c1) == T2::cons_ref_to_cons(c2)
            }
            (Option::None, Option::None) => true,
            _ => false,
        }
    }
}

impl<T> Clone for ValueList<T>
where
    T: ValueTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T1, T2> PartialEq<ValueList<T2>> for ValueList<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
{
    fn eq(&self, other: &ValueList<T2>) -> bool {
        self.list_eq(other)
    }
}

impl<T> Iterator for ValueList<T>
where
    T: ValueTypes + ?Sized,
{
    type Item = Value<T>;

    fn next(&mut self) -> Option<Self::Item> {
        match &self.0 {
            Option::None => Option::None,
            Option::Some(c) => {
                let cons = T::cons_ref_to_cons(c);
                let car = cons.car.clone();
                let cdr = cons.cdr.clone();
                *self = cdr;
                Option::Some(car)
            }
        }
    }
}

#[derive(Debug)]
pub struct Cons<T>
where
    T: ValueTypes + ?Sized,
{
    pub car: Value<T>,
    pub cdr: ValueList<T>,
}

impl<T> Clone for Cons<T>
where
    T: ValueTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Cons {
            car: self.car.clone(),
            cdr: self.cdr.clone(),
        }
    }
}

impl<T1, T2> PartialEq<Cons<T2>> for Cons<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    Value<T1>: PartialEq<Value<T2>>,
{
    fn eq(&self, other: &Cons<T2>) -> bool {
        self.car == other.car && self.cdr.list_eq(&other.cdr)
    }
}

#[derive(Debug)]
pub struct ValueUnqualifiedSymbol<S>(pub S::StringRef)
where
    S: StringTypes + ?Sized;

impl<S> ValueUnqualifiedSymbol<S>
where
    S: StringTypes + ?Sized,
{
    pub fn convert<S2>(&self) -> ValueUnqualifiedSymbol<S2>
    where
        S2: StringTypesMut + ?Sized,
    {
        ValueUnqualifiedSymbol(S2::string_ref_from_str(S::string_ref_to_str(&self.0)))
    }
}

impl<S> Clone for ValueUnqualifiedSymbol<S>
where
    S: StringTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<S1, S2> PartialEq<ValueUnqualifiedSymbol<S2>> for ValueUnqualifiedSymbol<S1>
where
    S1: StringTypes + ?Sized,
    S2: StringTypes + ?Sized,
{
    fn eq(&self, rhs: &ValueUnqualifiedSymbol<S2>) -> bool {
        S1::string_ref_to_str(&self.0) == S2::string_ref_to_str(&rhs.0)
    }
}

#[derive(Debug)]
pub struct ValueQualifiedSymbol<S>
where
    S: StringTypes + ?Sized,
{
    pub package: S::StringRef,
    pub name: S::StringRef,
}

impl<S> ValueQualifiedSymbol<S>
where
    S: StringTypes + ?Sized,
{
    pub fn convert<S2>(&self) -> ValueQualifiedSymbol<S2>
    where
        S2: StringTypesMut + ?Sized,
    {
        ValueQualifiedSymbol {
            package: S2::string_ref_from_str(S::string_ref_to_str(&self.package)),
            name: S2::string_ref_from_str(S::string_ref_to_str(&self.name)),
        }
    }
}

impl<S> Clone for ValueQualifiedSymbol<S>
where
    S: StringTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Self {
            package: self.package.clone(),
            name: self.name.clone(),
        }
    }
}

impl<S1, S2> PartialEq<ValueQualifiedSymbol<S2>> for ValueQualifiedSymbol<S1>
where
    S1: StringTypes + ?Sized,
    S2: StringTypes + ?Sized,
{
    fn eq(&self, rhs: &ValueQualifiedSymbol<S2>) -> bool {
        S1::string_ref_to_str(&self.package) == S2::string_ref_to_str(&rhs.package)
            && S1::string_ref_to_str(&self.name) == S2::string_ref_to_str(&rhs.name)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ValueBool(pub bool);

#[derive(Debug)]
pub struct ValueString<S>(pub S::StringRef)
where
    S: StringTypes + ?Sized;

impl<S> ValueString<S>
where
    S: StringTypes + ?Sized,
{
    pub fn convert<S2>(&self) -> ValueString<S2>
    where
        S2: StringTypesMut + ?Sized,
    {
        ValueString(S2::string_ref_from_str(S::string_ref_to_str(&self.0)))
    }
}

impl<S> Clone for ValueString<S>
where
    S: StringTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<S1, S2> PartialEq<ValueString<S2>> for ValueString<S1>
where
    S1: StringTypes + ?Sized,
    S2: StringTypes + ?Sized,
{
    fn eq(&self, rhs: &ValueString<S2>) -> bool {
        S1::string_ref_to_str(&self.0) == S2::string_ref_to_str(&rhs.0)
    }
}

#[derive(Debug)]
pub struct ValueSemver<T>
where
    T: SemverTypes + ?Sized,
{
    pub major: u64,
    pub rest: T::SemverRef,
}

impl<T> ValueSemver<T>
where
    T: SemverTypes + ?Sized,
{
    pub fn convert<T2>(&self) -> ValueSemver<T2>
    where
        T2: SemverTypesMut + ?Sized,
    {
        ValueSemver {
            major: self.major,
            rest: T2::semver_ref_from_iter(T::semver_ref_to_iter(&self.rest)),
        }
    }

    pub fn items<'v>(&'v self) -> SemverIter<'v, T> {
        SemverIter {
            v: self,
            iter: Option::None,
        }
    }
}

impl<T> Clone for ValueSemver<T>
where
    T: SemverTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Self {
            major: self.major,
            rest: self.rest.clone(),
        }
    }
}

pub struct SemverIter<'v, T>
where
    T: SemverTypes + ?Sized,
{
    v: &'v ValueSemver<T>,
    iter: Option<T::SemverIter>,
}

impl<'v, T> Iterator for SemverIter<'v, T>
where
    T: SemverTypes + ?Sized,
{
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            Option::None => {
                self.iter = Option::Some(T::semver_ref_to_iter(&self.v.rest));
                Option::Some(self.v.major)
            }
            Option::Some(i) => i.next(),
        }
    }
}

impl<T1, T2> PartialEq<ValueSemver<T2>> for ValueSemver<T1>
where
    T1: SemverTypes + ?Sized,
    T2: SemverTypes + ?Sized,
{
    fn eq(&self, other: &ValueSemver<T2>) -> bool {
        self.partial_cmp(other) == Option::Some(Ordering::Equal)
    }
}

impl<T1, T2> PartialOrd<ValueSemver<T2>> for ValueSemver<T1>
where
    T1: SemverTypes + ?Sized,
    T2: SemverTypes + ?Sized,
{
    fn partial_cmp(&self, other: &ValueSemver<T2>) -> Option<Ordering> {
        let mut v1 = self.items();
        let mut v2 = other.items();
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
pub enum ValueLanguageDirective<S, V>
where
    S: StringTypes + ?Sized,
    V: SemverTypes + ?Sized,
{
    Kira(ValueSemver<V>),
    Other(S::StringRef),
}

impl<S, V> ValueLanguageDirective<S, V>
where
    S: StringTypes + ?Sized,
    V: SemverTypes + ?Sized,
{
    pub fn convert<S2, V2>(&self) -> ValueLanguageDirective<S2, V2>
    where
        S2: StringTypesMut + ?Sized,
        V2: SemverTypesMut + ?Sized,
    {
        match self {
            ValueLanguageDirective::Kira(v) => ValueLanguageDirective::Kira(v.convert::<V2>()),
            ValueLanguageDirective::Other(name) => {
                ValueLanguageDirective::Other(S2::string_ref_from_str(S::string_ref_to_str(&name)))
            }
        }
    }
}

impl<S, V> Clone for ValueLanguageDirective<S, V>
where
    S: StringTypes + ?Sized,
    V: SemverTypes + ?Sized,
{
    fn clone(&self) -> Self {
        match self {
            ValueLanguageDirective::Kira(v) => ValueLanguageDirective::Kira(v.clone()),
            ValueLanguageDirective::Other(name) => ValueLanguageDirective::Other(name.clone()),
        }
    }
}

impl<S1, V1, S2, V2> PartialEq<ValueLanguageDirective<S2, V2>> for ValueLanguageDirective<S1, V1>
where
    S1: StringTypes + ?Sized,
    S2: StringTypes + ?Sized,
    V1: SemverTypes + ?Sized,
    V2: SemverTypes + ?Sized,
{
    fn eq(&self, rhs: &ValueLanguageDirective<S2, V2>) -> bool {
        eq_match!(self, rhs, {
            (ValueLanguageDirective::Kira(v1), ValueLanguageDirective::Kira(v2)) => v1 == v2,
            (ValueLanguageDirective::Other(n1), ValueLanguageDirective::Other(n2)) => S1::string_ref_to_str(&n1) == S2::string_ref_to_str(&n2),
        })
    }
}

#[derive(Debug)]
pub struct ValueFunction<S>(pub ValueQualifiedSymbol<S>)
where
    S: StringTypes + ?Sized;

impl<S> ValueFunction<S>
where
    S: StringTypes + ?Sized,
{
    pub fn convert<S2>(&self) -> ValueFunction<S2>
    where
        S2: StringTypesMut + ?Sized,
    {
        ValueFunction(self.0.convert())
    }
}

impl<S1, S2> PartialEq<ValueFunction<S2>> for ValueFunction<S1>
where
    S1: StringTypes + ?Sized,
    S2: StringTypes + ?Sized,
    ValueQualifiedSymbol<S1>: PartialEq<ValueQualifiedSymbol<S2>>,
{
    fn eq(&self, rhs: &ValueFunction<S2>) -> bool {
        self.0 == rhs.0
    }
}

impl<S> Clone for ValueFunction<S>
where
    S: StringTypes + ?Sized,
    ValueQualifiedSymbol<S>: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[derive(Debug)]
pub struct ValueBackquote<T>(pub T::ValueRef)
where
    T: ValueTypes + ?Sized;

impl<T> ValueBackquote<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn convert<T2>(&self) -> ValueBackquote<T2>
    where
        T2: ValueTypesMut + ?Sized,
        T2::StringTypes: StringTypesMut,
        T2::SemverTypes: SemverTypesMut,
    {
        ValueBackquote(T2::value_ref_from_value(
            T::value_ref_to_value(&self.0).convert(),
        ))
    }
}

impl<T1, T2> PartialEq<ValueBackquote<T2>> for ValueBackquote<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    Value<T1>: PartialEq<Value<T2>>,
{
    fn eq(&self, rhs: &ValueBackquote<T2>) -> bool {
        T1::value_ref_to_value(&self.0) == T2::value_ref_to_value(&rhs.0)
    }
}

impl<T> Clone for ValueBackquote<T>
where
    T: ValueTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[derive(Debug)]
pub struct ValueComma<T>(pub T::ValueRef)
where
    T: ValueTypes + ?Sized;

impl<T> ValueComma<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn convert<T2>(&self) -> ValueComma<T2>
    where
        T2: ValueTypesMut + ?Sized,
        T2::StringTypes: StringTypesMut,
        T2::SemverTypes: SemverTypesMut,
    {
        ValueComma(T2::value_ref_from_value(
            T::value_ref_to_value(&self.0).convert(),
        ))
    }
}

impl<T1, T2> PartialEq<ValueComma<T2>> for ValueComma<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    Value<T1>: PartialEq<Value<T2>>,
{
    fn eq(&self, rhs: &ValueComma<T2>) -> bool {
        T1::value_ref_to_value(&self.0) == T2::value_ref_to_value(&rhs.0)
    }
}

impl<T> Clone for ValueComma<T>
where
    T: ValueTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[derive(Debug)]
pub struct ValueSplice<T>(pub T::ValueRef)
where
    T: ValueTypes + ?Sized;

impl<T> ValueSplice<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn convert<T2>(&self) -> ValueSplice<T2>
    where
        T2: ValueTypesMut + ?Sized,
        T2::StringTypes: StringTypesMut,
        T2::SemverTypes: SemverTypesMut,
    {
        ValueSplice(T2::value_ref_from_value(
            T::value_ref_to_value(&self.0).convert(),
        ))
    }
}

impl<T1, T2> PartialEq<ValueSplice<T2>> for ValueSplice<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    Value<T1>: PartialEq<Value<T2>>,
{
    fn eq(&self, rhs: &ValueSplice<T2>) -> bool {
        T1::value_ref_to_value(&self.0) == T2::value_ref_to_value(&rhs.0)
    }
}

impl<T> Clone for ValueSplice<T>
where
    T: ValueTypes + ?Sized,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[derive(Debug)]
pub enum Value<T>
where
    T: ValueTypes + ?Sized,
{
    List(ValueList<T>),
    UnqualifiedSymbol(ValueUnqualifiedSymbol<T::StringTypes>),
    QualifiedSymbol(ValueQualifiedSymbol<T::StringTypes>),
    Bool(ValueBool),
    String(ValueString<T::StringTypes>),
    Semver(ValueSemver<T::SemverTypes>),
    LanguageDirective(ValueLanguageDirective<T::StringTypes, T::SemverTypes>),
    Function(ValueFunction<T::StringTypes>),
    Backquote(ValueBackquote<T>),
    Comma(ValueComma<T>),
    Splice(ValueSplice<T>),
}

impl<T> Value<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn convert<T2>(&self) -> Value<T2>
    where
        T2: ValueTypesMut + ?Sized,
        T2::StringTypes: StringTypesMut,
        T2::SemverTypes: SemverTypesMut,
    {
        match self {
            Value::List(l) => Value::List(l.convert::<T2>()),
            Value::UnqualifiedSymbol(s) => Value::UnqualifiedSymbol(s.convert::<T2::StringTypes>()),
            Value::QualifiedSymbol(s) => Value::QualifiedSymbol(s.convert::<T2::StringTypes>()),
            Value::Bool(b) => Value::Bool(b.clone()),
            Value::String(s) => Value::String(s.convert::<T2::StringTypes>()),
            Value::Semver(v) => Value::Semver(v.convert::<T2::SemverTypes>()),
            Value::LanguageDirective(l) => {
                Value::LanguageDirective(l.convert::<T2::StringTypes, T2::SemverTypes>())
            }
            Value::Function(f) => Value::Function(f.convert::<T2::StringTypes>()),
            Value::Backquote(b) => Value::Backquote(b.convert::<T2>()),
            Value::Comma(c) => Value::Comma(c.convert::<T2>()),
            Value::Splice(s) => Value::Splice(s.convert::<T2>()),
        }
    }

    pub fn value_type(&self) -> ValueType {
        use std::iter::FromIterator;

        match self {
            Value::List(l) => {
                ValueType::List(BTreeSet::from_iter(l.clone().map(|item| item.value_type())))
            }
            Value::UnqualifiedSymbol(_) => ValueType::UnqualifiedSymbol,
            Value::QualifiedSymbol(_) => ValueType::QualifiedSymbol,
            Value::Bool(_) => ValueType::Bool,
            Value::String(_) => ValueType::String,
            Value::Semver(_) => ValueType::Semver,
            Value::LanguageDirective(_) => ValueType::LanguageDirective,
            Value::Function(_) => ValueType::Function,
            Value::Backquote(b) => {
                ValueType::Backquote(Box::new(T::value_ref_to_value(&b.0).value_type()))
            }
            Value::Comma(c) => ValueType::Comma(Box::new(T::value_ref_to_value(&c.0).value_type())),
            Value::Splice(s) => {
                ValueType::Splice(Box::new(T::value_ref_to_value(&s.0).value_type()))
            }
        }
    }
}

impl<T> Clone for Value<T>
where
    T: ValueTypes + ?Sized,
    ValueUnqualifiedSymbol<T::StringTypes>: Clone,
    ValueQualifiedSymbol<T::StringTypes>: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Value::List(l) => Value::List((*l).clone()),
            Value::UnqualifiedSymbol(s) => Value::UnqualifiedSymbol((*s).clone()),
            Value::QualifiedSymbol(s) => Value::QualifiedSymbol((*s).clone()),
            Value::Bool(b) => Value::Bool((*b).clone()),
            Value::String(s) => Value::String((*s).clone()),
            Value::Semver(v) => Value::Semver((*v).clone()),
            Value::LanguageDirective(l) => Value::LanguageDirective((*l).clone()),
            Value::Function(f) => Value::Function((*f).clone()),
            Value::Backquote(b) => Value::Backquote((*b).clone()),
            Value::Comma(c) => Value::Comma((*c).clone()),
            Value::Splice(s) => Value::Splice((*s).clone()),
        }
    }
}

macro_rules! try_from_value {
    ($l:lifetime, $t:ident, $in:ty, $out:ty, $match:pat => $result:expr) => {
        impl<$l, $t> TryFrom<$in> for $out
        where
            $t: ValueTypes + ?Sized,
        {
            type Error = Error;

            fn try_from(v: $in) -> Result<Self> {
                match v {
                    $match => Result::Ok($result),
                    _ => Result::Err(Error::new(ErrorKind::IncorrectType, "Incorrect type")),
                }
            }
        }
    };

    ($t:ident, (), $match:pat => $result:expr) => {
        try_from_value!('v, $t, Value<$t>, (), $match => $result);
        try_from_value!('v, $t, &'v Value<$t>, (), $match => $result);
    };

    ($t:ident, $out:ty, $match:pat => $result:expr) => {
        try_from_value!('v, $t, Value<$t>, $out, $match => $result);
        try_from_value!('v, $t, &'v Value<$t>, &'v $out, $match => $result);
    };
}

try_from_value!(T, ValueList<T>, Value::List(l) => l);
try_from_value!(T, ValueUnqualifiedSymbol<T::StringTypes>, Value::UnqualifiedSymbol(s) => s);
try_from_value!(T, ValueQualifiedSymbol<T::StringTypes>, Value::QualifiedSymbol(s) => s);
try_from_value!(T, ValueBool, Value::Bool(b) => b);
try_from_value!(T, ValueString<T::StringTypes>, Value::String(s) => s);
try_from_value!(T, ValueSemver<T::SemverTypes>, Value::Semver(v) => v);
try_from_value!(T, ValueLanguageDirective<T::StringTypes, T::SemverTypes>, Value::LanguageDirective(l) => l);
try_from_value!(T, ValueFunction<T::StringTypes>, Value::Function(f) => f);
try_from_value!(T, ValueBackquote<T>, Value::Backquote(b) => b);
try_from_value!(T, ValueComma<T>, Value::Comma(c) => c);
try_from_value!(T, ValueSplice<T>, Value::Splice(s) => s);

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

from_value_type!(T, ValueList<T>, l -> Value::List(l));
from_value_type!(T, ValueUnqualifiedSymbol<T::StringTypes>, s -> Value::UnqualifiedSymbol(s));
from_value_type!(T, ValueQualifiedSymbol<T::StringTypes>, s -> Value::QualifiedSymbol(s));
from_value_type!(T, ValueBool, b -> Value::Bool(b));
from_value_type!(T, ValueString<T::StringTypes>, s -> Value::String(s));
from_value_type!(T, ValueSemver<T::SemverTypes>, v -> Value::Semver(v));
from_value_type!(T, ValueLanguageDirective<T::StringTypes, T::SemverTypes>, l -> Value::LanguageDirective(l));
from_value_type!(T, ValueFunction<T::StringTypes>, f -> Value::Function(f));
from_value_type!(T, ValueBackquote<T>, b -> Value::Backquote(b));
from_value_type!(T, ValueComma<T>, c -> Value::Comma(c));
from_value_type!(T, ValueSplice<T>, s -> Value::Splice(s));

impl<T1, T2> PartialEq<Value<T2>> for Value<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
{
    fn eq(&self, rhs: &Value<T2>) -> bool {
        eq_match!(self, rhs, {
            (Value::List(l1), Value::List(l2)) => l1.list_eq(l2),
            (Value::UnqualifiedSymbol(s1), Value::UnqualifiedSymbol(s2)) => s1 == s2,
            (Value::QualifiedSymbol(s1), Value::QualifiedSymbol(s2)) => s1 == s2,
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::String(s1), Value::String(s2)) => s1 == s2,
            (Value::Semver(v1), Value::Semver(v2)) => v1 == v2,
            (Value::LanguageDirective(l1), Value::LanguageDirective(l2)) => l1 == l2,
            (Value::Function(f1), Value::Function(f2)) => f1 == f2,
            (Value::Backquote(b1), Value::Backquote(b2)) => b1 == b2,
            (Value::Comma(c1), Value::Comma(c2)) => c1 == c2,
            (Value::Splice(s1), Value::Splice(s2)) => s1 == s2,
        })
    }
}

#[derive(Debug)]
pub struct StringTypesString;

impl StringTypes for StringTypesString {
    type StringRef = String;

    fn string_ref_to_str(s: &Self::StringRef) -> &str {
        &*s
    }

    fn string_ref_from_static_str(s: &'static str) -> Self::StringRef {
        s.to_string()
    }
}

impl StringTypesMut for StringTypesString {
    fn string_ref_from_str(s: &str) -> Self::StringRef {
        s.to_string()
    }

    fn string_ref_from_string(s: String) -> Self::StringRef {
        s
    }
}

#[derive(Debug)]
pub struct SemverTypesVec;

impl SemverTypes for SemverTypesVec {
    type SemverIter = std::vec::IntoIter<u64>;
    type SemverRef = Vec<u64>;

    fn semver_ref_to_iter(v: &Self::SemverRef) -> Self::SemverIter {
        v.clone().into_iter()
    }
}

impl SemverTypesMut for SemverTypesVec {
    fn semver_ref_extend<T>(v: &mut Self::SemverRef, iter: T)
    where
        T: IntoIterator<Item = u64>,
    {
        v.extend(iter)
    }

    fn semver_ref_from_iter<T>(iter: T) -> Self::SemverRef
    where
        T: IntoIterator<Item = u64>,
    {
        use std::iter::FromIterator;

        Self::SemverRef::from_iter(iter)
    }

    fn semver_ref_default() -> Self::SemverRef {
        Self::SemverRef::default()
    }
}

#[derive(Debug)]
pub struct ValueTypesRc;

impl ValueTypes for ValueTypesRc {
    type ConsRef = Rc<Cons<Self>>;
    type ValueRef = Box<Value<Self>>;
    type StringTypes = StringTypesString;
    type SemverTypes = SemverTypesVec;

    fn cons_ref_to_cons(c: &Self::ConsRef) -> &Cons<Self> {
        &*c
    }

    fn value_ref_to_value(v: &Self::ValueRef) -> &Value<Self> {
        &*v
    }
}

impl ValueTypesMut for ValueTypesRc {
    fn cons_ref_from_cons(c: Cons<Self>) -> Self::ConsRef {
        c.into()
    }

    fn value_ref_from_value(v: Value<Self>) -> Self::ValueRef {
        v.into()
    }
}

#[derive(Debug)]
pub struct StringTypesStatic;

impl StringTypes for StringTypesStatic {
    type StringRef = &'static str;

    fn string_ref_to_str(s: &Self::StringRef) -> &str {
        *s
    }

    fn string_ref_from_static_str(s: &'static str) -> Self::StringRef {
        s
    }
}

#[derive(Debug)]
pub struct SemverTypesStatic;

impl SemverTypes for SemverTypesStatic {
    type SemverIter = std::iter::Map<std::slice::Iter<'static, u64>, fn(&'static u64) -> u64>;
    type SemverRef = &'static [u64];

    fn semver_ref_to_iter(v: &Self::SemverRef) -> Self::SemverIter {
        (*v).into_iter().map(|comp| *comp)
    }
}

#[derive(Debug)]
pub struct ValueTypesStatic;

impl ValueTypes for ValueTypesStatic {
    type ConsRef = &'static Cons<Self>;
    type ValueRef = &'static Value<Self>;
    type StringTypes = StringTypesStatic;
    type SemverTypes = SemverTypesStatic;

    fn cons_ref_to_cons(c: &Self::ConsRef) -> &Cons<Self> {
        *c
    }

    fn value_ref_to_value(v: &Self::ValueRef) -> &Value<Self> {
        *v
    }
}

#[macro_export]
macro_rules! cons {
    ($car:expr, $cdr:expr) => {
        $crate::value::ValueList::<$crate::value::ValueTypesStatic>(::std::option::Option::Some(
            &$crate::value::Cons {
                car: $car,
                cdr: $cdr,
            },
        ))
    };
}

#[macro_export]
macro_rules! list {
    () => { $crate::value::ValueList::<$crate::value::ValueTypesStatic>(::std::option::Option::None) };
    ($e:expr) => { cons!($e, list!()) };
    ($e:expr, $($es:expr),*) => { cons!($e, list!($($es),*)) };
}

#[macro_export]
macro_rules! v_list {
    ($($es:expr),*) => { $crate::value::Value::<$crate::value::ValueTypesStatic>::List(list!($($es),*)) };
}

#[macro_export]
macro_rules! uqsym {
    ($name:expr) => {
        $crate::value::ValueUnqualifiedSymbol::<$crate::value::StringTypesStatic>($name)
    };
}

#[macro_export]
macro_rules! v_uqsym {
    ($name:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::UnqualifiedSymbol(uqsym!($name))
    };
}

#[macro_export]
macro_rules! qsym {
    ($package:expr, $name:expr) => {
        $crate::value::ValueQualifiedSymbol::<$crate::value::StringTypesStatic> {
            package: $package,
            name: $name,
        }
    };
}

#[macro_export]
macro_rules! v_qsym {
    ($package:expr, $name:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::QualifiedSymbol(qsym!(
            $package, $name
        ))
    };
}

#[macro_export]
macro_rules! bool {
    ($b:expr) => {
        $crate::value::ValueBool($b)
    };
}

#[macro_export]
macro_rules! v_bool {
    ($b:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::Bool(bool!($b))
    };
}

#[macro_export]
macro_rules! str {
    ($s:expr) => {
        $crate::value::ValueString::<$crate::value::StringTypesStatic>($s)
    };
}

#[macro_export]
macro_rules! v_str {
    ($s:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::String(str!($s))
    };
}

#[macro_export]
macro_rules! vref {
    ($major:expr, $rest:expr) => {
        $crate::value::ValueSemver::<$crate::value::SemverTypesStatic> {
            major: $major as u64,
            rest: $rest as &[u64],
        }
    };
}

#[macro_export]
macro_rules! v_vref {
    ($major:expr, $rest:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::Semver(vref!($major, $rest))
    };
}

#[macro_export]
macro_rules! v {
    [$major:expr] => {
        vref!($major, &[])
    };

    [$major:expr, $($rest:expr),*] => {
        vref!($major, &[$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! v_v {
    [$major:expr] => {
        v_vref!($major, &[])
    };

    [$major:expr, $($rest:expr),*] => {
        v_vref!($major, &[$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! v_lang {
    ($lang:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::LanguageDirective($lang)
    };
}

#[macro_export]
macro_rules! lang_kira_ref {
    ($major:expr, $rest:expr) => {
        $crate::value::ValueLanguageDirective::<
            $crate::value::StringTypesStatic,
            $crate::value::SemverTypesStatic,
        >::Kira(vref!($major, $rest))
    };
}

#[macro_export]
macro_rules! v_lang_kira_ref {
    ($major:expr, $rest:expr) => {
        v_lang!(lang_kira_ref!($major, $rest))
    };
}

#[macro_export]
macro_rules! lang_kira {
    [$major:expr] => {
        lang_kira_ref!($major, &[])
    };

    [$major:expr, $($rest:expr),*] => {
        lang_kira_ref!($major, &[$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! v_lang_kira {
    [$major:expr] => {
        v_lang_kira_ref!($major, &[])
    };

    [$major:expr, $($rest:expr),*] => {
        v_lang_kira_ref!($major, &[$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! lang_other {
    ($name:expr) => {
        $crate::value::ValueLanguageDirective::<
            $crate::value::StringTypesStatic,
            $crate::value::SemverTypesStatic,
        >::Other($name)
    };
}

#[macro_export]
macro_rules! v_lang_other {
    ($name:expr) => {
        v_lang!(lang_other!($name))
    };
}

#[macro_export]
macro_rules! func {
    ($name:expr) => {
        $crate::value::ValueFunction::<$crate::value::StringTypesStatic>($name)
    };
}

#[macro_export]
macro_rules! v_func {
    ($name:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::Function(func!($name))
    };
}

#[macro_export]
macro_rules! bq {
    ($val:expr) => {
        $crate::value::ValueBackquote::<$crate::value::ValueTypesStatic>(&$val)
    };
}

#[macro_export]
macro_rules! v_bq {
    ($val:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::Backquote(bq!($val))
    };
}

#[macro_export]
macro_rules! comma {
    ($val:expr) => {
        $crate::value::ValueComma::<$crate::value::ValueTypesStatic>(&$val)
    };
}

#[macro_export]
macro_rules! v_comma {
    ($val:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::Comma(comma!($val))
    };
}

#[macro_export]
macro_rules! splice {
    ($val:expr) => {
        $crate::value::ValueSplice::<$crate::value::ValueTypesStatic>(&$val)
    };
}

#[macro_export]
macro_rules! v_splice {
    ($val:expr) => {
        $crate::value::Value::<$crate::value::ValueTypesStatic>::Splice(splice!($val))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    mod macro_tests {
        #[test]
        fn test_uqsym_macro() {
            const UQSYM: super::ValueUnqualifiedSymbol<super::StringTypesStatic> = uqsym!("uqsym");
            assert_eq!(UQSYM.0, "uqsym");
        }

        #[test]
        fn test_v_uqsym_macro() {
            const UQSYM: super::Value<super::ValueTypesStatic> = v_uqsym!("uqsym");
            match UQSYM {
                super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym"),
                _ => panic!("Expected a Value::Symbol"),
            }
        }

        #[test]
        fn test_qsym_macro() {
            const QSYM: super::ValueQualifiedSymbol<super::StringTypesStatic> =
                qsym!("package", "qsym");
            assert_eq!(QSYM.package, "package");
            assert_eq!(QSYM.name, "qsym");
        }

        #[test]
        fn test_v_qsym_macro() {
            const QSYM: super::Value<super::ValueTypesStatic> = v_qsym!("package", "qsym");
            match QSYM {
                super::Value::QualifiedSymbol(s) => {
                    assert_eq!(s.package, "package");
                    assert_eq!(s.name, "qsym");
                }
                _ => panic!("Expected a Value::UnqualifiedSymbol"),
            }
        }

        #[test]
        fn test_bool_macro() {
            const BOOL1: super::ValueBool = bool!(true);
            assert_eq!(BOOL1.0, true);

            const BOOL2: super::ValueBool = bool!(false);
            assert_eq!(BOOL2.0, false);
        }

        #[test]
        fn test_v_bool_macro() {
            const BOOL1: super::Value<super::ValueTypesStatic> = v_bool!(true);
            match BOOL1 {
                super::Value::Bool(b) => assert_eq!(b.0, true),
                _ => panic!("Expected a Value::Bool"),
            }
            const BOOL2: super::Value<super::ValueTypesStatic> = v_bool!(false);
            match BOOL2 {
                super::Value::Bool(b) => assert_eq!(b.0, false),
                _ => panic!("Expected a Value::Bool"),
            }
        }

        #[test]
        fn test_str_macro() {
            const S: super::ValueString<super::StringTypesStatic> = str!("str");
            assert_eq!(S.0, "str");
        }

        #[test]
        fn test_v_str_macro() {
            const S: super::Value<super::ValueTypesStatic> = v_str!("str");
            match S {
                super::Value::String(s) => assert_eq!(s.0, "str"),
                _ => panic!("Expected a Value::String"),
            }
        }

        #[test]
        fn test_vref_macro() {
            const V1: super::ValueSemver<super::SemverTypesStatic> = vref!(1u64, &[0u64]);
            assert_eq!(V1.major, 1);
            assert_eq!(V1.rest, &[0]);

            const V2: super::ValueSemver<super::SemverTypesStatic> = vref!(4u64, &[]);
            assert_eq!(V2.major, 4);
            assert_eq!(V2.rest, &[]);
        }

        #[test]
        fn test_v_vref_macro() {
            const V1: super::Value<super::ValueTypesStatic> = v_vref!(1u64, &[0u64]);
            match V1 {
                super::Value::Semver(v) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, &[0]);
                }
                _ => panic!("Expected a Value::Semver"),
            }

            const V2: super::Value<super::ValueTypesStatic> = v_vref!(4u64, &[]);
            match V2 {
                super::Value::Semver(v) => {
                    assert_eq!(v.major, 4);
                    assert_eq!(v.rest, &[]);
                }
                _ => panic!("Expected a Value::Semver"),
            }
        }

        #[test]
        fn test_v_macro() {
            const V1: super::ValueSemver<super::SemverTypesStatic> = v![2, 1];
            assert_eq!(V1.major, 2);
            assert_eq!(V1.rest, &[1]);

            const V2: super::ValueSemver<super::SemverTypesStatic> = v![3];
            assert_eq!(V2.major, 3);
            assert_eq!(V2.rest, &[]);
        }

        #[test]
        fn test_v_v_macro() {
            const V1: super::Value<super::ValueTypesStatic> = v_v![2, 1];
            match V1 {
                super::Value::Semver(v) => {
                    assert_eq!(v.major, 2);
                    assert_eq!(v.rest, &[1]);
                }
                _ => panic!("Expected a Value::Semver"),
            }

            const V2: super::Value<super::ValueTypesStatic> = v_v![3];
            match V2 {
                super::Value::Semver(v) => {
                    assert_eq!(v.major, 3);
                    assert_eq!(v.rest, &[]);
                }
                _ => panic!("Expected a Value::Semver"),
            }
        }

        #[test]
        fn test_lang_kira_macro() {
            const L1: super::ValueLanguageDirective<
                super::StringTypesStatic,
                super::SemverTypesStatic,
            > = lang_kira![1];
            match L1 {
                super::ValueLanguageDirective::Kira(v) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, &[]);
                }
                _ => panic!("Expected a Value::LanguageDirective with Kira"),
            }

            const L2: super::ValueLanguageDirective<
                super::StringTypesStatic,
                super::SemverTypesStatic,
            > = lang_kira![1, 0];
            match L2 {
                super::ValueLanguageDirective::Kira(v) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, &[0]);
                }
                _ => panic!("Expected a Value::LanguageDirective with Kira"),
            }
        }

        #[test]
        fn test_v_lang_kira_macro() {
            const L1: super::Value<super::ValueTypesStatic> = v_lang_kira![1];
            match L1 {
                super::Value::LanguageDirective(super::ValueLanguageDirective::Kira(v)) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, &[]);
                }
                _ => panic!("Expected a Value::LanguageDirective with Kira"),
            }

            const L2: super::Value<super::ValueTypesStatic> = v_lang_kira![1, 0];
            match L2 {
                super::Value::LanguageDirective(super::ValueLanguageDirective::Kira(v)) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, &[0]);
                }
                _ => panic!("Expected a Value::LanguageDirective with Kira"),
            }
        }

        #[test]
        fn test_lang_other_macro() {
            const L1: super::ValueLanguageDirective<
                super::StringTypesStatic,
                super::SemverTypesStatic,
            > = lang_other!("not-kira");
            match L1 {
                super::ValueLanguageDirective::Other(n) => {
                    assert_eq!(n, "not-kira");
                }
                _ => panic!("Expected a Value::LanguageDirective with other"),
            }
        }

        #[test]
        fn test_v_lang_other_macro() {
            const L1: super::Value<super::ValueTypesStatic> = v_lang_other!("not-kira");
            match L1 {
                super::Value::LanguageDirective(super::ValueLanguageDirective::Other(n)) => {
                    assert_eq!(n, "not-kira");
                }
                _ => panic!("Expected a Value::LanguageDirective with other"),
            }
        }

        #[test]
        fn test_func_macro() {
            const F: super::ValueFunction<super::StringTypesStatic> = func!(qsym!("p", "f1"));
            assert_eq!(
                F.0,
                super::ValueQualifiedSymbol::<super::StringTypesStatic> {
                    package: "p",
                    name: "f1"
                }
            );
        }

        #[test]
        fn test_v_func_macro() {
            const F: super::Value<super::ValueTypesStatic> = v_func!(qsym!("p", "f1"));
            match F {
                super::Value::Function(super::ValueFunction(name)) => assert_eq!(
                    name,
                    super::ValueQualifiedSymbol::<super::StringTypesStatic> {
                        package: "p",
                        name: "f1"
                    }
                ),
                _ => panic!("Expected a Value::Function"),
            }
        }

        #[test]
        fn test_bq_macro() {
            const BQ1: super::ValueBackquote<super::ValueTypesStatic> = bq!(v_qsym!("p", "qsym"));
            assert_eq!(*BQ1.0, v_qsym!("p", "qsym"));

            const BQ2: super::ValueBackquote<super::ValueTypesStatic> = bq!(v_str!("str"));
            assert_eq!(*BQ2.0, v_str!("str"));
        }

        #[test]
        fn test_v_bq_macro() {
            const BQ: super::Value<super::ValueTypesStatic> = v_bq!(v_bool!(true));
            match BQ {
                super::Value::Backquote(super::ValueBackquote(v)) => assert_eq!(*v, v_bool!(true)),
                _ => panic!("Expected a Value::Backquote"),
            }
        }

        #[test]
        fn test_comma_macro() {
            const C1: super::ValueComma<super::ValueTypesStatic> = comma!(v_qsym!("p", "qsym"));
            assert_eq!(*C1.0, v_qsym!("p", "qsym"));

            const C2: super::ValueComma<super::ValueTypesStatic> = comma!(v_str!("str"));
            assert_eq!(*C2.0, v_str!("str"));
        }

        #[test]
        fn test_v_comma_macro() {
            const C: super::Value<super::ValueTypesStatic> = v_comma!(v_bool!(true));
            match C {
                super::Value::Comma(super::ValueComma(v)) => assert_eq!(*v, v_bool!(true)),
                _ => panic!("Expected a Value::Comma"),
            }
        }

        #[test]
        fn test_splice_macro() {
            const S1: super::ValueSplice<super::ValueTypesStatic> = splice!(v_qsym!("p", "qsym"));
            assert_eq!(*S1.0, v_qsym!("p", "qsym"));

            const S2: super::ValueSplice<super::ValueTypesStatic> = splice!(v_str!("str"));
            assert_eq!(*S2.0, v_str!("str"));
        }

        #[test]
        fn test_v_splice_macro() {
            const S: super::Value<super::ValueTypesStatic> = v_splice!(v_bool!(true));
            match S {
                super::Value::Splice(super::ValueSplice(v)) => assert_eq!(*v, v_bool!(true)),
                _ => panic!("Expected a Value::Splice"),
            }
        }

        #[test]
        fn test_list_macro() {
            const LIST1: super::ValueList<super::ValueTypesStatic> = list!();
            assert_eq!(
                LIST1,
                super::ValueList::<super::ValueTypesStatic>(Option::None)
            );

            const LIST2: super::ValueList<super::ValueTypesStatic> = list!(v_uqsym!("uqsym1"));
            match LIST2 {
                super::ValueList(Option::Some(l)) => {
                    match &l.car {
                        super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                        _ => panic!("Expected a Value::UnqualifiedSymbol"),
                    }
                    assert_eq!(
                        l.cdr,
                        super::ValueList::<super::ValueTypesStatic>(Option::None)
                    );
                }
                _ => panic!("Expected a ValueList(Option::Some)"),
            }

            const LIST3: super::ValueList<super::ValueTypesStatic> =
                list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"));
            match LIST3 {
                super::ValueList(Option::Some(l)) => {
                    match &l.car {
                        super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                        _ => panic!("Expected a Value::UnqualifiedSymbol"),
                    }
                    match &l.cdr {
                        super::ValueList(Option::Some(l)) => {
                            match &l.car {
                                super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym2"),
                                _ => panic!("Expected a Value::UnqualifiedSymbol"),
                            }
                            assert_eq!(
                                l.cdr,
                                super::ValueList::<super::ValueTypesStatic>(Option::None)
                            );
                        }
                        _ => panic!("Expected a ValueList(Option::Some)"),
                    }
                }
                _ => panic!("Expected a ValueList(Option::Some)"),
            }

            const LIST4: super::ValueList<super::ValueTypesStatic> =
                list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"), v_uqsym!("uqsym3"));
            match LIST4 {
                super::ValueList(Option::Some(l)) => {
                    match &l.car {
                        super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                        _ => panic!("Expected a Value::UnqualifiedSymbol"),
                    }
                    match &l.cdr {
                        super::ValueList(Option::Some(l)) => {
                            match &l.car {
                                super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym2"),
                                _ => panic!("Expected a Value::UnqualifiedSymbol"),
                            }
                            match &l.cdr {
                                super::ValueList(Option::Some(l)) => {
                                    match &l.car {
                                        super::Value::UnqualifiedSymbol(s) => {
                                            assert_eq!(s.0, "uqsym3")
                                        }
                                        _ => panic!("Expected a Value::UnqualifiedSymbol"),
                                    }
                                    assert_eq!(
                                        l.cdr,
                                        super::ValueList::<super::ValueTypesStatic>(Option::None)
                                    );
                                }
                                _ => panic!("Expected a ValueList(Option::Some)"),
                            }
                        }
                        _ => panic!("Expected a ValueList(Option::Some)"),
                    }
                }
                _ => panic!("Expected a ValueList(Option::Some)"),
            }
        }

        #[test]
        fn test_v_list_macro() {
            const LIST1: super::Value<super::ValueTypesStatic> = v_list!();
            assert_eq!(
                LIST1,
                super::Value::<super::ValueTypesStatic>::List(list!())
            );

            const LIST2: super::Value<super::ValueTypesStatic> = v_list!(v_uqsym!("uqsym1"));
            assert_eq!(
                LIST2,
                super::Value::<super::ValueTypesStatic>::List(list!(v_uqsym!("uqsym1")))
            );

            const LIST3: super::Value<super::ValueTypesStatic> =
                v_list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"));
            assert_eq!(
                LIST3,
                super::Value::<super::ValueTypesStatic>::List(list!(
                    v_uqsym!("uqsym1"),
                    v_uqsym!("uqsym2")
                ))
            );

            const LIST4: super::Value<super::ValueTypesStatic> =
                v_list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"), v_uqsym!("uqsym3"));
            assert_eq!(
                LIST4,
                super::Value::<super::ValueTypesStatic>::List(list!(
                    v_uqsym!("uqsym1"),
                    v_uqsym!("uqsym2"),
                    v_uqsym!("uqsym3")
                ))
            );
        }
    }

    #[test]
    fn test_semver_compare() {
        use more_asserts::*;

        assert_eq!(v![1, 0], v![1, 0]);
        assert_ne!(v![1, 0], v![1, 0, 0]);
        assert_lt!(v![1, 0], v![1, 0, 0]);
        assert_lt!(v![1, 0], v![1, 1]);
        assert_lt!(v![1, 1], v![2, 0]);
        assert_lt!(v![1, 1], v![2]);
        assert_ne!(v![1, 0, 0], v![1, 0]);
        assert_gt!(v![1, 0, 0], v![1, 0]);
        assert_gt!(v![1, 1], v![1, 0]);
        assert_gt!(v![2, 0], v![1, 1]);
        assert_gt!(v![2], v![1, 1]);
    }

    #[test]
    fn test_eq() {
        assert_eq!(v_list!(), v_list!());
        assert_eq!(v_list!(v_uqsym!("uqsym")), v_list!(v_uqsym!("uqsym")));
        assert_ne!(v_list!(v_uqsym!("uqsym1")), v_list!(v_uqsym!("v_uqsym2")));
        assert_ne!(v_list!(v_str!("uqsym")), v_list!(v_uqsym!("v_uqsym")));
        assert_ne!(v_list!(v_uqsym!("uqsym")), v_uqsym!("uqsym"));

        assert_eq!(v_uqsym!("uqsym"), v_uqsym!("uqsym"));
        assert_eq!(
            v_uqsym!("uqsym"),
            Value::<ValueTypesRc>::UnqualifiedSymbol(ValueUnqualifiedSymbol("uqsym".to_string()))
        );
        assert_ne!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"));
        assert_ne!(
            v_uqsym!("uqsym1"),
            Value::<ValueTypesRc>::UnqualifiedSymbol(ValueUnqualifiedSymbol("uqsym2".to_string()))
        );
        assert_ne!(v_uqsym!("uqsym"), v_str!("uqsym"));
        assert_ne!(v_uqsym!("uqsym"), v_list!());

        assert_eq!(v_qsym!("p", "qsym"), v_qsym!("p", "qsym"));
        assert_eq!(
            v_qsym!("p", "qsym"),
            Value::<ValueTypesRc>::QualifiedSymbol(ValueQualifiedSymbol {
                package: "p".to_string(),
                name: "qsym".to_string()
            })
        );
        assert_ne!(v_qsym!("p1", "qsym"), v_qsym!("p2", "qsym"));
        assert_ne!(v_qsym!("p", "qsym1"), v_qsym!("p", "qsym2"));
        assert_ne!(v_qsym!("p", "qsym"), v_uqsym!("qsym"));
        assert_ne!(v_qsym!("p", "qsym"), v_str!("p:qsym"));
        assert_ne!(v_qsym!("p", "qsym"), v_str!("p"));
        assert_ne!(v_qsym!("p", "qsym"), v_str!("qsym"));
        assert_ne!(v_qsym!("p", "qsym"), v_list!());

        assert_eq!(v_bool!(true), v_bool!(true));
        assert_ne!(v_bool!(true), v_bool!(false));
        assert_ne!(v_bool!(true), v_list!());

        assert_eq!(v_str!("str"), v_str!("str"));
        assert_eq!(
            v_str!("str"),
            Value::<ValueTypesRc>::String(ValueString("str".to_string()))
        );
        assert_ne!(v_str!("str1"), v_str!("str2"));
        assert_ne!(
            v_str!("str1"),
            Value::<ValueTypesRc>::String(ValueString("str2".to_string()))
        );
        assert_ne!(v_str!("str"), v_uqsym!("str"));
        assert_ne!(v_str!("str"), v_list!());

        assert_eq!(v_v![1, 0], v_v![1, 0]);
        assert_ne!(v_v![1, 0], v_v![1, 1]);
        assert_ne!(v_v![1, 0], v_list!());

        assert_eq!(v_lang_kira![1, 0], v_lang_kira![1, 0]);
        assert_ne!(v_lang_kira![1, 0], v_lang_kira![1, 1]);
        assert_ne!(v_lang_kira![1, 0], v_lang_other!("not-kira"));
        assert_ne!(v_lang_kira![1, 0], v_v![1, 0]);
        assert_ne!(v_lang_kira![1, 0], v_list!());

        assert_eq!(v_func!(qsym!("p", "f1")), v_func!(qsym!("p", "f1")));
        assert_ne!(v_func!(qsym!("p", "f1")), v_func!(qsym!("p", "f2")));
        assert_ne!(v_func!(qsym!("p", "f1")), v_qsym!("p", "f1"));
        assert_ne!(v_func!(qsym!("p", "f1")), v_list!());

        assert_eq!(v_bq!(v_bool!(true)), v_bq!(v_bool!(true)));
        assert_ne!(v_bq!(v_bool!(true)), v_bq!(v_bool!(false)));
        assert_ne!(v_bq!(v_bool!(true)), v_bq!(v_list!()));
        assert_ne!(v_bq!(v_bool!(true)), v_bool!(true));
        assert_ne!(v_bq!(v_bool!(true)), v_list!());

        assert_eq!(v_comma!(v_bool!(true)), v_comma!(v_bool!(true)));
        assert_ne!(v_comma!(v_bool!(true)), v_comma!(v_bool!(false)));
        assert_ne!(v_comma!(v_bool!(true)), v_comma!(v_list!()));
        assert_ne!(v_comma!(v_bool!(true)), v_bool!(true));
        assert_ne!(v_comma!(v_bool!(true)), v_bq!(v_bool!(true)));
        assert_ne!(v_comma!(v_bool!(true)), v_list!());

        assert_eq!(v_splice!(v_bool!(true)), v_splice!(v_bool!(true)));
        assert_ne!(v_splice!(v_bool!(true)), v_splice!(v_bool!(false)));
        assert_ne!(v_splice!(v_bool!(true)), v_splice!(v_list!()));
        assert_ne!(v_splice!(v_bool!(true)), v_bool!(true));
        assert_ne!(v_splice!(v_bool!(true)), v_bq!(v_bool!(true)));
        assert_ne!(v_splice!(v_bool!(true)), v_list!());
    }

    #[test]
    fn test_try_into_value_type_ref() {
        use std::convert::TryInto;

        let v = v_list!();
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v).unwrap(),
            &list!()
        );
        assert_eq!(
            TryInto::<&ValueString<StringTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_uqsym!("uqsym");
        assert_eq!(
            TryInto::<&ValueUnqualifiedSymbol<StringTypesStatic>>::try_into(&v).unwrap(),
            &uqsym!("uqsym")
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_qsym!("p", "qsym");
        assert_eq!(
            TryInto::<&ValueQualifiedSymbol<StringTypesStatic>>::try_into(&v).unwrap(),
            &qsym!("p", "qsym")
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_bool!(true);
        assert_eq!(TryInto::<&ValueBool>::try_into(&v).unwrap(), &bool!(true));
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_str!("str");
        assert_eq!(
            TryInto::<&ValueString<StringTypesStatic>>::try_into(&v).unwrap(),
            &str!("str")
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_v![1, 0];
        assert_eq!(
            TryInto::<&ValueSemver<SemverTypesStatic>>::try_into(&v).unwrap(),
            &v![1, 0]
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_lang_kira![1, 0];
        assert_eq!(
            TryInto::<&ValueLanguageDirective<StringTypesStatic, SemverTypesStatic>>::try_into(&v)
                .unwrap(),
            &lang_kira![1, 0]
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_func!(qsym!("p", "f1"));
        assert_eq!(
            TryInto::<&ValueFunction<StringTypesStatic>>::try_into(&v).unwrap(),
            &func!(qsym!("p", "f1"))
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_bq!(v_bool!(true));
        assert_eq!(
            TryInto::<&ValueBackquote<ValueTypesStatic>>::try_into(&v).unwrap(),
            &bq!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_comma!(v_bool!(true));
        assert_eq!(
            TryInto::<&ValueComma<ValueTypesStatic>>::try_into(&v).unwrap(),
            &comma!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_splice!(v_bool!(true));
        assert_eq!(
            TryInto::<&ValueSplice<ValueTypesStatic>>::try_into(&v).unwrap(),
            &splice!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<&ValueList<ValueTypesStatic>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );
    }

    #[test]
    fn test_try_into_value_type() {
        use std::convert::TryInto;

        let v = v_list!();
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v.clone()).unwrap(),
            list!()
        );
        assert_eq!(
            TryInto::<ValueString<StringTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_uqsym!("uqsym");
        assert_eq!(
            TryInto::<ValueUnqualifiedSymbol<StringTypesStatic>>::try_into(v.clone()).unwrap(),
            uqsym!("uqsym")
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_qsym!("p", "qsym");
        assert_eq!(
            TryInto::<ValueQualifiedSymbol<StringTypesStatic>>::try_into(v.clone()).unwrap(),
            qsym!("p", "qsym")
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_bool!(true);
        assert_eq!(
            TryInto::<ValueBool>::try_into(v.clone()).unwrap(),
            bool!(true)
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_str!("str");
        assert_eq!(
            TryInto::<ValueString<StringTypesStatic>>::try_into(v.clone()).unwrap(),
            str!("str")
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_v![1, 0];
        assert_eq!(
            TryInto::<ValueSemver<SemverTypesStatic>>::try_into(v.clone()).unwrap(),
            v![1, 0]
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_lang_kira![1, 0];
        assert_eq!(
            TryInto::<ValueLanguageDirective<StringTypesStatic, SemverTypesStatic>>::try_into(
                v.clone()
            )
            .unwrap(),
            lang_kira![1, 0]
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_func!(qsym!("p", "f1"));
        assert_eq!(
            TryInto::<ValueFunction<StringTypesStatic>>::try_into(v.clone()).unwrap(),
            func!(qsym!("p", "f1"))
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_bq!(v_bool!(true));
        assert_eq!(
            TryInto::<ValueBackquote<ValueTypesStatic>>::try_into(v.clone()).unwrap(),
            bq!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_comma!(v_bool!(true));
        assert_eq!(
            TryInto::<ValueComma<ValueTypesStatic>>::try_into(v.clone()).unwrap(),
            comma!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_splice!(v_bool!(true));
        assert_eq!(
            TryInto::<ValueSplice<ValueTypesStatic>>::try_into(v.clone()).unwrap(),
            splice!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<ValueList<ValueTypesStatic>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );
    }

    #[test]
    fn test_into_value() {
        let v: Value<ValueTypesStatic> = list!().into();
        assert_eq!(v, v_list!());

        let v: Value<ValueTypesStatic> = uqsym!("uqsym").into();
        assert_eq!(v, v_uqsym!("uqsym"));

        let v: Value<ValueTypesStatic> = qsym!("p", "qsym").into();
        assert_eq!(v, v_qsym!("p", "qsym"));

        let v: Value<ValueTypesStatic> = bool!(true).into();
        assert_eq!(v, v_bool!(true));

        let v: Value<ValueTypesStatic> = str!("str").into();
        assert_eq!(v, v_str!("str"));

        let v: Value<ValueTypesStatic> = v![1, 0].into();
        assert_eq!(v, v_v![1, 0]);

        let v: Value<ValueTypesStatic> = lang_kira![1, 0].into();
        assert_eq!(v, v_lang_kira![1, 0]);

        let v: Value<ValueTypesStatic> = func!(qsym!("p", "f1")).into();
        assert_eq!(v, v_func!(qsym!("p", "f1")));

        let v: Value<ValueTypesStatic> = bq!(v_bool!(true)).into();
        assert_eq!(v, v_bq!(v_bool!(true)));

        let v: Value<ValueTypesStatic> = comma!(v_bool!(true)).into();
        assert_eq!(v, v_comma!(v_bool!(true)));

        let v: Value<ValueTypesStatic> = splice!(v_bool!(true)).into();
        assert_eq!(v, v_splice!(v_bool!(true)));
    }

    #[test]
    fn test_iter() {
        let mut i = list!();
        assert!(i.next().is_none());
        assert_eq!(i, list!());

        let mut i = list!(v_uqsym!("uqsym"), v_bool!(true), v_str!("str"));
        assert_eq!(i.next().unwrap(), v_uqsym!("uqsym"));
        assert_eq!(i.next().unwrap(), v_bool!(true));
        assert_eq!(i, list!(v_str!("str")));
        assert_eq!(i.next().unwrap(), v_str!("str"));
        assert!(i.next().is_none());
        assert_eq!(i, list!());
    }
}
