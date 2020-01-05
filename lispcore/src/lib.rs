use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::convert::{TryFrom, TryInto};
use std::fmt::{Debug, Formatter};
use std::iter::FromIterator;
use std::rc::Rc;

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
    type Func: Fn(
            &mut (dyn Environment<Self> + 'static),
            &mut dyn Iterator<Item = Self::ValueRef>,
        ) -> Result<Self::ValueRef>
        + ?Sized;
    type FuncRef: Borrow<Self::Func>;
    type SemverTypes: SemverTypes;
}

pub trait Environment<T>
where
    T: ValueTypes + ?Sized,
    T::ValueRef: Clone,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn as_dyn_mut(&mut self) -> &mut (dyn Environment<T> + 'static);

    // TODO
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

pub struct ValueFunction<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub name: ValueQualifiedSymbol<T::StringRef>,
    pub func: T::FuncRef,
}

impl<T> Clone for ValueFunction<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::FuncRef: Clone,
    ValueQualifiedSymbol<T::StringRef>: Clone,
{
    fn clone(&self) -> Self {
        ValueFunction {
            name: self.name.clone(),
            func: self.func.clone(),
        }
    }
}

impl<T1, T2> PartialEq<ValueFunction<T2>> for ValueFunction<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    ValueQualifiedSymbol<T1::StringRef>: PartialEq<ValueQualifiedSymbol<T2::StringRef>>,
{
    fn eq(&self, rhs: &ValueFunction<T2>) -> bool {
        self.name == rhs.name
    }
}

impl<T> Debug for ValueFunction<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::StringRef: Debug,
{
    fn fmt(&self, fmt: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        fmt.debug_struct("ValueFunction")
            .field("name", &self.name)
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
pub struct ValueSemver<T>
where
    T: SemverTypes + ?Sized,
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>,
{
    pub major: u64,
    pub rest: T::SemverRef,
}

impl<T> Clone for ValueSemver<T>
where
    T: SemverTypes + ?Sized,
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>,
    T::SemverRef: Clone,
{
    fn clone(&self) -> Self {
        ValueSemver {
            major: self.major,
            rest: self.rest.clone(),
        }
    }
}

pub struct SemverIter<'v, T>
where
    T: SemverTypes + ?Sized,
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>,
{
    v: &'v ValueSemver<T>,
    iter: Option<<&'v T::Semver as IntoIterator>::IntoIter>,
}

impl<'v, T> Iterator for SemverIter<'v, T>
where
    T: SemverTypes + ?Sized,
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>,
{
    type Item = &'v u64;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            Option::None => {
                self.iter = Option::Some(self.v.rest.borrow().into_iter());
                Option::Some(&self.v.major)
            }
            Option::Some(i) => i.next(),
        }
    }
}

impl<T> ValueSemver<T>
where
    T: SemverTypes + ?Sized,
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>,
{
    fn items<'v>(&'v self) -> SemverIter<'v, T> {
        SemverIter {
            v: self,
            iter: Option::None,
        }
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
    S: Borrow<str>,
    V: SemverTypes + ?Sized,
    for<'a> &'a V::Semver: IntoIterator<Item = &'a u64>,
{
    Kira(ValueSemver<V>),
    Other(S),
}

impl<S, V> Clone for ValueLanguageDirective<S, V>
where
    S: Borrow<str> + Clone,
    V: SemverTypes + ?Sized,
    for<'a> &'a V::Semver: IntoIterator<Item = &'a u64>,
    V::SemverRef: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::Kira(v) => Self::Kira(v.clone()),
            Self::Other(s) => Self::Other(s.clone()),
        }
    }
}

impl<S1, V1, S2, V2> PartialEq<ValueLanguageDirective<S2, V2>> for ValueLanguageDirective<S1, V1>
where
    S1: Borrow<str>,
    S2: Borrow<str>,
    V1: SemverTypes + ?Sized,
    V2: SemverTypes + ?Sized,
    for<'a> &'a V1::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a V2::Semver: IntoIterator<Item = &'a u64>,
{
    fn eq(&self, rhs: &ValueLanguageDirective<S2, V2>) -> bool {
        eq_match!(self, rhs, {
            (ValueLanguageDirective::Kira(v1), ValueLanguageDirective::Kira(v2)) => v1 == v2,
            (ValueLanguageDirective::Other(n1), ValueLanguageDirective::Other(n2)) => n1.borrow() == n2.borrow(),
        })
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
    LanguageDirective(ValueLanguageDirective<T::StringRef, T::SemverTypes>),
    Function(ValueFunction<T>),
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
    T, ValueFunction<T>,
    (ValueFunction<T>: Clone),
    Value::Function(f) => (*f).clone()
);
try_from_value_ref!(T, ValueFunction<T>, Value::Function(p) => p);

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
from_value_type!(T, ValueFunction<T>, f -> Value::Function(f));

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
            (Value::LanguageDirective(l1), Value::LanguageDirective(l2)) => l1 == l2,
            (Value::Function(f1), Value::Function(f2)) => f1 == f2,
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
                Value::UnqualifiedSymbol(ValueUnqualifiedSymbol(s.clone().into()))
            }
            Value::QualifiedSymbol(ValueQualifiedSymbol { package, name }) => {
                Value::QualifiedSymbol(ValueQualifiedSymbol {
                    package: package.clone().into().into(),
                    name: name.clone().into().into(),
                })
            }
            Value::Cons(ValueCons { car, cdr }) => Value::Cons(ValueCons {
                car: Into::<Value<T2>>::into(car.borrow()).into(),
                cdr: Into::<Value<T2>>::into(cdr.borrow()).into(),
            }),
            Value::Bool(b) => Value::Bool(b.clone()),
            Value::String(ValueString(s)) => Value::String(ValueString(s.clone().into())),
            Value::Semver(ValueSemver { major, rest }) => Value::Semver(ValueSemver {
                major: *major,
                rest: rest.clone().into(),
            }),
            Value::LanguageDirective(l) => Value::<T2>::LanguageDirective(match l {
                ValueLanguageDirective::Kira(ValueSemver { major, rest }) => {
                    ValueLanguageDirective::Kira(ValueSemver {
                        major: *major,
                        rest: rest.clone().into(),
                    })
                }
                ValueLanguageDirective::Other(n) => ValueLanguageDirective::Other(n.clone().into()),
            }),
            Value::Function(_) => panic!("Cannot move functions across value type boundaries"),
        }
    }
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ValueType {
    List(ValueTypeList),
    NonList(ValueTypeNonList),
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ValueTypeList {
    pub items: BTreeSet<ValueType>,
    pub tail: BTreeSet<ValueTypeNonList>,
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ValueTypeNonList {
    Nil,
    UnqualifiedSymbol,
    QualifiedSymbol,
    Bool,
    String,
    Semver,
    LanguageDirective,
    Function,
}

impl<T> From<&Value<T>> for ValueType
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::ValueRef: Clone,
{
    fn from(v: &Value<T>) -> Self {
        match v {
            Value::Cons(c) => {
                let mut l = ValueTypeList {
                    items: BTreeSet::from_iter(vec![ValueType::from(c.car.borrow())]),
                    tail: BTreeSet::from_iter(vec![ValueTypeNonList::Nil]),
                };
                for item in LispList::<T>::new(c.cdr.clone()) {
                    match item {
                        LispListItem::Item(i) => {
                            l.items.insert(ValueType::from(i.borrow()));
                        }
                        LispListItem::Tail(t) => {
                            l.tail.clear();
                            l.tail.insert(ValueTypeNonList::from(t.borrow()));
                        }
                    }
                }
                ValueType::List(l)
            }
            _ => ValueType::NonList(ValueTypeNonList::from(v)),
        }
    }
}

impl<T> From<&Value<T>> for ValueTypeNonList
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::ValueRef: Clone,
{
    fn from(v: &Value<T>) -> Self {
        match v {
            Value::Nil => ValueTypeNonList::Nil,
            Value::UnqualifiedSymbol(_) => ValueTypeNonList::UnqualifiedSymbol,
            Value::QualifiedSymbol(_) => ValueTypeNonList::QualifiedSymbol,
            Value::Cons(_) => panic!("Unexpected Value::Cons"),
            Value::Bool(_) => ValueTypeNonList::Bool,
            Value::String(_) => ValueTypeNonList::String,
            Value::Semver(_) => ValueTypeNonList::Semver,
            Value::LanguageDirective(_) => ValueTypeNonList::LanguageDirective,
            Value::Function(_) => ValueTypeNonList::Function,
        }
    }
}

pub trait CompilerTypes
where
    for<'a> &'a <<Self::ValueTypes as ValueTypes>::SemverTypes as SemverTypes>::Semver:
        IntoIterator<Item = &'a u64>,
    <Self::ValueTypes as ValueTypes>::StringRef: std::fmt::Debug,
{
    type ValueTypes: ValueTypes + ?Sized;
    type Macro: Fn(
            <Self::ValueTypes as ValueTypes>::ValueRef,
        ) -> Result<TryCompilationResult<Self::ValueTypes>>
        + ?Sized;
    type MacroRef: Borrow<Self::Macro>;
}

#[derive(Debug)]
pub enum CompilationResultType<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::StringRef: std::fmt::Debug,
{
    Literal(T::ValueRef),
    SymbolDeref(ValueQualifiedSymbol<T::StringRef>),
    FunctionCall,
}

impl<T1, T2> PartialEq<CompilationResultType<T2>> for CompilationResultType<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T1::StringRef: std::fmt::Debug,
    T2::StringRef: std::fmt::Debug,
    <T1 as ValueTypes>::ValueRef: PartialEq<<T2 as ValueTypes>::ValueRef>,
{
    fn eq(&self, rhs: &CompilationResultType<T2>) -> bool {
        eq_match!(self, rhs, {
            (CompilationResultType::Literal(l1), CompilationResultType::Literal(l2)) => l1 == l2,
            (CompilationResultType::SymbolDeref(s1), CompilationResultType::SymbolDeref(s2)) => s1 == s2,
            (CompilationResultType::FunctionCall, CompilationResultType::FunctionCall) => true,
        })
    }
}

#[derive(Debug)]
pub struct CompilationResult<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::StringRef: std::fmt::Debug,
{
    pub result: CompilationResultType<T>,
    pub types: BTreeSet<ValueType>,
}

impl<T1, T2> PartialEq<CompilationResult<T2>> for CompilationResult<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T1::StringRef: std::fmt::Debug,
    T2::StringRef: std::fmt::Debug,
    CompilationResultType<T1>: PartialEq<CompilationResultType<T2>>,
{
    fn eq(&self, rhs: &CompilationResult<T2>) -> bool {
        self.result == rhs.result && self.types == rhs.types
    }
}

pub enum TryCompilationResult<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::StringRef: std::fmt::Debug,
{
    Compiled(CompilationResult<T>),
    Uncompiled(T::ValueRef),
}

impl<T1, T2> PartialEq<TryCompilationResult<T2>> for TryCompilationResult<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T1::StringRef: std::fmt::Debug,
    T2::StringRef: std::fmt::Debug,
    CompilationResult<T1>: PartialEq<CompilationResult<T2>>,
    T1::ValueRef: PartialEq<T2::ValueRef>,
{
    fn eq(&self, rhs: &TryCompilationResult<T2>) -> bool {
        eq_match!(self, rhs, {
            (TryCompilationResult::Compiled(r1), TryCompilationResult::Compiled(r2)) => r1 == r2,
            (TryCompilationResult::Uncompiled(r1), TryCompilationResult::Uncompiled(r2)) => r1 == r2,
        })
    }
}

pub trait Compiler<T>
where
    T: CompilerTypes + ?Sized,
    for<'a> &'a <<T::ValueTypes as ValueTypes>::SemverTypes as SemverTypes>::Semver:
        IntoIterator<Item = &'a u64>,
    <T::ValueTypes as ValueTypes>::StringRef: std::fmt::Debug,
    <T::ValueTypes as ValueTypes>::ValueRef: Clone,
{
    fn resolve_symbol_get_macro(
        &self,
        name: &ValueUnqualifiedSymbol<<T::ValueTypes as ValueTypes>::StringRef>,
    ) -> Result<ValueQualifiedSymbol<<T::ValueTypes as ValueTypes>::StringRef>>;

    fn get_macro(
        &self,
        name: &ValueQualifiedSymbol<<T::ValueTypes as ValueTypes>::StringRef>,
    ) -> Result<T::MacroRef>;

    fn compile(
        &self,
        v: <T::ValueTypes as ValueTypes>::ValueRef,
    ) -> Result<CompilationResult<T::ValueTypes>> {
        let mut result = TryCompilationResult::<T::ValueTypes>::Uncompiled(v);

        loop {
            match result {
                TryCompilationResult::Uncompiled(v) => {
                    result = match v.borrow() {
                        _ => {
                            let t = ValueType::from(v.borrow());
                            TryCompilationResult::Compiled(CompilationResult {
                                result: CompilationResultType::Literal(v),
                                types: BTreeSet::from_iter(vec![t]),
                            })
                        }
                    }
                }
                TryCompilationResult::Compiled(r) => return Result::Ok(r),
            }
        }
    }
}

pub struct CompilerTypesRc;

impl CompilerTypes for CompilerTypesRc {
    type ValueTypes = ValueTypesRc;
    type Macro = dyn Fn(
        <Self::ValueTypes as ValueTypes>::ValueRef,
    ) -> Result<TryCompilationResult<Self::ValueTypes>>;
    type MacroRef = Rc<Self::Macro>;
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

pub enum LispListItem<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    Item(T::ValueRef),
    Tail(T::ValueRef),
}

impl<T> LispListItem<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn try_unwrap_item(self) -> Result<T::ValueRef> {
        match self {
            LispListItem::Item(v) => Result::Ok(v),
            _ => Result::Err(Error::new(ErrorKind::IncorrectType, "Incorrect type")),
        }
    }

    pub fn unwrap_item(self) -> T::ValueRef {
        match self {
            LispListItem::Item(v) => v,
            _ => panic!("Expected LispListItem::Item"),
        }
    }

    pub fn unwrap_tail(self) -> T::ValueRef {
        match self {
            LispListItem::Tail(v) => v,
            _ => panic!("Expected LispListItem::Tail"),
        }
    }
}

pub struct LispList<T>
where
    T: ValueTypes + ?Sized,
    for<'b> &'b <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    T::ValueRef: Clone,
{
    ptr: Option<T::ValueRef>,
}

impl<T> LispList<T>
where
    T: ValueTypes + ?Sized,
    for<'b> &'b <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    T::ValueRef: Clone,
{
    pub fn new(ptr: T::ValueRef) -> Self {
        Self {
            ptr: LispList::<T>::filter_nil(ptr),
        }
    }

    pub fn take(self) -> Option<T::ValueRef> {
        self.ptr
    }

    fn filter_nil(v: T::ValueRef) -> Option<T::ValueRef> {
        match v.borrow() {
            Value::Nil => Option::None,
            _ => Option::Some(v),
        }
    }
}

impl<T> Iterator for LispList<T>
where
    T: ValueTypes + ?Sized,
    for<'b> &'b <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'b u64>,
    T::ValueRef: Clone,
{
    type Item = LispListItem<T>;

    fn next(&mut self) -> Option<Self::Item> {
        match &self.ptr {
            Option::Some(v) => match v.borrow() {
                Value::Cons(c) => {
                    let car = c.car.clone();
                    let cdr = c.cdr.clone();
                    self.ptr = LispList::<T>::filter_nil(cdr);
                    Option::Some(LispListItem::Item(car))
                }
                _ => {
                    let result = LispListItem::Tail(v.clone());
                    self.ptr = Option::None;
                    Option::Some(result)
                }
            },
            Option::None => Option::None,
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
    type Func = dyn Fn(
        &mut (dyn Environment<Self> + 'static),
        &mut dyn Iterator<Item = Self::ValueRef>,
    ) -> Result<Self::ValueRef>;
    type FuncRef = Rc<Self::Func>;
    type SemverTypes = SemverTypesVec;
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
    type Func = &'static dyn Fn(
        &mut (dyn Environment<Self> + 'static),
        &mut dyn Iterator<Item = Self::ValueRef>,
    ) -> Result<Self::ValueRef>;
    type FuncRef = Self::Func;
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
    ($major: expr, $rest:expr) => {{
        const V: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::Semver($crate::ValueSemver {
                major: $major as u64,
                rest: $rest as &[u64],
            });
        V
    }};
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
macro_rules! lang_ref {
    ($lang:expr) => {{
        const L: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::LanguageDirective($lang);
        L
    }};
}

#[macro_export]
macro_rules! lang_kira_ref {
    ($major:expr, $rest:expr) => {
        lang_ref!($crate::ValueLanguageDirective::Kira($crate::ValueSemver {
            major: $major as u64,
            rest: $rest as &[u64]
        }))
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
macro_rules! lang_other {
    ($name:expr) => {
        lang_ref!($crate::ValueLanguageDirective::Other($name))
    };
}

#[macro_export]
macro_rules! func {
    ($name:expr, $func:expr) => {{
        const P: &$crate::Value<$crate::ValueTypesStatic> =
            &$crate::Value::Function($crate::ValueFunction {
                name: $name,
                func: $func,
            });
        P
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
    fn static_f1(
        _: &mut (dyn super::Environment<super::ValueTypesStatic> + 'static),
        _: &mut dyn Iterator<Item = &'static super::Value<super::ValueTypesStatic>>,
    ) -> super::Result<&'static super::Value<super::ValueTypesStatic>> {
        super::Result::Ok(&super::Value::Nil)
    }

    fn static_f2(
        _: &mut (dyn super::Environment<super::ValueTypesStatic> + 'static),
        _: &mut dyn Iterator<Item = &'static super::Value<super::ValueTypesStatic>>,
    ) -> super::Result<&'static super::Value<super::ValueTypesStatic>> {
        super::Result::Ok(&super::Value::String(super::ValueString("str")))
    }

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
        const V1: &super::Value<super::ValueTypesStatic> = vref!(1u64, &[0u64]);
        match &*V1 {
            super::Value::Semver(v) => {
                assert_eq!(v.major, 1);
                assert_eq!(v.rest, &[0]);
            }
            _ => panic!("Expected a Value::Semver"),
        }

        const V2: &super::Value<super::ValueTypesStatic> = vref!(4u64, &[]);
        match &*V2 {
            super::Value::Semver(v) => {
                assert_eq!(v.major, 4);
                assert_eq!(v.rest, &[]);
            }
            _ => panic!("Expected a Value::Semver"),
        }
    }

    #[test]
    fn test_v_macro() {
        const V1: &super::Value<super::ValueTypesStatic> = v![2, 1];
        match &*V1 {
            super::Value::Semver(v) => {
                assert_eq!(v.major, 2);
                assert_eq!(v.rest, &[1]);
            }
            _ => panic!("Expected a Value::Semver"),
        }

        const V2: &super::Value<super::ValueTypesStatic> = v![3];
        match &*V2 {
            super::Value::Semver(v) => {
                assert_eq!(v.major, 3);
                assert_eq!(v.rest, &[]);
            }
            _ => panic!("Expected a Value::Semver"),
        }
    }

    #[test]
    fn test_lang_kira_macro() {
        const L1: &super::Value<super::ValueTypesStatic> = lang_kira![1];
        match &*L1 {
            super::Value::LanguageDirective(super::ValueLanguageDirective::Kira(v)) => {
                assert_eq!(v.major, 1);
                assert_eq!(v.rest, &[]);
            }
            _ => panic!("Expected a Value::LanguageDirective with Kira"),
        }

        const L2: &super::Value<super::ValueTypesStatic> = lang_kira![1, 0];
        match &*L2 {
            super::Value::LanguageDirective(super::ValueLanguageDirective::Kira(v)) => {
                assert_eq!(v.major, 1);
                assert_eq!(v.rest, &[0]);
            }
            _ => panic!("Expected a Value::LanguageDirective with Kira"),
        }
    }

    #[test]
    fn test_lang_other_macro() {
        const L1: &super::Value<super::ValueTypesStatic> = lang_other!("not-kira");
        match &*L1 {
            super::Value::LanguageDirective(super::ValueLanguageDirective::Other(n)) => {
                assert_eq!(n, &"not-kira");
            }
            _ => panic!("Expected a Value::LanguageDirective with other"),
        }
    }

    #[test]
    fn test_func_macro() {
        const P: &super::Value<super::ValueTypesStatic> = func!(
            super::ValueQualifiedSymbol {
                package: "p",
                name: "f1"
            },
            &static_f1
        );
        match &*P {
            super::Value::Function(super::ValueFunction { name, func: _ }) => assert_eq!(
                name,
                &super::ValueQualifiedSymbol::<&'static str> {
                    package: "p",
                    name: "f1"
                }
            ),
            _ => panic!("Expected a Value::Function"),
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
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            },
        );

        assert_ne!(
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64, 0u64] as &[u64]
            },
        );

        assert_lt!(
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64, 0u64] as &[u64]
            },
        );

        assert_lt!(
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[1u64] as &[u64]
            },
        );

        assert_lt!(
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[1u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 2u64,
                rest: &[0u64] as &[u64]
            },
        );

        assert_lt!(
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[1u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 2u64,
                rest: &[] as &[u64]
            },
        );

        assert_ne!(
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64, 0u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            },
        );

        assert_gt!(
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64, 0u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            },
        );

        assert_gt!(
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[1u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            },
        );

        assert_gt!(
            ValueSemver::<SemverTypesStatic> {
                major: 2u64,
                rest: &[0u64] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[1u64] as &[u64]
            },
        );

        assert_gt!(
            ValueSemver::<SemverTypesStatic> {
                major: 2u64,
                rest: &[] as &[u64]
            },
            ValueSemver::<SemverTypesStatic> {
                major: 1u64,
                rest: &[1u64] as &[u64]
            },
        );
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

        assert_eq!(lang_kira![1, 0], lang_kira![1, 0]);
        assert_ne!(lang_kira![1, 0], lang_kira![1, 1]);
        assert_ne!(lang_kira![1, 0], lang_other!("not-kira"));
        assert_ne!(lang_kira![1, 0], v![1, 0]);
        assert_ne!(lang_kira![1, 0], nil!());

        const F1_NAME: super::ValueQualifiedSymbol<&'static str> = super::ValueQualifiedSymbol {
            package: "p",
            name: "f1",
        };
        const F2_NAME: super::ValueQualifiedSymbol<&'static str> = super::ValueQualifiedSymbol {
            package: "p",
            name: "f2",
        };
        assert_eq!(func!(F1_NAME, &static_f1), func!(F1_NAME, &static_f1));
        assert_eq!(func!(F1_NAME, &static_f1), func!(F1_NAME, &static_f2));
        assert_ne!(func!(F1_NAME, &static_f1), func!(F2_NAME, &static_f1));
        assert_ne!(func!(F1_NAME, &static_f1), func!(F2_NAME, &static_f2));
        assert_ne!(func!(F1_NAME, &static_f1), nil!());
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
            &ValueSemver::<<ValueTypesStatic as ValueTypes>::SemverTypes> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        const F1_NAME: ValueQualifiedSymbol<&'static str> = ValueQualifiedSymbol {
            package: "p",
            name: "f1",
        };
        let v = func!(F1_NAME, &static_f1);
        assert_eq!(
            TryInto::<&ValueFunction<ValueTypesStatic>>::try_into(v).unwrap(),
            &ValueFunction::<ValueTypesStatic> {
                name: F1_NAME,
                func: &static_f1,
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
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
            ValueSemver::<<ValueTypesStatic as ValueTypes>::SemverTypes> {
                major: 1u64,
                rest: &[0u64] as &[u64]
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        const F1_NAME: ValueQualifiedSymbol<&'static str> = ValueQualifiedSymbol {
            package: "p",
            name: "f1",
        };
        let v = func!(F1_NAME, &static_f1);
        assert_eq!(
            TryInto::<ValueFunction<ValueTypesStatic>>::try_into(v).unwrap(),
            ValueFunction::<ValueTypesStatic> {
                name: F1_NAME,
                func: &static_f1,
            }
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
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

        const F1_NAME: ValueQualifiedSymbol<&'static str> = ValueQualifiedSymbol {
            package: "p",
            name: "f1",
        };
        let v: Value<ValueTypesStatic> = ValueFunction::<ValueTypesStatic> {
            name: F1_NAME.clone(),
            func: &static_f1,
        }
        .into();
        assert_eq!(
            v,
            Value::<ValueTypesStatic>::Function(ValueFunction {
                name: F1_NAME.clone(),
                func: &static_f1,
            })
        );
    }

    #[test]
    fn test_lisp_list() {
        use super::*;

        let mut i =
            LispList::<ValueTypesStatic>::new(list!(uqsym!("uqsym"), bool!(true), str!("str")));
        assert_eq!(i.next().unwrap().unwrap_item(), uqsym!("uqsym"));
        assert_eq!(i.next().unwrap().unwrap_item(), bool!(true));
        assert_eq!(i.next().unwrap().unwrap_item(), str!("str"));
        assert!(i.next().is_none());
        assert_eq!(i.take(), Option::None);

        let mut i = LispList::<ValueTypesStatic>::new(cons!(uqsym!("uqsym"), bool!(true)));
        assert_eq!(i.next().unwrap().unwrap_item(), uqsym!("uqsym"));
        assert_eq!(i.next().unwrap().unwrap_tail(), bool!(true));
        assert!(i.next().is_none());
        assert_eq!(i.take(), Option::None);

        let mut i =
            LispList::<ValueTypesStatic>::new(list!(uqsym!("uqsym"), bool!(true), str!("str")));
        assert_eq!(i.next().unwrap().unwrap_item(), uqsym!("uqsym"));
        assert_eq!(i.take(), Option::Some(list!(bool!(true), str!("str"))));

        let mut i =
            LispList::<ValueTypesStatic>::new(list!(uqsym!("uqsym"), bool!(true), str!("str")));
        assert_eq!(i.next().unwrap().unwrap_item(), uqsym!("uqsym"));
        assert_eq!(i.next().unwrap().unwrap_item(), bool!(true));
        assert_eq!(i.next().unwrap().unwrap_item(), str!("str"));
        assert_eq!(i.take(), Option::None);

        let i = LispList::<ValueTypesStatic>::new(nil!());
        assert_eq!(i.take(), Option::None);
    }

    #[test]
    fn test_from_non_list() {
        use super::*;

        assert_eq!(ValueTypeNonList::from(nil!()), ValueTypeNonList::Nil);
        assert_eq!(
            ValueTypeNonList::from(uqsym!("uqsym")),
            ValueTypeNonList::UnqualifiedSymbol
        );
        assert_eq!(
            ValueTypeNonList::from(qsym!("p", "qsym")),
            ValueTypeNonList::QualifiedSymbol
        );
        assert_eq!(ValueTypeNonList::from(bool!(true)), ValueTypeNonList::Bool);
        assert_eq!(
            ValueTypeNonList::from(str!("str")),
            ValueTypeNonList::String
        );
        assert_eq!(ValueTypeNonList::from(v![1, 0]), ValueTypeNonList::Semver);
        assert_eq!(
            ValueTypeNonList::from(lang_kira![1, 0]),
            ValueTypeNonList::LanguageDirective
        );
        assert_eq!(
            ValueTypeNonList::from(func!(
                ValueQualifiedSymbol {
                    package: "p",
                    name: "f1"
                },
                &static_f1
            )),
            ValueTypeNonList::Function
        );
    }

    #[test]
    fn test_from_list() {
        use super::*;

        assert_eq!(
            ValueType::from(list!(
                nil!(),
                bool!(true),
                str!("str"),
                cons!(uqsym!("uqsym"), cons!(bool!(true), qsym!("p", "qsym")))
            )),
            ValueType::List(ValueTypeList {
                items: BTreeSet::from_iter(vec![
                    ValueType::NonList(ValueTypeNonList::Nil),
                    ValueType::NonList(ValueTypeNonList::Bool),
                    ValueType::NonList(ValueTypeNonList::String),
                    ValueType::List(ValueTypeList {
                        items: BTreeSet::from_iter(vec![
                            ValueType::NonList(ValueTypeNonList::UnqualifiedSymbol),
                            ValueType::NonList(ValueTypeNonList::Bool),
                        ]),
                        tail: BTreeSet::from_iter(vec![ValueTypeNonList::QualifiedSymbol]),
                    }),
                ]),
                tail: BTreeSet::from_iter(vec![ValueTypeNonList::Nil]),
            })
        );
    }

    struct SimpleCompiler;

    impl super::Compiler<super::CompilerTypesRc> for SimpleCompiler {
        fn resolve_symbol_get_macro(
            &self,
            _name: &super::ValueUnqualifiedSymbol<
                <super::ValueTypesRc as super::ValueTypes>::StringRef,
            >,
        ) -> super::Result<
            super::ValueQualifiedSymbol<<super::ValueTypesRc as super::ValueTypes>::StringRef>,
        > {
            super::Result::Err(super::Error::new(
                super::ErrorKind::NoPackageForSymbol,
                "No package for symbol",
            ))
        }

        fn get_macro(
            &self,
            _name: &super::ValueQualifiedSymbol<
                <super::ValueTypesRc as super::ValueTypes>::StringRef,
            >,
        ) -> super::Result<<super::CompilerTypesRc as super::CompilerTypes>::MacroRef> {
            super::Result::Err(super::Error::new(
                super::ErrorKind::ValueNotDefined,
                "Value not defined",
            ))
        }
    }

    fn test_literal(
        comp: &SimpleCompiler,
        code: <super::ValueTypesStatic as super::ValueTypes>::ValueRef,
        t: super::ValueType,
    ) {
        use super::*;

        assert_eq!(
            comp.compile(value_type_convert::<ValueTypesStatic, ValueTypesRc>(code))
                .unwrap(),
            CompilationResult::<ValueTypesRc> {
                result: CompilationResultType::Literal(value_type_convert::<
                    ValueTypesStatic,
                    ValueTypesRc,
                >(code)),
                types: BTreeSet::from_iter(vec![t]),
            }
        );
    }

    #[test]
    fn test_compile_literal() {
        use super::*;

        let comp = SimpleCompiler;
        test_literal(&comp, nil!(), ValueType::NonList(ValueTypeNonList::Nil));
        test_literal(
            &comp,
            bool!(true),
            ValueType::NonList(ValueTypeNonList::Bool),
        );
        test_literal(
            &comp,
            str!("Hello world!"),
            ValueType::NonList(ValueTypeNonList::String),
        );
        test_literal(
            &comp,
            v![1, 0],
            ValueType::NonList(ValueTypeNonList::Semver),
        );
    }
}
