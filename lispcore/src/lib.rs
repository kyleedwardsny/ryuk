use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::convert::TryFrom;
use std::fmt::{Debug, Formatter};
use std::iter::FromIterator;
use std::rc::Rc;

macro_rules! eq_match {
    ($lhs: expr, $rhs:expr, { $(($lpat:pat, $rpat:pat) => $result:expr,)* }) => {
        match $lhs {
            $($lpat => match $rhs {
                $rpat => $result,
                _ => false,
            }),*
        }
    };
}

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub error: Box<dyn std::error::Error>,
}

impl Error {
    pub fn new(kind: ErrorKind, error: impl Into<Box<dyn std::error::Error>>) -> Error {
        Error {
            kind,
            error: error.into(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    IncorrectType,
    ValueNotDefined,
    NotAFunction,
    NoPackageForSymbol,
    IncorrectParams,
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        std::fmt::Display::fmt(&self.error, formatter)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub trait ValueTypes: Debug
where
    for<'a> &'a <Self::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    type ConsRef: Borrow<Cons<Self>> + Clone + Debug;
    type StringRef: Borrow<str> + Clone + Debug;
    type SemverTypes: SemverTypes + ?Sized;
}

pub trait Environment<T>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    Value<T>: Clone,
{
    fn as_dyn_mut(&mut self) -> &mut (dyn Environment<T> + 'static);

    fn resolve_symbol_get_macro(
        &self,
        name: &ValueUnqualifiedSymbol<T::StringRef>,
    ) -> Option<ValueQualifiedSymbol<T::StringRef>>;

    fn compile_function(
        &self,
        name: &ValueQualifiedSymbol<T::StringRef>,
        params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
    ) -> Option<Result<BTreeSet<ValueType>>>;

    fn compile_function_from_macro(
        &mut self,
        name: &ValueQualifiedSymbol<T::StringRef>,
        params: LispList<T>,
    ) -> Option<Result<TryCompilationResult<T>>> {
        let mut compiled_params = Vec::new();
        for item in params.map(|v| self.compile(v.try_unwrap_item()?)) {
            match item {
                Result::Ok(r) => compiled_params.push(r),
                Result::Err(e) => return Option::Some(Result::Err(e)),
            }
        }

        Option::Some(
            match self
                .compile_function(name, &mut (&compiled_params).into_iter().map(|p| &p.types))?
            {
                Result::Ok(r) => Result::Ok(TryCompilationResult::Compiled(CompilationResult {
                    result: Box::new(FunctionCall::new(
                        ValueFunction(name.clone()),
                        compiled_params.into_iter().map(|p| p.result).collect(),
                    )),
                    types: r,
                })),
                Result::Err(e) => Result::Err(e),
            },
        )
    }

    fn evaluate_function(
        &mut self,
        name: &ValueQualifiedSymbol<T::StringRef>,
        params: Vec<Value<T>>,
    ) -> Result<Value<T>>;

    fn compile_macro(
        &mut self,
        name: &ValueQualifiedSymbol<T::StringRef>,
        params: LispList<T>,
    ) -> Option<Result<TryCompilationResult<T>>>;

    fn compile(&mut self, v: Value<T>) -> Result<CompilationResult<T>> {
        let mut result = TryCompilationResult::<T>::Uncompiled(v);

        loop {
            match result {
                TryCompilationResult::Uncompiled(v) => {
                    result = match v {
                        Value::Cons(ValueCons(c)) => {
                            let cons = c.borrow();
                            let name = match &cons.car {
                                Value::UnqualifiedSymbol(name) => {
                                    match self.resolve_symbol_get_macro(name) {
                                        Option::Some(name) => name,
                                        Option::None => {
                                            return Result::Err(Error::new(
                                                ErrorKind::ValueNotDefined,
                                                "Value not defined",
                                            ))
                                        }
                                    }
                                }
                                Value::QualifiedSymbol(name) => (*name).clone(),
                                _ => {
                                    return Result::Err(Error::new(
                                        ErrorKind::IncorrectType,
                                        "Incorrect type",
                                    ))
                                }
                            };
                            match self.compile_macro(&name, cons.cdr.clone().into_iter()) {
                                Option::Some(r) => r?,
                                Option::None => {
                                    return Result::Err(Error::new(
                                        ErrorKind::ValueNotDefined,
                                        "Value not defined",
                                    ))
                                }
                            }
                        }
                        _ => {
                            let t = v.value_type();
                            TryCompilationResult::Compiled(CompilationResult {
                                result: Box::new(Literal::new(v)),
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

#[derive(Clone, Debug)]
pub struct ValueUnqualifiedSymbol<S>(pub S)
where
    S: Borrow<str> + Clone;

impl<S> ValueUnqualifiedSymbol<S>
where
    S: Borrow<str> + Clone,
{
    pub fn convert<S2>(&self) -> ValueUnqualifiedSymbol<S2>
    where
        S2: Borrow<str> + Clone,
        for<'a> &'a str: Into<S2>,
    {
        ValueUnqualifiedSymbol(self.0.borrow().into())
    }
}

impl<S1, S2> PartialEq<ValueUnqualifiedSymbol<S2>> for ValueUnqualifiedSymbol<S1>
where
    S1: Borrow<str> + Clone,
    S2: Borrow<str> + Clone,
{
    fn eq(&self, rhs: &ValueUnqualifiedSymbol<S2>) -> bool {
        self.0.borrow() == rhs.0.borrow()
    }
}

#[derive(Clone, Debug)]
pub struct ValueQualifiedSymbol<S>
where
    S: Borrow<str> + Clone,
{
    pub package: S,
    pub name: S,
}

impl<S> ValueQualifiedSymbol<S>
where
    S: Borrow<str> + Clone,
{
    pub fn convert<S2>(&self) -> ValueQualifiedSymbol<S2>
    where
        S2: Borrow<str> + Clone,
        for<'a> &'a str: Into<S2>,
    {
        ValueQualifiedSymbol {
            package: self.package.borrow().into(),
            name: self.name.borrow().into(),
        }
    }
}

impl<S1, S2> PartialEq<ValueQualifiedSymbol<S2>> for ValueQualifiedSymbol<S1>
where
    S1: Borrow<str> + Clone,
    S2: Borrow<str> + Clone,
{
    fn eq(&self, rhs: &ValueQualifiedSymbol<S2>) -> bool {
        self.package.borrow() == rhs.package.borrow() && self.name.borrow() == rhs.name.borrow()
    }
}

#[derive(Debug)]
pub struct ValueCons<T>(pub T::ConsRef)
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>;

impl<T> ValueCons<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn convert<T2>(&self) -> ValueCons<T2>
    where
        T2: ValueTypes + ?Sized,
        for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
        for<'a> &'a str: Into<T2::StringRef>,
        Cons<T2>: Into<T2::ConsRef>,
        for<'a> &'a <T::SemverTypes as SemverTypes>::Semver:
            Into<<T2::SemverTypes as SemverTypes>::SemverRef>,
    {
        let cons = self.0.borrow();
        ValueCons(
            Cons {
                car: cons.car.convert::<T2>(),
                cdr: cons.cdr.convert::<T2>(),
            }
            .into(),
        )
    }
}

impl<T> Clone for ValueCons<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T1, T2> PartialEq<ValueCons<T2>> for ValueCons<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    <T1 as ValueTypes>::ConsRef: PartialEq<<T2 as ValueTypes>::ConsRef>,
{
    fn eq(&self, other: &ValueCons<T2>) -> bool {
        self.0 == other.0
    }
}

#[derive(Debug)]
pub struct Cons<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub car: Value<T>,
    pub cdr: Value<T>,
}

impl<T> Clone for Cons<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
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
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    Value<T1>: PartialEq<Value<T2>>,
{
    fn eq(&self, other: &Cons<T2>) -> bool {
        self.car == other.car && self.cdr == other.cdr
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ValueBool(pub bool);

#[derive(Debug)]
pub struct ValueString<S>(pub S)
where
    S: Borrow<str> + Clone;

impl<S> ValueString<S>
where
    S: Borrow<str> + Clone,
{
    pub fn convert<S2>(&self) -> ValueString<S2>
    where
        S2: Borrow<str> + Clone,
        for<'a> &'a str: Into<S2>,
    {
        ValueString(self.0.borrow().into())
    }
}

impl<S> Clone for ValueString<S>
where
    S: Borrow<str> + Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<S1, S2> PartialEq<ValueString<S2>> for ValueString<S1>
where
    S1: Borrow<str> + Clone,
    S2: Borrow<str> + Clone,
{
    fn eq(&self, rhs: &ValueString<S2>) -> bool {
        self.0.borrow() == rhs.0.borrow()
    }
}

pub trait SemverTypes: Debug
where
    for<'a> &'a Self::Semver: IntoIterator<Item = &'a u64>,
{
    type Semver: ?Sized;
    type SemverRef: Borrow<Self::Semver> + Clone + Debug;
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

impl<T> ValueSemver<T>
where
    T: SemverTypes + ?Sized,
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn convert<T2>(&self) -> ValueSemver<T2>
    where
        T2: SemverTypes + ?Sized,
        for<'a> &'a T2::Semver: IntoIterator<Item = &'a u64>,
        for<'a> &'a T::Semver: Into<T2::SemverRef>,
    {
        ValueSemver {
            major: self.major,
            rest: self.rest.borrow().into(),
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
    for<'a> &'a T::Semver: IntoIterator<Item = &'a u64>,
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
    S: Borrow<str> + Clone,
    V: SemverTypes + ?Sized,
    for<'a> &'a V::Semver: IntoIterator<Item = &'a u64>,
{
    Kira(ValueSemver<V>),
    Other(S),
}

impl<S, V> ValueLanguageDirective<S, V>
where
    S: Borrow<str> + Clone,
    V: SemverTypes + ?Sized,
    for<'a> &'a V::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn convert<S2, V2>(&self) -> ValueLanguageDirective<S2, V2>
    where
        S2: Borrow<str> + Clone,
        V2: SemverTypes + ?Sized,
        for<'a> &'a V2::Semver: IntoIterator<Item = &'a u64>,
        for<'a> &'a V::Semver: Into<V2::SemverRef>,
        for<'a> &'a str: Into<S2>,
    {
        match self {
            ValueLanguageDirective::Kira(v) => ValueLanguageDirective::Kira(v.convert::<V2>()),
            ValueLanguageDirective::Other(name) => {
                ValueLanguageDirective::Other(name.borrow().into())
            }
        }
    }
}

impl<S, V> Clone for ValueLanguageDirective<S, V>
where
    S: Borrow<str> + Clone,
    V: SemverTypes + ?Sized,
    for<'a> &'a V::Semver: IntoIterator<Item = &'a u64>,
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
    S1: Borrow<str> + Clone,
    S2: Borrow<str> + Clone,
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
pub struct ValueFunction<S>(pub ValueQualifiedSymbol<S>)
where
    S: Borrow<str> + Clone;

impl<S> ValueFunction<S>
where
    S: Borrow<str> + Clone,
{
    pub fn convert<S2>(&self) -> ValueFunction<S2>
    where
        S2: Borrow<str> + Clone,
        for<'a> &'a str: Into<S2>,
    {
        ValueFunction(self.0.convert())
    }
}

impl<S1, S2> PartialEq<ValueFunction<S2>> for ValueFunction<S1>
where
    S1: Borrow<str> + Clone,
    S2: Borrow<str> + Clone,
    ValueQualifiedSymbol<S1>: PartialEq<ValueQualifiedSymbol<S2>>,
{
    fn eq(&self, rhs: &ValueFunction<S2>) -> bool {
        self.0 == rhs.0
    }
}

impl<S> Clone for ValueFunction<S>
where
    S: Borrow<str> + Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
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
    Function(ValueFunction<T::StringRef>),
}

impl<T> Value<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn convert<T2>(&self) -> Value<T2>
    where
        T2: ValueTypes + ?Sized,
        for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
        for<'a> &'a str: Into<T2::StringRef>,
        Cons<T2>: Into<T2::ConsRef>,
        for<'a> &'a <T::SemverTypes as SemverTypes>::Semver:
            Into<<T2::SemverTypes as SemverTypes>::SemverRef>,
    {
        match self {
            Value::Nil => Value::Nil,
            Value::UnqualifiedSymbol(s) => Value::UnqualifiedSymbol(s.convert::<T2::StringRef>()),
            Value::QualifiedSymbol(s) => Value::QualifiedSymbol(s.convert::<T2::StringRef>()),
            Value::Cons(c) => Value::Cons(c.convert::<T2>()),
            Value::Bool(b) => Value::Bool(b.clone()),
            Value::String(s) => Value::String(s.convert::<T2::StringRef>()),
            Value::Semver(v) => Value::Semver(v.convert::<T2::SemverTypes>()),
            Value::LanguageDirective(l) => {
                Value::LanguageDirective(l.convert::<T2::StringRef, T2::SemverTypes>())
            }
            Value::Function(f) => Value::Function(f.convert::<T2::StringRef>()),
        }
    }

    pub fn value_type(&self) -> ValueType {
        match self {
            Value::Cons(c) => {
                let cons = c.0.borrow();
                let mut l = ValueTypeList {
                    items: BTreeSet::from_iter(vec![cons.car.value_type()]),
                    tail: BTreeSet::from_iter(vec![ValueTypeNonList::Nil]),
                };
                for item in cons.cdr.clone().into_iter() {
                    match item {
                        LispListItem::Item(i) => {
                            l.items.insert(i.value_type());
                        }
                        LispListItem::Tail(t) => {
                            l.tail.clear();
                            l.tail.insert(t.value_type_non_list());
                        }
                    }
                }
                ValueType::List(l)
            }
            _ => ValueType::NonList(self.value_type_non_list()),
        }
    }

    pub fn value_type_non_list(&self) -> ValueTypeNonList {
        match self {
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

impl<T> IntoIterator for Value<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    type IntoIter = LispList<T>;
    type Item = LispListItem<T>;

    fn into_iter(self) -> Self::IntoIter {
        LispList { val: self }
    }
}

impl<T> Clone for Value<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn clone(&self) -> Self {
        match self {
            Value::Nil => Value::Nil,
            Value::UnqualifiedSymbol(s) => Value::UnqualifiedSymbol((*s).clone()),
            Value::QualifiedSymbol(s) => Value::QualifiedSymbol((*s).clone()),
            Value::Cons(c) => Value::Cons((*c).clone()),
            Value::Bool(b) => Value::Bool((*b).clone()),
            Value::String(s) => Value::String((*s).clone()),
            Value::Semver(v) => Value::Semver((*v).clone()),
            Value::LanguageDirective(l) => Value::LanguageDirective((*l).clone()),
            Value::Function(f) => Value::Function((*f).clone()),
        }
    }
}

macro_rules! try_from_value {
    ($l:lifetime, $t:ident, $in:ty, $out:ty, $match:pat => $result:expr) => {
        impl<$l, $t> TryFrom<$in> for $out
        where
            $t: ValueTypes + ?Sized,
            for<'a> &'a <$t::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
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

try_from_value!(T, (), Value::Nil => ());
try_from_value!(T, ValueUnqualifiedSymbol<T::StringRef>, Value::UnqualifiedSymbol(s) => s);
try_from_value!(T, ValueQualifiedSymbol<T::StringRef>, Value::QualifiedSymbol(s) => s);
try_from_value!(T, ValueCons<T>, Value::Cons(c) => c);
try_from_value!(T, ValueBool, Value::Bool(b) => b);
try_from_value!(T, ValueString<T::StringRef>, Value::String(s) => s);
try_from_value!(T, ValueSemver<T::SemverTypes>, Value::Semver(v) => v);
try_from_value!(T, ValueLanguageDirective<T::StringRef, T::SemverTypes>, Value::LanguageDirective(l) => l);
try_from_value!(T, ValueFunction<T::StringRef>, Value::Function(f) => f);

macro_rules! from_value_type {
    ($t:ident, $in:ty, $param:ident -> $result:expr) => {
        impl<$t> From<$in> for Value<$t>
        where
            $t: ValueTypes + ?Sized,
            for<'a> &'a <$t::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
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
from_value_type!(T, ValueLanguageDirective<T::StringRef, T::SemverTypes>, l -> Value::LanguageDirective(l));
from_value_type!(T, ValueFunction<T::StringRef>, f -> Value::Function(f));

impl<T1, T2> PartialEq<Value<T2>> for Value<T1>
where
    T1: ValueTypes + ?Sized,
    T2: ValueTypes + ?Sized,
    for<'a> &'a <T1::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    for<'a> &'a <T2::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn eq(&self, rhs: &Value<T2>) -> bool {
        eq_match!(self, rhs, {
            (Value::Nil, Value::Nil) => true,
            (Value::UnqualifiedSymbol(s1), Value::UnqualifiedSymbol(s2)) => s1 == s2,
            (Value::QualifiedSymbol(s1), Value::QualifiedSymbol(s2)) => s1 == s2,
            (Value::Cons(c1), Value::Cons(c2)) => {
                // This has to be a direct comparison to avoid a cyclic dependency when
                // calculating eligibility for PartialEq
                let cons1 = c1.0.borrow();
                let cons2 = c2.0.borrow();
                cons1.car == cons2.car && cons1.cdr == cons2.cdr
            },
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::String(s1), Value::String(s2)) => s1 == s2,
            (Value::Semver(v1), Value::Semver(v2)) => v1 == v2,
            (Value::LanguageDirective(l1), Value::LanguageDirective(l2)) => l1 == l2,
            (Value::Function(f1), Value::Function(f2)) => f1 == f2,
        })
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ValueType {
    List(ValueTypeList),
    NonList(ValueTypeNonList),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ValueTypeList {
    pub items: BTreeSet<ValueType>,
    pub tail: BTreeSet<ValueTypeNonList>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
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

pub trait CompilationResultType<T>: Debug
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>>;
}

#[derive(Debug)]
pub struct FunctionCall<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    name: ValueFunction<T::StringRef>,
    params: Vec<Box<dyn CompilationResultType<T>>>,
}

impl<T> FunctionCall<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn new(
        name: ValueFunction<T::StringRef>,
        params: Vec<Box<dyn CompilationResultType<T>>>,
    ) -> Self {
        FunctionCall { name, params }
    }
}

impl<T> CompilationResultType<T> for FunctionCall<T>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>> {
        use std::borrow::BorrowMut;

        let params = (&mut self.params)
            .into_iter()
            .map(|p| BorrowMut::<dyn CompilationResultType<T>>::borrow_mut(p).evaluate(env))
            .collect::<Result<Vec<Value<T>>>>()?;
        env.evaluate_function(&self.name.0, params)
    }
}

#[derive(Debug)]
pub struct Literal<T>(Value<T>)
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>;

impl<T> Literal<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn new(value: Value<T>) -> Self {
        Literal(value)
    }
}

impl<T> CompilationResultType<T> for Literal<T>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn evaluate(&mut self, _env: &mut dyn Environment<T>) -> Result<Value<T>> {
        Result::Ok(self.0.clone())
    }
}

#[derive(Debug)]
pub struct CompilationResult<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub result: Box<dyn CompilationResultType<T> + 'static>,
    pub types: BTreeSet<ValueType>,
}

pub enum TryCompilationResult<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    Compiled(CompilationResult<T>),
    Uncompiled(Value<T>),
}

pub enum LispListItem<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    Item(Value<T>),
    Tail(Value<T>),
}

impl<T> LispListItem<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn try_unwrap_item(self) -> Result<Value<T>> {
        match self {
            LispListItem::Item(v) => Result::Ok(v),
            _ => Result::Err(Error::new(ErrorKind::IncorrectType, "Incorrect type")),
        }
    }

    pub fn unwrap_item(self) -> Value<T> {
        match self {
            LispListItem::Item(v) => v,
            _ => panic!("Expected LispListItem::Item"),
        }
    }

    pub fn unwrap_tail(self) -> Value<T> {
        match self {
            LispListItem::Tail(v) => v,
            _ => panic!("Expected LispListItem::Tail"),
        }
    }
}

pub struct LispList<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    val: Value<T>,
}

impl<T> LispList<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    Value<T>: Clone,
{
    pub fn take(self) -> Value<T> {
        self.val
    }
}

impl<T> Iterator for LispList<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    Value<T>: Clone,
{
    type Item = LispListItem<T>;

    fn next(&mut self) -> Option<Self::Item> {
        match &self.val {
            Value::Nil => Option::None,
            Value::Cons(ValueCons(c)) => {
                let cons = c.borrow();
                let car = cons.car.clone();
                let cdr = cons.cdr.clone();
                self.val = cdr;
                Option::Some(LispListItem::Item(car))
            }
            _ => {
                let mut result = Value::Nil;
                std::mem::swap(&mut self.val, &mut result);
                Option::Some(LispListItem::Tail(result))
            }
        }
    }
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
    type ConsRef = Rc<Cons<Self>>;
    type StringRef = String;
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
    type ConsRef = &'static Cons<Self>;
    type StringRef = &'static str;
    type SemverTypes = SemverTypesStatic;
}

#[macro_export]
macro_rules! v_nil {
    () => {
        $crate::Value::<$crate::ValueTypesStatic>::Nil
    };
}

#[macro_export]
macro_rules! uqsym {
    ($name:expr) => {
        $crate::ValueUnqualifiedSymbol::<&'static str>($name)
    };
}

#[macro_export]
macro_rules! v_uqsym {
    ($name:expr) => {
        $crate::Value::<$crate::ValueTypesStatic>::UnqualifiedSymbol(uqsym!($name))
    };
}

#[macro_export]
macro_rules! qsym {
    ($package:expr, $name:expr) => {
        $crate::ValueQualifiedSymbol::<&'static str> {
            package: $package,
            name: $name,
        }
    };
}

#[macro_export]
macro_rules! v_qsym {
    ($package:expr, $name:expr) => {
        $crate::Value::<$crate::ValueTypesStatic>::QualifiedSymbol(qsym!($package, $name))
    };
}

#[macro_export]
macro_rules! cons {
    ($car:expr, $cdr:expr) => {
        $crate::ValueCons::<$crate::ValueTypesStatic>(&$crate::Cons {
            car: $car,
            cdr: $cdr,
        })
    };
}

#[macro_export]
macro_rules! v_cons {
    ($car:expr, $cdr:expr) => {
        $crate::Value::<$crate::ValueTypesStatic>::Cons(cons!($car, $cdr))
    };
}

#[macro_export]
macro_rules! bool {
    ($b:expr) => {
        $crate::ValueBool($b)
    };
}

#[macro_export]
macro_rules! v_bool {
    ($b:expr) => {
        $crate::Value::<$crate::ValueTypesStatic>::Bool(bool!($b))
    };
}

#[macro_export]
macro_rules! str {
    ($s:expr) => {
        $crate::ValueString::<&'static str>($s)
    };
}

#[macro_export]
macro_rules! v_str {
    ($s:expr) => {
        $crate::Value::<$crate::ValueTypesStatic>::String(str!($s))
    };
}

#[macro_export]
macro_rules! vref {
    ($major:expr, $rest:expr) => {
        $crate::ValueSemver::<$crate::SemverTypesStatic> {
            major: $major as u64,
            rest: $rest as &[u64],
        }
    };
}

#[macro_export]
macro_rules! v_vref {
    ($major:expr, $rest:expr) => {
        $crate::Value::<$crate::ValueTypesStatic>::Semver(vref!($major, $rest))
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
        $crate::Value::<$crate::ValueTypesStatic>::LanguageDirective($lang)
    };
}

#[macro_export]
macro_rules! lang_kira_ref {
    ($major:expr, $rest:expr) => {
        $crate::ValueLanguageDirective::<&'static str, $crate::SemverTypesStatic>::Kira(vref!(
            $major, $rest
        ))
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
        $crate::ValueLanguageDirective::<&'static str, $crate::SemverTypesStatic>::Other($name)
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
        $crate::ValueFunction::<&'static str>($name)
    };
}

#[macro_export]
macro_rules! v_func {
    ($name:expr) => {
        $crate::Value::<$crate::ValueTypesStatic>::Function(func!($name))
    };
}

#[macro_export]
macro_rules! v_list {
    () => { v_nil!() };
    ($e:expr) => { v_cons!($e, v_nil!()) };
    ($e:expr, $($es:expr),+) => { v_cons!($e, v_list!($($es),*)) };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_v_nil_macro() {
        const NIL: super::Value<super::ValueTypesStatic> = v_nil!();
        assert_eq!(NIL, super::Value::<super::ValueTypesStatic>::Nil);
    }

    #[test]
    fn test_uqsym_macro() {
        const UQSYM: super::ValueUnqualifiedSymbol<&'static str> = uqsym!("uqsym");
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
        const QSYM: super::ValueQualifiedSymbol<&'static str> = qsym!("package", "qsym");
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
    fn test_cons_macro() {
        const CONS: super::ValueCons<super::ValueTypesStatic> = cons!(v_uqsym!("uqsym"), v_nil!());
        match &CONS.0.car {
            super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym"),
            _ => panic!("Expected a Value::UnqualifiedSymbol"),
        }
        assert_eq!(CONS.0.cdr, super::Value::<super::ValueTypesStatic>::Nil);
    }

    #[test]
    fn test_v_cons_macro() {
        const CONS: super::Value<super::ValueTypesStatic> = v_cons!(v_uqsym!("uqsym"), v_nil!());
        match CONS {
            super::Value::Cons(c) => {
                match &c.0.car {
                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym"),
                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                }
                assert_eq!(c.0.cdr, super::Value::<super::ValueTypesStatic>::Nil);
            }
            _ => panic!("Expected a Value::Cons"),
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
        const S: super::ValueString<&'static str> = str!("str");
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
        const L1: super::ValueLanguageDirective<&'static str, super::SemverTypesStatic> =
            lang_kira![1];
        match L1 {
            super::ValueLanguageDirective::Kira(v) => {
                assert_eq!(v.major, 1);
                assert_eq!(v.rest, &[]);
            }
            _ => panic!("Expected a Value::LanguageDirective with Kira"),
        }

        const L2: super::ValueLanguageDirective<&'static str, super::SemverTypesStatic> =
            lang_kira![1, 0];
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
        const L1: super::ValueLanguageDirective<&'static str, super::SemverTypesStatic> =
            lang_other!("not-kira");
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
        const F: super::ValueFunction<&'static str> = func!(qsym!("p", "f1"));
        assert_eq!(
            F.0,
            super::ValueQualifiedSymbol::<&'static str> {
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
                super::ValueQualifiedSymbol::<&'static str> {
                    package: "p",
                    name: "f1"
                }
            ),
            _ => panic!("Expected a Value::Function"),
        }
    }

    #[test]
    fn test_v_list_macro() {
        const LIST1: super::Value<super::ValueTypesStatic> = v_list!();
        assert_eq!(LIST1, super::Value::<super::ValueTypesStatic>::Nil);

        const LIST2: super::Value<super::ValueTypesStatic> = v_list!(v_uqsym!("uqsym1"));
        match LIST2 {
            super::Value::Cons(c) => {
                match &c.0.car {
                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                }
                assert_eq!(c.0.cdr, super::Value::<super::ValueTypesStatic>::Nil);
            }
            _ => panic!("Expected a Value::Cons"),
        }

        const LIST3: super::Value<super::ValueTypesStatic> =
            v_list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"));
        match LIST3 {
            super::Value::Cons(c) => {
                match &c.0.car {
                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                }
                match &c.0.cdr {
                    super::Value::Cons(c) => {
                        match &c.0.car {
                            super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym2"),
                            _ => panic!("Expected a Value::UnqualifiedSymbol"),
                        }
                        assert_eq!(c.0.cdr, super::Value::<super::ValueTypesStatic>::Nil);
                    }
                    _ => panic!("Expected a Value::Cons"),
                }
            }
            _ => panic!("Expected a Value::Cons"),
        }

        const LIST4: super::Value<super::ValueTypesStatic> =
            v_list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"), v_uqsym!("uqsym3"));
        match LIST4 {
            super::Value::Cons(c) => {
                match &c.0.car {
                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                }
                match &c.0.cdr {
                    super::Value::Cons(c) => {
                        match &c.0.car {
                            super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym2"),
                            _ => panic!("Expected a Value::UnqualifiedSymbol"),
                        }
                        match &c.0.cdr {
                            super::Value::Cons(c) => {
                                match &c.0.car {
                                    super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym3"),
                                    _ => panic!("Expected a Value::UnqualifiedSymbol"),
                                }
                                assert_eq!(c.0.cdr, super::Value::<super::ValueTypesStatic>::Nil);
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
    fn test_semver_compare() {
        use super::*;
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
        assert_eq!(v_nil!(), v_nil!());
        assert_ne!(v_nil!(), v_uqsym!("uqsym"));

        assert_eq!(v_uqsym!("uqsym"), v_uqsym!("uqsym"));
        assert_eq!(
            v_uqsym!("uqsym"),
            super::Value::<super::ValueTypesRc>::UnqualifiedSymbol(super::ValueUnqualifiedSymbol(
                "uqsym".to_string()
            ))
        );
        assert_ne!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"));
        assert_ne!(
            v_uqsym!("uqsym1"),
            super::Value::<super::ValueTypesRc>::UnqualifiedSymbol(super::ValueUnqualifiedSymbol(
                "uqsym2".to_string()
            ))
        );
        assert_ne!(v_uqsym!("uqsym"), v_str!("uqsym"));
        assert_ne!(v_uqsym!("uqsym"), v_nil!());

        assert_eq!(v_qsym!("p", "qsym"), v_qsym!("p", "qsym"));
        assert_eq!(
            v_qsym!("p", "qsym"),
            super::Value::<super::ValueTypesRc>::QualifiedSymbol(super::ValueQualifiedSymbol {
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
        assert_ne!(v_qsym!("p", "qsym"), v_nil!());

        assert_eq!(
            v_cons!(v_uqsym!("uqsym"), v_nil!()),
            v_cons!(v_uqsym!("uqsym"), v_nil!())
        );
        assert_ne!(
            v_cons!(v_uqsym!("uqsym1"), v_nil!()),
            v_cons!(v_uqsym!("uqsym2"), v_nil!())
        );
        assert_ne!(
            v_cons!(v_uqsym!("uqsym"), v_nil!()),
            v_cons!(v_nil!(), v_nil!())
        );
        assert_ne!(
            v_cons!(v_uqsym!("uqsym"), v_nil!()),
            v_cons!(v_uqsym!("uqsym"), v_uqsym!("uqsym"))
        );
        assert_ne!(v_cons!(v_uqsym!("uqsym"), v_nil!()), v_nil!());

        assert_eq!(v_bool!(true), v_bool!(true));
        assert_ne!(v_bool!(true), v_bool!(false));
        assert_ne!(v_bool!(true), v_nil!());

        assert_eq!(v_str!("str"), v_str!("str"));
        assert_eq!(
            v_str!("str"),
            super::Value::<super::ValueTypesRc>::String(super::ValueString("str".to_string()))
        );
        assert_ne!(v_str!("str1"), v_str!("str2"));
        assert_ne!(
            v_str!("str1"),
            super::Value::<super::ValueTypesRc>::String(super::ValueString("str2".to_string()))
        );
        assert_ne!(v_str!("str"), v_uqsym!("str"));
        assert_ne!(v_str!("str"), v_nil!());

        assert_eq!(v_v![1, 0], v_v![1, 0]);
        assert_ne!(v_v![1, 0], v_v![1, 1]);
        assert_ne!(v_v![1, 0], v_nil!());

        assert_eq!(v_lang_kira![1, 0], v_lang_kira![1, 0]);
        assert_ne!(v_lang_kira![1, 0], v_lang_kira![1, 1]);
        assert_ne!(v_lang_kira![1, 0], v_lang_other!("not-kira"));
        assert_ne!(v_lang_kira![1, 0], v_v![1, 0]);
        assert_ne!(v_lang_kira![1, 0], v_nil!());

        assert_eq!(v_func!(qsym!("p", "f1")), v_func!(qsym!("p", "f1")));
        assert_ne!(v_func!(qsym!("p", "f1")), v_func!(qsym!("p", "f2")));
        assert_ne!(v_func!(qsym!("p", "f1")), v_qsym!("p", "f1"));
        assert_ne!(v_func!(qsym!("p", "f1")), v_nil!());
    }

    #[test]
    fn test_try_into_value_type_ref() {
        use super::*;
        use std::convert::TryInto;

        let v = v_nil!();
        assert_eq!(TryInto::<()>::try_into(&v).unwrap(), ());
        assert_eq!(
            TryInto::<&ValueString<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(&v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_uqsym!("uqsym");
        assert_eq!(
            TryInto::<&ValueUnqualifiedSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(&v)
                .unwrap(),
            &uqsym!("uqsym")
        );
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_qsym!("p", "qsym");
        assert_eq!(
            TryInto::<&ValueQualifiedSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(&v)
                .unwrap(),
            &qsym!("p", "qsym")
        );
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_cons!(v_nil!(), v_nil!());
        assert_eq!(
            TryInto::<&ValueCons<ValueTypesStatic>>::try_into(&v).unwrap(),
            &cons!(v_nil!(), v_nil!())
        );
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_bool!(true);
        assert_eq!(TryInto::<&ValueBool>::try_into(&v).unwrap(), &bool!(true));
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_str!("str");
        assert_eq!(
            TryInto::<&ValueString<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(&v)
                .unwrap(),
            &str!("str")
        );
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_v![1, 0];
        assert_eq!(
            TryInto::<&ValueSemver<<ValueTypesStatic as ValueTypes>::SemverTypes>>::try_into(&v)
                .unwrap(),
            &v![1, 0]
        );
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_lang_kira![1, 0];
        assert_eq!(
            TryInto::<&ValueLanguageDirective<&'static str, SemverTypesStatic>>::try_into(&v)
                .unwrap(),
            &lang_kira![1, 0]
        );
        assert_eq!(
            TryInto::<()>::try_into(&v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_func!(qsym!("p", "f1"));
        assert_eq!(
            TryInto::<&ValueFunction<&'static str>>::try_into(&v).unwrap(),
            &func!(qsym!("p", "f1"))
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

        let v = v_nil!();
        assert_eq!(TryInto::<()>::try_into(v.clone()).unwrap(), ());
        assert_eq!(
            TryInto::<ValueString<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v)
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );

        let v = v_uqsym!("uqsym");
        assert_eq!(
            TryInto::<ValueUnqualifiedSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(v.clone())
                .unwrap(),
            uqsym!("uqsym")
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_qsym!("p", "qsym");
        assert_eq!(
            TryInto::<ValueQualifiedSymbol<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(
                v.clone()
            )
            .unwrap(),
            qsym!("p", "qsym")
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_cons!(v_nil!(), v_nil!());
        assert_eq!(
            TryInto::<ValueCons<ValueTypesStatic>>::try_into(v.clone()).unwrap(),
            cons!(v_nil!(), v_nil!())
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_bool!(true);
        assert_eq!(
            TryInto::<ValueBool>::try_into(v.clone()).unwrap(),
            bool!(true)
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_str!("str");
        assert_eq!(
            TryInto::<ValueString<<ValueTypesStatic as ValueTypes>::StringRef>>::try_into(
                v.clone()
            )
            .unwrap(),
            str!("str")
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_v![1, 0];
        assert_eq!(
            TryInto::<ValueSemver<<ValueTypesStatic as ValueTypes>::SemverTypes>>::try_into(
                v.clone()
            )
            .unwrap(),
            v![1, 0]
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_lang_kira![1, 0];
        assert_eq!(
            TryInto::<ValueLanguageDirective<&'static str, SemverTypesStatic>>::try_into(v.clone())
                .unwrap(),
            lang_kira![1, 0]
        );
        assert_eq!(
            TryInto::<()>::try_into(v).unwrap_err().kind,
            ErrorKind::IncorrectType
        );

        let v = v_func!(qsym!("p", "f1"));
        assert_eq!(
            TryInto::<ValueFunction<&'static str>>::try_into(v.clone()).unwrap(),
            func!(qsym!("p", "f1"))
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
        assert_eq!(v, v_nil!());

        let v: Value<ValueTypesStatic> = uqsym!("uqsym").into();
        assert_eq!(v, v_uqsym!("uqsym"));

        let v: Value<ValueTypesStatic> = qsym!("p", "qsym").into();
        assert_eq!(v, v_qsym!("p", "qsym"));

        let v: Value<ValueTypesStatic> = cons!(v_nil!(), v_nil!()).into();
        assert_eq!(v, v_cons!(v_nil!(), v_nil!()));

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
    }

    #[test]
    fn test_into_iter() {
        use super::*;

        let mut i = v_list!(v_uqsym!("uqsym"), v_bool!(true), v_str!("str")).into_iter();
        assert_eq!(i.next().unwrap().unwrap_item(), v_uqsym!("uqsym"));
        assert_eq!(i.next().unwrap().unwrap_item(), v_bool!(true));
        assert_eq!(i.next().unwrap().unwrap_item(), v_str!("str"));
        assert!(i.next().is_none());
        assert_eq!(i.take(), v_nil!());

        let mut i = v_cons!(v_uqsym!("uqsym"), v_bool!(true)).into_iter();
        assert_eq!(i.next().unwrap().unwrap_item(), v_uqsym!("uqsym"));
        assert_eq!(i.next().unwrap().unwrap_tail(), v_bool!(true));
        assert!(i.next().is_none());
        assert_eq!(i.take(), v_nil!());

        let mut i = v_list!(v_uqsym!("uqsym"), v_bool!(true), v_str!("str")).into_iter();
        assert_eq!(i.next().unwrap().unwrap_item(), v_uqsym!("uqsym"));
        assert_eq!(i.take(), v_list!(v_bool!(true), v_str!("str")));

        let mut i = v_list!(v_uqsym!("uqsym"), v_bool!(true), v_str!("str")).into_iter();
        assert_eq!(i.next().unwrap().unwrap_item(), v_uqsym!("uqsym"));
        assert_eq!(i.next().unwrap().unwrap_item(), v_bool!(true));
        assert_eq!(i.next().unwrap().unwrap_item(), v_str!("str"));
        assert_eq!(i.take(), v_nil!());

        let i = v_nil!().into_iter();
        assert_eq!(i.take(), v_nil!());
    }

    #[test]
    fn test_value_type() {
        use super::*;

        assert_eq!(
            v_nil!().value_type(),
            ValueType::NonList(ValueTypeNonList::Nil)
        );
        assert_eq!(
            v_uqsym!("uqsym").value_type(),
            ValueType::NonList(ValueTypeNonList::UnqualifiedSymbol)
        );
        assert_eq!(
            v_qsym!("p", "qsym").value_type(),
            ValueType::NonList(ValueTypeNonList::QualifiedSymbol)
        );
        assert_eq!(
            v_bool!(true).value_type(),
            ValueType::NonList(ValueTypeNonList::Bool)
        );
        assert_eq!(
            v_str!("str").value_type(),
            ValueType::NonList(ValueTypeNonList::String)
        );
        assert_eq!(
            v_v![1, 0].value_type(),
            ValueType::NonList(ValueTypeNonList::Semver)
        );
        assert_eq!(
            v_lang_kira![1, 0].value_type(),
            ValueType::NonList(ValueTypeNonList::LanguageDirective)
        );
        assert_eq!(
            v_func!(qsym!("p", "f1")).value_type(),
            ValueType::NonList(ValueTypeNonList::Function)
        );
        assert_eq!(
            v_list!(
                v_nil!(),
                v_bool!(true),
                v_str!("str"),
                v_cons!(
                    v_uqsym!("uqsym"),
                    v_cons!(v_bool!(true), v_qsym!("p", "qsym"))
                )
            )
            .value_type(),
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

    struct SimpleEnvironment;

    fn simplemacro1() -> super::Result<super::TryCompilationResult<super::ValueTypesRc>> {
        use super::*;
        use std::iter::FromIterator;

        Result::Ok(TryCompilationResult::Compiled(CompilationResult {
            result: Box::new(Literal(v_str!("Hello world!").convert())),
            types: BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::String)]),
        }))
    }

    fn simplemacro2() -> super::Result<super::TryCompilationResult<super::ValueTypesRc>> {
        use super::*;
        use std::iter::FromIterator;

        Result::Ok(TryCompilationResult::Compiled(CompilationResult {
            result: Box::new(Literal::new(v_bool!(true).convert())),
            types: BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Bool)]),
        }))
    }

    fn compile_simplefunc1(
        params: &mut dyn Iterator<Item = &super::BTreeSet<super::ValueType>>,
    ) -> super::Result<super::BTreeSet<super::ValueType>> {
        use super::*;

        let result = match params.next() {
            Option::Some(p) => (*p).clone(),
            Option::None => {
                return Result::Err(Error::new(
                    ErrorKind::IncorrectParams,
                    "Incorrect parameters",
                ))
            }
        };

        match params.next() {
            Option::None => Result::Ok(result),
            Option::Some(_) => Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            )),
        }
    }

    fn simplefunc1(
        _env: &mut dyn super::Environment<super::ValueTypesRc>,
        params: Vec<super::Value<super::ValueTypesRc>>,
    ) -> super::Result<super::Value<super::ValueTypesRc>> {
        use super::*;

        let mut params = params.into_iter();
        let result = match params.next() {
            Option::Some(p) => p,
            Option::None => {
                return Result::Err(Error::new(
                    ErrorKind::IncorrectParams,
                    "Incorrect parameters",
                ))
            }
        };

        match params.next() {
            Option::None => Result::Ok(result),
            Option::Some(_) => Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            )),
        }
    }

    impl super::Environment<super::ValueTypesRc> for SimpleEnvironment {
        fn as_dyn_mut(&mut self) -> &mut (dyn super::Environment<super::ValueTypesRc> + 'static) {
            self as &mut (dyn super::Environment<super::ValueTypesRc> + 'static)
        }

        fn evaluate_function(
            &mut self,
            name: &super::ValueQualifiedSymbol<
                <super::ValueTypesRc as super::ValueTypes>::StringRef,
            >,
            params: Vec<super::Value<super::ValueTypesRc>>,
        ) -> super::Result<super::Value<super::ValueTypesRc>> {
            use super::*;
            use std::borrow::Borrow;

            match (name.package.borrow(), name.name.borrow()) {
                ("p", "simplefunc1") => simplefunc1(self, params),
                _ => Result::Err(Error::new(ErrorKind::ValueNotDefined, "Value not defined")),
            }
        }

        fn resolve_symbol_get_macro(
            &self,
            name: &super::ValueUnqualifiedSymbol<
                <super::ValueTypesRc as super::ValueTypes>::StringRef,
            >,
        ) -> Option<
            super::ValueQualifiedSymbol<<super::ValueTypesRc as super::ValueTypes>::StringRef>,
        > {
            Option::Some(super::ValueQualifiedSymbol {
                package: "p".to_string(),
                name: name.0.clone(),
            })
        }

        fn compile_macro(
            &mut self,
            name: &super::ValueQualifiedSymbol<String>,
            v: super::LispList<super::ValueTypesRc>,
        ) -> Option<super::Result<super::TryCompilationResult<super::ValueTypesRc>>> {
            use std::borrow::Borrow;

            match (name.package.borrow(), name.name.borrow()) {
                ("p", "simplemacro1") => Option::Some(simplemacro1()),
                ("p", "simplemacro2") => Option::Some(simplemacro2()),
                ("p", "simplefunc1") => self.compile_function_from_macro(name, v),
                _ => Option::None,
            }
        }

        fn compile_function(
            &self,
            name: &super::ValueQualifiedSymbol<String>,
            params: &mut dyn Iterator<Item = &super::BTreeSet<super::ValueType>>,
        ) -> Option<super::Result<super::BTreeSet<super::ValueType>>> {
            use std::borrow::Borrow;

            match (name.package.borrow(), name.name.borrow()) {
                ("p", "simplefunc1") => Option::Some(compile_simplefunc1(params)),
                _ => Option::None,
            }
        }
    }

    fn test_compile_and_evaluate(
        env: &mut SimpleEnvironment,
        code: super::Value<super::ValueTypesStatic>,
        result: super::Value<super::ValueTypesStatic>,
        types: super::BTreeSet<super::ValueType>,
    ) {
        use super::*;

        let mut comp = env.compile(code.convert()).unwrap();
        assert_eq!(comp.types, types);
        assert_eq!(comp.result.evaluate(env).unwrap(), result);
    }

    #[test]
    fn test_compile_and_evaluate_literal() {
        use super::*;

        let mut env = SimpleEnvironment;
        test_compile_and_evaluate(
            &mut env,
            v_nil!(),
            v_nil!(),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Nil)]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_bool!(true),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Bool)]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_str!("Hello world!"),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::String)]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_v![1, 0],
            v_v![1, 0],
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Semver)]),
        );
    }

    #[test]
    fn test_compile_and_evaluate_macro() {
        use super::*;

        let mut env = SimpleEnvironment;

        test_compile_and_evaluate(
            &mut env,
            v_list!(v_uqsym!("simplemacro1")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::String)]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_list!(v_uqsym!("simplemacro2")),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Bool)]),
        );
        assert_eq!(
            env.compile(v_list!(v_uqsym!("simplemacro3")).convert())
                .unwrap_err()
                .kind,
            ErrorKind::ValueNotDefined
        );

        test_compile_and_evaluate(
            &mut env,
            v_list!(v_qsym!("p", "simplemacro1")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::String)]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_list!(v_qsym!("p", "simplemacro2")),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Bool)]),
        );
        assert_eq!(
            env.compile(v_list!(v_qsym!("p", "simplemacro3")).convert())
                .unwrap_err()
                .kind,
            ErrorKind::ValueNotDefined
        );
    }

    #[test]
    fn test_compile_and_evaluate_function() {
        use super::*;

        let mut env = SimpleEnvironment;

        test_compile_and_evaluate(
            &mut env,
            v_list!(v_uqsym!("simplefunc1"), v_str!("Hello world!")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::String)]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_list!(v_uqsym!("simplefunc1"), v_bool!(true)),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Bool)]),
        );
        assert_eq!(
            env.compile(v_list!(v_uqsym!("simplefunc1")).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectParams
        );

        test_compile_and_evaluate(
            &mut env,
            v_list!(v_qsym!("p", "simplefunc1"), v_str!("Hello world!")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::String)]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_list!(v_qsym!("p", "simplefunc1"), v_bool!(true)),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Bool)]),
        );
        assert_eq!(
            env.compile(v_list!(v_qsym!("p", "simplefunc1")).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectParams
        );
    }

    #[test]
    fn test_evaluate_literal() {
        use super::*;

        let mut env = SimpleEnvironment;

        let mut comp = Literal::new(v_str!("Hello world!").convert());
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("Hello world!"));

        let mut comp = Literal::new(v_bool!(true).convert());
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_bool!(true));
    }

    #[test]
    fn test_evaluate_function() {
        use super::*;

        let mut env = SimpleEnvironment;

        let mut comp = FunctionCall::new(
            func!(qsym!("p", "simplefunc1")).convert(),
            vec![Box::new(Literal::new(v_str!("Hello world!").convert()))],
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("Hello world!"));

        let mut comp = FunctionCall::new(
            func!(qsym!("p", "simplefunc1")).convert(),
            vec![Box::new(Literal::new(v_bool!(true).convert()))],
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_bool!(true));
    }
}
