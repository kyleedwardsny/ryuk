use std::borrow::Borrow;
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[derive(Debug)]
pub struct ValueList(pub Option<Rc<Cons>>);

impl ValueList {
    pub fn deep_clone(&self) -> ValueList {
        ValueList(match &self.0 {
            Option::Some(c) => Option::Some(Rc::new(Cons {
                car: c.car.deep_clone(),
                cdr: c.cdr.deep_clone(),
            })),
            Option::None => Option::None,
        })
    }

    fn list_eq(&self, other: &ValueList) -> bool {
        match (&self.0, &other.0) {
            (Option::Some(c1), Option::Some(c2)) => c1 == c2,
            (Option::None, Option::None) => true,
            _ => false,
        }
    }
}

impl Clone for ValueList {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl PartialEq<ValueList> for ValueList {
    fn eq(&self, other: &ValueList) -> bool {
        self.list_eq(other)
    }
}

impl Iterator for ValueList {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        match &self.0 {
            Option::None => Option::None,
            Option::Some(c) => {
                let car = c.car.clone();
                let cdr = c.cdr.clone();
                *self = cdr;
                Option::Some(car)
            }
        }
    }
}

#[derive(Debug)]
pub struct Cons {
    pub car: Value,
    pub cdr: ValueList,
}

impl Clone for Cons {
    fn clone(&self) -> Self {
        Cons {
            car: self.car.clone(),
            cdr: self.cdr.clone(),
        }
    }
}

impl PartialEq<Cons> for Cons {
    fn eq(&self, other: &Cons) -> bool {
        self.car == other.car && self.cdr.list_eq(&other.cdr)
    }
}

#[derive(Debug)]
pub struct ValueUnqualifiedSymbol(pub String);

impl Clone for ValueUnqualifiedSymbol {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl PartialEq<ValueUnqualifiedSymbol> for ValueUnqualifiedSymbol {
    fn eq(&self, rhs: &ValueUnqualifiedSymbol) -> bool {
        self.0 == rhs.0
    }
}

#[derive(Debug)]
pub struct ValueQualifiedSymbol {
    pub package: String,
    pub name: String,
}

impl Clone for ValueQualifiedSymbol {
    fn clone(&self) -> Self {
        Self {
            package: self.package.clone(),
            name: self.name.clone(),
        }
    }
}

impl PartialEq<ValueQualifiedSymbol> for ValueQualifiedSymbol {
    fn eq(&self, rhs: &ValueQualifiedSymbol) -> bool {
        self.package == rhs.package && self.name == rhs.name
    }
}

impl Eq for ValueQualifiedSymbol {}

impl Hash for ValueQualifiedSymbol {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.package.hash(state);
        self.name.hash(state);
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ValueBool(pub bool);

#[derive(Debug)]
pub struct ValueString(pub String);

impl Clone for ValueString {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl PartialEq<ValueString> for ValueString {
    fn eq(&self, rhs: &ValueString) -> bool {
        self.0 == rhs.0
    }
}

#[derive(Debug)]
pub struct ValueSemver {
    pub major: u64,
    pub rest: Vec<u64>,
}

impl ValueSemver {
    pub fn items<'v>(&'v self) -> SemverIter<'v> {
        SemverIter {
            v: self,
            iter: Option::None,
        }
    }
}

impl Clone for ValueSemver {
    fn clone(&self) -> Self {
        Self {
            major: self.major,
            rest: self.rest.clone(),
        }
    }
}

pub struct SemverIter<'v> {
    v: &'v ValueSemver,
    iter: Option<std::slice::Iter<'v, u64>>,
}

impl<'v> Iterator for SemverIter<'v> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            Option::None => {
                self.iter = Option::Some((&self.v.rest).into_iter());
                Option::Some(self.v.major)
            }
            Option::Some(i) => i.next().map(|v| *v),
        }
    }
}

impl PartialEq<ValueSemver> for ValueSemver {
    fn eq(&self, other: &ValueSemver) -> bool {
        self.partial_cmp(other) == Option::Some(Ordering::Equal)
    }
}

impl PartialOrd<ValueSemver> for ValueSemver {
    fn partial_cmp(&self, other: &ValueSemver) -> Option<Ordering> {
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
pub enum ValueLanguageDirective {
    Kira(ValueSemver),
    Other(String),
}

impl Clone for ValueLanguageDirective {
    fn clone(&self) -> Self {
        match self {
            ValueLanguageDirective::Kira(v) => ValueLanguageDirective::Kira(v.clone()),
            ValueLanguageDirective::Other(name) => ValueLanguageDirective::Other(name.clone()),
        }
    }
}

impl PartialEq<ValueLanguageDirective> for ValueLanguageDirective {
    fn eq(&self, rhs: &ValueLanguageDirective) -> bool {
        eq_match!(self, rhs, {
            (ValueLanguageDirective::Kira(v1), ValueLanguageDirective::Kira(v2)) => v1 == v2,
            (ValueLanguageDirective::Other(n1), ValueLanguageDirective::Other(n2)) => n1 == n2,
        })
    }
}

#[derive(Debug)]
pub struct ValueFunction(pub ValueQualifiedSymbol);

impl PartialEq<ValueFunction> for ValueFunction {
    fn eq(&self, rhs: &ValueFunction) -> bool {
        self.0 == rhs.0
    }
}

impl Clone for ValueFunction {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[derive(Debug)]
pub struct ValueBackquote(pub Box<Value>);

impl ValueBackquote {
    pub fn deep_clone(&self) -> ValueBackquote {
        ValueBackquote(Box::new(self.0.deep_clone()))
    }
}

impl PartialEq<ValueBackquote> for ValueBackquote {
    fn eq(&self, rhs: &ValueBackquote) -> bool {
        self.0 == rhs.0
    }
}

impl Clone for ValueBackquote {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[derive(Debug)]
pub struct ValueComma(pub Box<Value>);

impl ValueComma {
    pub fn deep_clone(&self) -> ValueComma {
        ValueComma(Box::new(self.0.deep_clone()))
    }
}

impl PartialEq<ValueComma> for ValueComma {
    fn eq(&self, rhs: &ValueComma) -> bool {
        self.0 == rhs.0
    }
}

impl Clone for ValueComma {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[derive(Debug)]
pub struct ValueSplice(pub Box<Value>);

impl ValueSplice {
    pub fn deep_clone(&self) -> ValueSplice {
        ValueSplice(Box::new(self.0.deep_clone()))
    }
}

impl PartialEq<ValueSplice> for ValueSplice {
    fn eq(&self, rhs: &ValueSplice) -> bool {
        self.0 == rhs.0
    }
}

impl Clone for ValueSplice {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[derive(Debug)]
pub enum Value {
    List(ValueList),
    UnqualifiedSymbol(ValueUnqualifiedSymbol),
    QualifiedSymbol(ValueQualifiedSymbol),
    Bool(ValueBool),
    String(ValueString),
    Semver(ValueSemver),
    LanguageDirective(ValueLanguageDirective),
    Function(ValueFunction),
    Backquote(ValueBackquote),
    Comma(ValueComma),
    Splice(ValueSplice),
}

impl Value {
    pub fn deep_clone(&self) -> Value {
        match self {
            Value::List(l) => Value::List(l.deep_clone()),
            Value::UnqualifiedSymbol(s) => Value::UnqualifiedSymbol(s.clone()),
            Value::QualifiedSymbol(s) => Value::QualifiedSymbol(s.clone()),
            Value::Bool(b) => Value::Bool(b.clone()),
            Value::String(s) => Value::String(s.clone()),
            Value::Semver(v) => Value::Semver(v.clone()),
            Value::LanguageDirective(l) => Value::LanguageDirective(l.clone()),
            Value::Function(f) => Value::Function(f.clone()),
            Value::Backquote(b) => Value::Backquote(b.deep_clone()),
            Value::Comma(c) => Value::Comma(c.deep_clone()),
            Value::Splice(s) => Value::Splice(s.deep_clone()),
        }
    }
}

impl Clone for Value {
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
    ($l:lifetime, $in:ty, $out:ty, $match:pat => $result:expr) => {
        impl<$l> TryFrom<$in> for $out {
            type Error = $in;

            fn try_from(v: $in) -> std::result::Result<Self, $in> {
                match v {
                    $match => std::result::Result::Ok($result),
                    _ => std::result::Result::Err(v),
                }
            }
        }
    };

    ($out:ty, $match:pat => $result:expr) => {
        try_from_value!('v, Value, $out, $match => $result);
        try_from_value!('v, &'v Value, &'v $out, $match => $result);
    };
}

try_from_value!(ValueList, Value::List(l) => l);
try_from_value!(ValueUnqualifiedSymbol, Value::UnqualifiedSymbol(s) => s);
try_from_value!(ValueQualifiedSymbol, Value::QualifiedSymbol(s) => s);
try_from_value!(ValueBool, Value::Bool(b) => b);
try_from_value!(ValueString, Value::String(s) => s);
try_from_value!(ValueSemver, Value::Semver(v) => v);
try_from_value!(ValueLanguageDirective, Value::LanguageDirective(l) => l);
try_from_value!(ValueFunction, Value::Function(f) => f);
try_from_value!(ValueBackquote, Value::Backquote(b) => b);
try_from_value!(ValueComma, Value::Comma(c) => c);
try_from_value!(ValueSplice, Value::Splice(s) => s);

macro_rules! from_value_type {
    ($in:ty, $param:ident -> $result:expr) => {
        impl From<$in> for Value {
            fn from($param: $in) -> Self {
                $result
            }
        }
    };
}

from_value_type!(ValueList, l -> Value::List(l));
from_value_type!(ValueUnqualifiedSymbol, s -> Value::UnqualifiedSymbol(s));
from_value_type!(ValueQualifiedSymbol, s -> Value::QualifiedSymbol(s));
from_value_type!(ValueBool, b -> Value::Bool(b));
from_value_type!(ValueString, s -> Value::String(s));
from_value_type!(ValueSemver, v -> Value::Semver(v));
from_value_type!(ValueLanguageDirective, l -> Value::LanguageDirective(l));
from_value_type!(ValueFunction, f -> Value::Function(f));
from_value_type!(ValueBackquote, b -> Value::Backquote(b));
from_value_type!(ValueComma, c -> Value::Comma(c));
from_value_type!(ValueSplice, s -> Value::Splice(s));

impl PartialEq<Value> for Value {
    fn eq(&self, rhs: &Value) -> bool {
        eq_match!(self, rhs, {
            (Value::List(l1), Value::List(l2)) => l1 == l2,
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

impl Eq for Value {}

#[macro_export]
macro_rules! cons {
    ($car:expr, $cdr:expr) => {
        $crate::value::ValueList(::std::option::Option::Some(
            $crate::value::Cons {
                car: $car,
                cdr: $cdr,
            }
            .into(),
        ))
    };
}

#[macro_export]
macro_rules! list {
    () => { $crate::value::ValueList(::std::option::Option::None) };
    ($e:expr) => { cons!($e, list!()) };
    ($e:expr, $($es:expr),*) => { cons!($e, list!($($es),*)) };
}

#[macro_export]
macro_rules! v_list {
    ($($es:expr),*) => { $crate::value::Value::List(list!($($es),*)) };
}

#[macro_export]
macro_rules! uqsym {
    ($name:expr) => {
        $crate::value::ValueUnqualifiedSymbol($name.into())
    };
}

#[macro_export]
macro_rules! v_uqsym {
    ($name:expr) => {
        $crate::value::Value::UnqualifiedSymbol(uqsym!($name))
    };
}

#[macro_export]
macro_rules! qsym {
    ($package:expr, $name:expr) => {
        $crate::value::ValueQualifiedSymbol {
            package: $package.into(),
            name: $name.into(),
        }
    };
}

#[macro_export]
macro_rules! v_qsym {
    ($package:expr, $name:expr) => {
        $crate::value::Value::QualifiedSymbol(qsym!($package, $name))
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
        $crate::value::Value::Bool(bool!($b))
    };
}

#[macro_export]
macro_rules! str {
    ($s:expr) => {
        $crate::value::ValueString($s.into())
    };
}

#[macro_export]
macro_rules! v_str {
    ($s:expr) => {
        $crate::value::Value::String(str!($s))
    };
}

#[macro_export]
macro_rules! vref {
    ($major:expr, $rest:expr) => {
        $crate::value::ValueSemver {
            major: $major as u64,
            rest: $rest,
        }
    };
}

#[macro_export]
macro_rules! v_vref {
    ($major:expr, $rest:expr) => {
        $crate::value::Value::Semver(vref!($major, $rest))
    };
}

#[macro_export]
macro_rules! v {
    [$major:expr] => {
        vref!($major, vec![])
    };

    [$major:expr, $($rest:expr),*] => {
        vref!($major, vec![$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! v_v {
    [$major:expr] => {
        v_vref!($major, vec![])
    };

    [$major:expr, $($rest:expr),*] => {
        v_vref!($major, vec![$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! v_lang {
    ($lang:expr) => {
        $crate::value::Value::LanguageDirective($lang)
    };
}

#[macro_export]
macro_rules! lang_kira_ref {
    ($major:expr, $rest:expr) => {
        $crate::value::ValueLanguageDirective::Kira(vref!($major, $rest))
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
        lang_kira_ref!($major, vec![])
    };

    [$major:expr, $($rest:expr),*] => {
        lang_kira_ref!($major, vec![$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! v_lang_kira {
    [$major:expr] => {
        v_lang_kira_ref!($major, vec![])
    };

    [$major:expr, $($rest:expr),*] => {
        v_lang_kira_ref!($major, vec![$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! lang_other {
    ($name:expr) => {
        $crate::value::ValueLanguageDirective::Other($name.into())
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
        $crate::value::ValueFunction($name)
    };
}

#[macro_export]
macro_rules! v_func {
    ($name:expr) => {
        $crate::value::Value::Function(func!($name))
    };
}

#[macro_export]
macro_rules! bq {
    ($val:expr) => {
        $crate::value::ValueBackquote($val.into())
    };
}

#[macro_export]
macro_rules! v_bq {
    ($val:expr) => {
        $crate::value::Value::Backquote(bq!($val))
    };
}

#[macro_export]
macro_rules! comma {
    ($val:expr) => {
        $crate::value::ValueComma($val.into())
    };
}

#[macro_export]
macro_rules! v_comma {
    ($val:expr) => {
        $crate::value::Value::Comma(comma!($val))
    };
}

#[macro_export]
macro_rules! splice {
    ($val:expr) => {
        $crate::value::ValueSplice($val.into())
    };
}

#[macro_export]
macro_rules! v_splice {
    ($val:expr) => {
        $crate::value::Value::Splice(splice!($val))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    mod macro_tests {
        #[test]
        fn test_uqsym_macro() {
            let uqsym: super::ValueUnqualifiedSymbol = uqsym!("uqsym");
            assert_eq!(uqsym.0, "uqsym");
        }

        #[test]
        fn test_v_uqsym_macro() {
            let uqsym: super::Value = v_uqsym!("uqsym");
            match uqsym {
                super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym"),
                _ => panic!("Expected a Value::Symbol"),
            }
        }

        #[test]
        fn test_qsym_macro() {
            let qsym: super::ValueQualifiedSymbol = qsym!("package", "qsym");
            assert_eq!(qsym.package, "package");
            assert_eq!(qsym.name, "qsym");
        }

        #[test]
        fn test_v_qsym_macro() {
            let qsym: super::Value = v_qsym!("package", "qsym");
            match qsym {
                super::Value::QualifiedSymbol(s) => {
                    assert_eq!(s.package, "package");
                    assert_eq!(s.name, "qsym");
                }
                _ => panic!("Expected a Value::UnqualifiedSymbol"),
            }
        }

        #[test]
        fn test_bool_macro() {
            let bool1: super::ValueBool = bool!(true);
            assert_eq!(bool1.0, true);

            let bool2: super::ValueBool = bool!(false);
            assert_eq!(bool2.0, false);
        }

        #[test]
        fn test_v_bool_macro() {
            let bool1: super::Value = v_bool!(true);
            match bool1 {
                super::Value::Bool(b) => assert_eq!(b.0, true),
                _ => panic!("Expected a Value::Bool"),
            }
            let bool2: super::Value = v_bool!(false);
            match bool2 {
                super::Value::Bool(b) => assert_eq!(b.0, false),
                _ => panic!("Expected a Value::Bool"),
            }
        }

        #[test]
        fn test_str_macro() {
            let s: super::ValueString = str!("str");
            assert_eq!(s.0, "str");
        }

        #[test]
        fn test_v_str_macro() {
            let s: super::Value = v_str!("str");
            match s {
                super::Value::String(s) => assert_eq!(s.0, "str"),
                _ => panic!("Expected a Value::String"),
            }
        }

        #[test]
        fn test_vref_macro() {
            let v1: super::ValueSemver = vref!(1u64, vec![0u64]);
            assert_eq!(v1.major, 1);
            assert_eq!(v1.rest, vec![0]);

            let v2: super::ValueSemver = vref!(4u64, vec![]);
            assert_eq!(v2.major, 4);
            assert_eq!(v2.rest, vec![]);
        }

        #[test]
        fn test_v_vref_macro() {
            let v1: super::Value = v_vref!(1u64, vec![0u64]);
            match v1 {
                super::Value::Semver(v) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, vec![0]);
                }
                _ => panic!("Expected a Value::Semver"),
            }

            let v2: super::Value = v_vref!(4u64, vec![]);
            match v2 {
                super::Value::Semver(v) => {
                    assert_eq!(v.major, 4);
                    assert_eq!(v.rest, vec![]);
                }
                _ => panic!("Expected a Value::Semver"),
            }
        }

        #[test]
        fn test_v_macro() {
            let v1: super::ValueSemver = v![2, 1];
            assert_eq!(v1.major, 2);
            assert_eq!(v1.rest, vec![1]);

            let v2: super::ValueSemver = v![3];
            assert_eq!(v2.major, 3);
            assert_eq!(v2.rest, vec![]);
        }

        #[test]
        fn test_v_v_macro() {
            let v1: super::Value = v_v![2, 1];
            match v1 {
                super::Value::Semver(v) => {
                    assert_eq!(v.major, 2);
                    assert_eq!(v.rest, vec![1]);
                }
                _ => panic!("Expected a Value::Semver"),
            }

            let v2: super::Value = v_v![3];
            match v2 {
                super::Value::Semver(v) => {
                    assert_eq!(v.major, 3);
                    assert_eq!(v.rest, vec![]);
                }
                _ => panic!("Expected a Value::Semver"),
            }
        }

        #[test]
        fn test_lang_kira_macro() {
            let l1: super::ValueLanguageDirective = lang_kira![1];
            match l1 {
                super::ValueLanguageDirective::Kira(v) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, vec![]);
                }
                _ => panic!("Expected a Value::LanguageDirective with Kira"),
            }

            let l2: super::ValueLanguageDirective = lang_kira![1, 0];
            match l2 {
                super::ValueLanguageDirective::Kira(v) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, vec![0]);
                }
                _ => panic!("Expected a Value::LanguageDirective with Kira"),
            }
        }

        #[test]
        fn test_v_lang_kira_macro() {
            let l1: super::Value = v_lang_kira![1];
            match l1 {
                super::Value::LanguageDirective(super::ValueLanguageDirective::Kira(v)) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, vec![]);
                }
                _ => panic!("Expected a Value::LanguageDirective with Kira"),
            }

            let l2: super::Value = v_lang_kira![1, 0];
            match l2 {
                super::Value::LanguageDirective(super::ValueLanguageDirective::Kira(v)) => {
                    assert_eq!(v.major, 1);
                    assert_eq!(v.rest, vec![0]);
                }
                _ => panic!("Expected a Value::LanguageDirective with Kira"),
            }
        }

        #[test]
        fn test_lang_other_macro() {
            let l1: super::ValueLanguageDirective = lang_other!("not-kira");
            match l1 {
                super::ValueLanguageDirective::Other(n) => {
                    assert_eq!(n, "not-kira");
                }
                _ => panic!("Expected a Value::LanguageDirective with other"),
            }
        }

        #[test]
        fn test_v_lang_other_macro() {
            let l1: super::Value = v_lang_other!("not-kira");
            match l1 {
                super::Value::LanguageDirective(super::ValueLanguageDirective::Other(n)) => {
                    assert_eq!(n, "not-kira");
                }
                _ => panic!("Expected a Value::LanguageDirective with other"),
            }
        }

        #[test]
        fn test_func_macro() {
            let f: super::ValueFunction = func!(qsym!("p", "f1"));
            assert_eq!(
                f.0,
                super::ValueQualifiedSymbol {
                    package: "p".to_string(),
                    name: "f1".to_string(),
                }
            );
        }

        #[test]
        fn test_v_func_macro() {
            let f: super::Value = v_func!(qsym!("p", "f1"));
            match f {
                super::Value::Function(super::ValueFunction(name)) => assert_eq!(
                    name,
                    super::ValueQualifiedSymbol {
                        package: "p".to_string(),
                        name: "f1".to_string(),
                    }
                ),
                _ => panic!("Expected a Value::Function"),
            }
        }

        #[test]
        fn test_bq_macro() {
            let bq1: super::ValueBackquote = bq!(v_qsym!("p", "qsym"));
            assert_eq!(*bq1.0, v_qsym!("p", "qsym"));

            let bq2: super::ValueBackquote = bq!(v_str!("str"));
            assert_eq!(*bq2.0, v_str!("str"));
        }

        #[test]
        fn test_v_bq_macro() {
            let bq: super::Value = v_bq!(v_bool!(true));
            match bq {
                super::Value::Backquote(super::ValueBackquote(v)) => assert_eq!(*v, v_bool!(true)),
                _ => panic!("Expected a Value::Backquote"),
            }
        }

        #[test]
        fn test_comma_macro() {
            let c1: super::ValueComma = comma!(v_qsym!("p", "qsym"));
            assert_eq!(*c1.0, v_qsym!("p", "qsym"));

            let c2: super::ValueComma = comma!(v_str!("str"));
            assert_eq!(*c2.0, v_str!("str"));
        }

        #[test]
        fn test_v_comma_macro() {
            let c: super::Value = v_comma!(v_bool!(true));
            match c {
                super::Value::Comma(super::ValueComma(v)) => assert_eq!(*v, v_bool!(true)),
                _ => panic!("Expected a Value::Comma"),
            }
        }

        #[test]
        fn test_splice_macro() {
            let s1: super::ValueSplice = splice!(v_qsym!("p", "qsym"));
            assert_eq!(*s1.0, v_qsym!("p", "qsym"));

            let s2: super::ValueSplice = splice!(v_str!("str"));
            assert_eq!(*s2.0, v_str!("str"));
        }

        #[test]
        fn test_v_splice_macro() {
            let s: super::Value = v_splice!(v_bool!(true));
            match s {
                super::Value::Splice(super::ValueSplice(v)) => assert_eq!(*v, v_bool!(true)),
                _ => panic!("Expected a Value::Splice"),
            }
        }

        #[test]
        fn test_list_macro() {
            let list1: super::ValueList = list!();
            assert_eq!(list1, super::ValueList(Option::None));

            let list2: super::ValueList = list!(v_uqsym!("uqsym1"));
            match list2 {
                super::ValueList(Option::Some(l)) => {
                    match &l.car {
                        super::Value::UnqualifiedSymbol(s) => assert_eq!(s.0, "uqsym1"),
                        _ => panic!("Expected a Value::UnqualifiedSymbol"),
                    }
                    assert_eq!(l.cdr, super::ValueList(Option::None));
                }
                _ => panic!("Expected a ValueList(Option::Some)"),
            }

            let list3: super::ValueList = list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"));
            match list3 {
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
                            assert_eq!(l.cdr, super::ValueList(Option::None));
                        }
                        _ => panic!("Expected a ValueList(Option::Some)"),
                    }
                }
                _ => panic!("Expected a ValueList(Option::Some)"),
            }

            let list4: super::ValueList =
                list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"), v_uqsym!("uqsym3"));
            match list4 {
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
                                    assert_eq!(l.cdr, super::ValueList(Option::None));
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
            let list1: super::Value = v_list!();
            assert_eq!(list1, super::Value::List(list!()));

            let list2: super::Value = v_list!(v_uqsym!("uqsym1"));
            assert_eq!(list2, super::Value::List(list!(v_uqsym!("uqsym1"))));

            let list3: super::Value = v_list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"));
            assert_eq!(
                list3,
                super::Value::List(list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2")))
            );

            let list4: super::Value =
                v_list!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"), v_uqsym!("uqsym3"));
            assert_eq!(
                list4,
                super::Value::List(list!(
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
        assert_ne!(v_uqsym!("uqsym1"), v_uqsym!("uqsym2"));
        assert_ne!(v_uqsym!("uqsym"), v_str!("uqsym"));
        assert_ne!(v_uqsym!("uqsym"), v_list!());

        assert_eq!(v_qsym!("p", "qsym"), v_qsym!("p", "qsym"));
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
        assert_ne!(v_str!("str1"), v_str!("str2"));
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
        assert_eq!(TryInto::<&ValueList>::try_into(&v).unwrap(), &list!());
        assert_eq!(
            TryInto::<&ValueString>::try_into(&v).unwrap_err(),
            &v_list!()
        );

        let v = v_uqsym!("uqsym");
        assert_eq!(
            TryInto::<&ValueUnqualifiedSymbol>::try_into(&v).unwrap(),
            &uqsym!("uqsym")
        );
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_uqsym!("uqsym")
        );

        let v = v_qsym!("p", "qsym");
        assert_eq!(
            TryInto::<&ValueQualifiedSymbol>::try_into(&v).unwrap(),
            &qsym!("p", "qsym")
        );
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_qsym!("p", "qsym")
        );

        let v = v_bool!(true);
        assert_eq!(TryInto::<&ValueBool>::try_into(&v).unwrap(), &bool!(true));
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_bool!(true)
        );

        let v = v_str!("str");
        assert_eq!(TryInto::<&ValueString>::try_into(&v).unwrap(), &str!("str"));
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_str!("str")
        );

        let v = v_v![1, 0];
        assert_eq!(TryInto::<&ValueSemver>::try_into(&v).unwrap(), &v![1, 0]);
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_v![1, 0]
        );

        let v = v_lang_kira![1, 0];
        assert_eq!(
            TryInto::<&ValueLanguageDirective>::try_into(&v).unwrap(),
            &lang_kira![1, 0]
        );
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_lang_kira![1, 0]
        );

        let v = v_func!(qsym!("p", "f1"));
        assert_eq!(
            TryInto::<&ValueFunction>::try_into(&v).unwrap(),
            &func!(qsym!("p", "f1"))
        );
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_func!(qsym!("p", "f1"))
        );

        let v = v_bq!(v_bool!(true));
        assert_eq!(
            TryInto::<&ValueBackquote>::try_into(&v).unwrap(),
            &bq!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_bq!(v_bool!(true))
        );

        let v = v_comma!(v_bool!(true));
        assert_eq!(
            TryInto::<&ValueComma>::try_into(&v).unwrap(),
            &comma!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_comma!(v_bool!(true))
        );

        let v = v_splice!(v_bool!(true));
        assert_eq!(
            TryInto::<&ValueSplice>::try_into(&v).unwrap(),
            &splice!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<&ValueList>::try_into(&v).unwrap_err(),
            &v_splice!(v_bool!(true))
        );
    }

    #[test]
    fn test_try_into_value_type() {
        use std::convert::TryInto;

        let v = v_list!();
        assert_eq!(TryInto::<ValueList>::try_into(v.clone()).unwrap(), list!());
        assert_eq!(TryInto::<ValueString>::try_into(v).unwrap_err(), v_list!());

        let v = v_uqsym!("uqsym");
        assert_eq!(
            TryInto::<ValueUnqualifiedSymbol>::try_into(v.clone()).unwrap(),
            uqsym!("uqsym")
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_uqsym!("uqsym")
        );

        let v = v_qsym!("p", "qsym");
        assert_eq!(
            TryInto::<ValueQualifiedSymbol>::try_into(v.clone()).unwrap(),
            qsym!("p", "qsym")
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_qsym!("p", "qsym")
        );

        let v = v_bool!(true);
        assert_eq!(
            TryInto::<ValueBool>::try_into(v.clone()).unwrap(),
            bool!(true)
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_bool!(true)
        );

        let v = v_str!("str");
        assert_eq!(
            TryInto::<ValueString>::try_into(v.clone()).unwrap(),
            str!("str")
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_str!("str")
        );

        let v = v_v![1, 0];
        assert_eq!(
            TryInto::<ValueSemver>::try_into(v.clone()).unwrap(),
            v![1, 0]
        );
        assert_eq!(TryInto::<ValueList>::try_into(v).unwrap_err(), v_v![1, 0]);

        let v = v_lang_kira![1, 0];
        assert_eq!(
            TryInto::<ValueLanguageDirective>::try_into(v.clone()).unwrap(),
            lang_kira![1, 0]
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_lang_kira![1, 0]
        );

        let v = v_func!(qsym!("p", "f1"));
        assert_eq!(
            TryInto::<ValueFunction>::try_into(v.clone()).unwrap(),
            func!(qsym!("p", "f1"))
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_func!(qsym!("p", "f1"))
        );

        let v = v_bq!(v_bool!(true));
        assert_eq!(
            TryInto::<ValueBackquote>::try_into(v.clone()).unwrap(),
            bq!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_bq!(v_bool!(true))
        );

        let v = v_comma!(v_bool!(true));
        assert_eq!(
            TryInto::<ValueComma>::try_into(v.clone()).unwrap(),
            comma!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_comma!(v_bool!(true))
        );

        let v = v_splice!(v_bool!(true));
        assert_eq!(
            TryInto::<ValueSplice>::try_into(v.clone()).unwrap(),
            splice!(v_bool!(true))
        );
        assert_eq!(
            TryInto::<ValueList>::try_into(v).unwrap_err(),
            v_splice!(v_bool!(true))
        );
    }

    #[test]
    fn test_into_value() {
        let v: Value = list!().into();
        assert_eq!(v, v_list!());

        let v: Value = uqsym!("uqsym").into();
        assert_eq!(v, v_uqsym!("uqsym"));

        let v: Value = qsym!("p", "qsym").into();
        assert_eq!(v, v_qsym!("p", "qsym"));

        let v: Value = bool!(true).into();
        assert_eq!(v, v_bool!(true));

        let v: Value = str!("str").into();
        assert_eq!(v, v_str!("str"));

        let v: Value = v![1, 0].into();
        assert_eq!(v, v_v![1, 0]);

        let v: Value = lang_kira![1, 0].into();
        assert_eq!(v, v_lang_kira![1, 0]);

        let v: Value = func!(qsym!("p", "f1")).into();
        assert_eq!(v, v_func!(qsym!("p", "f1")));

        let v: Value = bq!(v_bool!(true)).into();
        assert_eq!(v, v_bq!(v_bool!(true)));

        let v: Value = comma!(v_bool!(true)).into();
        assert_eq!(v, v_comma!(v_bool!(true)));

        let v: Value = splice!(v_bool!(true)).into();
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
