use ryuk_lisptypes::*;
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::iter::FromIterator;

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ValueType {
    List(ValueTypeList),
    NonList(ValueTypeNonList),
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ValueTypeList {
    pub items: BTreeSet<ValueType>,
    pub tail: BTreeSet<ValueTypeNonNil>,
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ValueTypeNonList {
    Nil,
    NonNil(ValueTypeNonNil),
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ValueTypeNonNil {
    UnqualifiedSymbol,
    QualifiedSymbol,
    Bool,
    String,
    Semver,
    LanguageDirective,
    Procedure,
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
                    tail: BTreeSet::new(),
                };
                for item in LispList::<T>::new(c.cdr.clone()) {
                    match item {
                        LispListItem::Item(i) => l.items.insert(ValueType::from(i.borrow())),
                        LispListItem::Tail(t) => l.tail.insert(ValueTypeNonNil::from(t.borrow())),
                    };
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
            _ => ValueTypeNonList::NonNil(ValueTypeNonNil::from(v)),
        }
    }
}

impl<T> From<&Value<T>> for ValueTypeNonNil
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    T::ValueRef: Clone,
{
    fn from(v: &Value<T>) -> Self {
        match v {
            Value::Nil => panic!("Unexpected Value::Nil"),
            Value::UnqualifiedSymbol(_) => ValueTypeNonNil::UnqualifiedSymbol,
            Value::QualifiedSymbol(_) => ValueTypeNonNil::QualifiedSymbol,
            Value::Cons(_) => panic!("Unexpected Value::Cons"),
            Value::Bool(_) => ValueTypeNonNil::Bool,
            Value::String(_) => ValueTypeNonNil::String,
            Value::Semver(_) => ValueTypeNonNil::Semver,
            Value::LanguageDirective(_) => ValueTypeNonNil::LanguageDirective,
            Value::Procedure(_) => ValueTypeNonNil::Procedure,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn static_f1(
        _: &mut (dyn Environment<ValueTypesStatic> + 'static),
        _: &Value<ValueTypesStatic>,
    ) -> Result<&'static Value<ValueTypesStatic>> {
        Result::Ok(&Value::Nil)
    }

    #[test]
    fn test_from_non_nil() {
        assert_eq!(
            ValueTypeNonNil::from(uqsym!("uqsym")),
            ValueTypeNonNil::UnqualifiedSymbol
        );
        assert_eq!(
            ValueTypeNonNil::from(qsym!("p", "qsym")),
            ValueTypeNonNil::QualifiedSymbol
        );
        assert_eq!(ValueTypeNonNil::from(bool!(true)), ValueTypeNonNil::Bool);
        assert_eq!(ValueTypeNonNil::from(str!("str")), ValueTypeNonNil::String);
        assert_eq!(ValueTypeNonNil::from(v![1, 0]), ValueTypeNonNil::Semver);
        assert_eq!(
            ValueTypeNonNil::from(lang_kira![1, 0]),
            ValueTypeNonNil::LanguageDirective
        );
        assert_eq!(
            ValueTypeNonNil::from(proc!(1, &static_f1)),
            ValueTypeNonNil::Procedure
        );
    }

    #[test]
    fn test_from_non_list() {
        assert_eq!(ValueTypeNonList::from(nil!()), ValueTypeNonList::Nil);
        assert_eq!(
            ValueTypeNonList::from(bool!(true)),
            ValueTypeNonList::NonNil(ValueTypeNonNil::Bool)
        );
    }

    #[test]
    fn test_from_list() {
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
                    ValueType::NonList(ValueTypeNonList::NonNil(ValueTypeNonNil::Bool)),
                    ValueType::NonList(ValueTypeNonList::NonNil(ValueTypeNonNil::String)),
                    ValueType::List(ValueTypeList {
                        items: BTreeSet::from_iter(vec![
                            ValueType::NonList(ValueTypeNonList::NonNil(
                                ValueTypeNonNil::UnqualifiedSymbol
                            )),
                            ValueType::NonList(ValueTypeNonList::NonNil(ValueTypeNonNil::Bool)),
                        ]),
                        tail: BTreeSet::from_iter(vec![ValueTypeNonNil::QualifiedSymbol,]),
                    }),
                ]),
                tail: BTreeSet::new(),
            })
        );
    }
}
