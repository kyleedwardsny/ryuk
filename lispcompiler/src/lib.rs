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
            Value::Procedure(_) => ValueTypeNonList::Procedure,
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
    fn test_from_non_list() {
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
            ValueTypeNonList::from(proc!(1, &static_f1)),
            ValueTypeNonList::Procedure
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
}
