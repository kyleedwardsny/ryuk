use ryuk_lisptypes::*;
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::iter::FromIterator;
use std::rc::Rc;

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

    struct SimpleCompiler;

    impl Compiler<CompilerTypesRc> for SimpleCompiler {
        fn resolve_symbol_get_macro(
            &self,
            _name: &ValueUnqualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>,
        ) -> Result<ValueQualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>> {
            Result::Err(Error::new(
                ErrorKind::NoPackageForSymbol,
                "No package for symbol",
            ))
        }

        fn get_macro(
            &self,
            _name: &ValueQualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>,
        ) -> Result<<CompilerTypesRc as CompilerTypes>::MacroRef> {
            Result::Err(Error::new(ErrorKind::ValueNotDefined, "Value not defined"))
        }
    }

    fn test_literal(
        comp: &SimpleCompiler,
        code: <ValueTypesStatic as ValueTypes>::ValueRef,
        t: ValueType,
    ) {
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
