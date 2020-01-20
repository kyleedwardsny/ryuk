use super::algo::*;
use super::error::*;
use super::list::*;
use super::value::*;
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::iter::FromIterator;

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
        params: Value<T>,
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
        params: Value<T>,
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
    Backquote(Box<ValueType>),
    Comma(Box<ValueType>),
    Splice(Box<ValueType>),
}

pub trait CompilationResultType<T>: Debug
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>>;
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
pub struct ConcatenateLists<T>(Vec<ListItem<Box<dyn CompilationResultType<T>>>>)
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>;

impl<T> ConcatenateLists<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn new(items: Vec<ListItem<Box<dyn CompilationResultType<T>>>>) -> Self {
        Self(items)
    }
}

impl<T> CompilationResultType<T> for ConcatenateLists<T>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    Cons<T>: Into<T::ConsRef>,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>> {
        let mut items = Vec::new();
        for item in &mut self.0 {
            items.push(item.as_mut().map(|comp| comp.evaluate(env)).transpose()?);
        }
        concat_lists(items.into_iter())
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

#[cfg(test)]
mod tests {
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
            v_bq!(v_qsym!("p", "f1")).value_type(),
            ValueType::NonList(ValueTypeNonList::Backquote(Box::new(ValueType::NonList(
                ValueTypeNonList::QualifiedSymbol
            ))))
        );
        assert_eq!(
            v_comma!(v_qsym!("p", "f1")).value_type(),
            ValueType::NonList(ValueTypeNonList::Comma(Box::new(ValueType::NonList(
                ValueTypeNonList::QualifiedSymbol
            ))))
        );
        assert_eq!(
            v_splice!(v_qsym!("p", "f1")).value_type(),
            ValueType::NonList(ValueTypeNonList::Splice(Box::new(ValueType::NonList(
                ValueTypeNonList::QualifiedSymbol
            ))))
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
            v: super::Value<super::ValueTypesRc>,
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

    #[test]
    fn test_evaluate_concatenate_lists() {
        use super::*;

        let mut env = SimpleEnvironment;

        let mut comp = ConcatenateLists::new(vec![
            ListItem::List(Box::new(Literal::new(v_list!(v_str!("str")).convert()))),
            ListItem::List(Box::new(Literal::new(v_list!(v_bool!(true)).convert()))),
        ]);
        assert_eq!(
            comp.evaluate(&mut env).unwrap(),
            v_list!(v_str!("str"), v_bool!(true))
        );

        let mut comp = ConcatenateLists::new(vec![
            ListItem::Item(Box::new(Literal::new(v_str!("str").convert()))),
            ListItem::List(Box::new(Literal::new(v_bool!(true).convert()))),
        ]);
        assert_eq!(
            comp.evaluate(&mut env).unwrap(),
            v_cons!(v_str!("str"), v_bool!(true))
        );

        let mut comp = ConcatenateLists::new(vec![
            ListItem::List(Box::new(Literal::new(v_str!("str").convert()))),
            ListItem::List(Box::new(Literal::new(v_bool!(true).convert()))),
        ]);
        assert_eq!(
            comp.evaluate(&mut env).unwrap_err().kind,
            ErrorKind::IncorrectType
        );
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
}
