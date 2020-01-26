use super::algo::*;
use super::error::*;
use super::list::*;
use super::value::*;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::iter::FromIterator;

pub trait Environment<T>
where
    T: ValueTypes + ?Sized + 'static,
    Value<T>: Clone,
{
    fn as_dyn_mut(&mut self) -> &mut (dyn Environment<T> + 'static);

    fn resolve_symbol_get_variable(
        &self,
        name: &ValueUnqualifiedSymbol<T::StringTypes>,
    ) -> Option<ValueQualifiedSymbol<T::StringTypes>>;

    fn compile_variable(
        &self,
        name: &ValueQualifiedSymbol<T::StringTypes>,
    ) -> Option<BTreeSet<ValueType>>;

    fn resolve_symbol_get_macro(
        &self,
        name: &ValueUnqualifiedSymbol<T::StringTypes>,
    ) -> Option<ValueQualifiedSymbol<T::StringTypes>>;

    fn compile_function(
        &self,
        name: &ValueQualifiedSymbol<T::StringTypes>,
        params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
    ) -> Option<Result<BTreeSet<ValueType>>>;

    fn compile_function_from_macro(
        &mut self,
        name: &ValueQualifiedSymbol<T::StringTypes>,
        params: ValueList<T>,
    ) -> Option<Result<TryCompilationResult<T>>> {
        let mut compiled_params = Vec::new();
        for item in params.map(|v| self.compile(v)) {
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
                    result: Box::new(FunctionCallEvaluator::new(
                        ValueFunction(name.clone()),
                        compiled_params.into_iter().map(|p| p.result).collect(),
                    )),
                    types: r,
                })),
                Result::Err(e) => Result::Err(e),
            },
        )
    }

    fn evaluate_variable(&self, name: &ValueQualifiedSymbol<T::StringTypes>) -> Result<Value<T>>;

    fn evaluate_function(
        &mut self,
        name: &ValueQualifiedSymbol<T::StringTypes>,
        params: Vec<Value<T>>,
    ) -> Result<Value<T>>;

    fn compile_macro(
        &mut self,
        name: &ValueQualifiedSymbol<T::StringTypes>,
        params: ValueList<T>,
    ) -> Option<Result<TryCompilationResult<T>>>;

    fn compile(&mut self, v: Value<T>) -> Result<CompilationResult<T>> {
        let mut result = TryCompilationResult::<T>::Uncompiled(v);

        loop {
            match result {
                TryCompilationResult::Uncompiled(v) => {
                    result = match v {
                        Value::List(ValueList(Option::Some(l))) => {
                            let list = T::cons_ref_to_cons(&l);
                            let name = match &list.car {
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
                            match self.compile_macro(&name, list.cdr.clone()) {
                                Option::Some(r) => r?,
                                Option::None => {
                                    return Result::Err(Error::new(
                                        ErrorKind::ValueNotDefined,
                                        "Value not defined",
                                    ))
                                }
                            }
                        }
                        Value::UnqualifiedSymbol(name) => {
                            match self.resolve_symbol_get_variable(&name) {
                                Option::Some(name) => match self.compile_variable(&name) {
                                    Option::Some(types) => {
                                        TryCompilationResult::Compiled(CompilationResult {
                                            result: Box::new(VariableEvaluator::new(name)),
                                            types,
                                        })
                                    }
                                    Option::None => {
                                        return Result::Err(Error::new(
                                            ErrorKind::ValueNotDefined,
                                            "Value not defined",
                                        ))
                                    }
                                },
                                Option::None => {
                                    return Result::Err(Error::new(
                                        ErrorKind::ValueNotDefined,
                                        "Value not defined",
                                    ))
                                }
                            }
                        }
                        Value::QualifiedSymbol(name) => match self.compile_variable(&name) {
                            Option::Some(types) => {
                                TryCompilationResult::Compiled(CompilationResult {
                                    result: Box::new(VariableEvaluator::new(name)),
                                    types,
                                })
                            }
                            Option::None => {
                                return Result::Err(Error::new(
                                    ErrorKind::ValueNotDefined,
                                    "Value not defined",
                                ))
                            }
                        },
                        _ => {
                            let t = v.value_type();
                            TryCompilationResult::Compiled(CompilationResult {
                                result: Box::new(LiteralEvaluator::new(v)),
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
    List(BTreeSet<ValueType>),
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

pub trait Evaluator<T>: Debug
where
    T: ValueTypes + ?Sized + 'static,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>>;
}

#[derive(Debug)]
pub struct LiteralEvaluator<T>(Value<T>)
where
    T: ValueTypes + ?Sized;

impl<T> LiteralEvaluator<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn new(value: Value<T>) -> Self {
        Self(value)
    }
}

impl<T> Evaluator<T> for LiteralEvaluator<T>
where
    T: ValueTypes + ?Sized + 'static,
{
    fn evaluate(&mut self, _env: &mut dyn Environment<T>) -> Result<Value<T>> {
        Result::Ok(self.0.clone())
    }
}

#[derive(Debug)]
pub struct VariableEvaluator<T>(ValueQualifiedSymbol<T::StringTypes>)
where
    T: ValueTypes + ?Sized + 'static;

impl<T> VariableEvaluator<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn new(name: ValueQualifiedSymbol<T::StringTypes>) -> Self {
        Self(name)
    }
}

impl<T> Evaluator<T> for VariableEvaluator<T>
where
    T: ValueTypes + ?Sized + 'static,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>> {
        env.evaluate_variable(&self.0)
    }
}

#[derive(Debug)]
pub struct FunctionCallEvaluator<T>
where
    T: ValueTypes + ?Sized,
{
    name: ValueFunction<T::StringTypes>,
    params: Vec<Box<dyn Evaluator<T>>>,
}

impl<T> FunctionCallEvaluator<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn new(name: ValueFunction<T::StringTypes>, params: Vec<Box<dyn Evaluator<T>>>) -> Self {
        Self { name, params }
    }
}

impl<T> Evaluator<T> for FunctionCallEvaluator<T>
where
    T: ValueTypes + ?Sized + 'static,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>> {
        use std::borrow::BorrowMut;

        let params = (&mut self.params)
            .into_iter()
            .map(|p| BorrowMut::<dyn Evaluator<T>>::borrow_mut(p).evaluate(env))
            .collect::<Result<Vec<Value<T>>>>()?;
        env.evaluate_function(&self.name.0, params)
    }
}

#[derive(Debug)]
pub struct ConcatenateListsEvaluator<T>(Vec<ListItem<Box<dyn Evaluator<T>>>>)
where
    T: ValueTypes + ?Sized;

impl<T> ConcatenateListsEvaluator<T>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
{
    pub fn new(items: Vec<ListItem<Box<dyn Evaluator<T>>>>) -> Self {
        Self(items)
    }
}

impl<T> Evaluator<T> for ConcatenateListsEvaluator<T>
where
    T: ValueTypesMut + ?Sized + 'static,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>> {
        let mut items = Vec::new();
        for item in &mut self.0 {
            items.push(item.as_mut().map(|comp| comp.evaluate(env)).transpose()?);
        }
        Result::Ok(Value::List(concat_lists(items.into_iter())?))
    }
}

#[derive(Debug)]
pub struct CompilationResult<T>
where
    T: ValueTypes + ?Sized,
{
    pub result: Box<dyn Evaluator<T> + 'static>,
    pub types: BTreeSet<ValueType>,
}

pub enum TryCompilationResult<T>
where
    T: ValueTypes + ?Sized,
{
    Compiled(CompilationResult<T>),
    Uncompiled(Value<T>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_type() {
        assert_eq!(
            v_list!(
                v_bool!(true),
                v_str!("str"),
                v_list!(v_uqsym!("uqsym"), v_bool!(true), v_qsym!("p", "qsym"))
            )
            .value_type(),
            ValueType::List(BTreeSet::from_iter(vec![
                ValueType::Bool,
                ValueType::String,
                ValueType::List(BTreeSet::from_iter(vec![
                    ValueType::UnqualifiedSymbol,
                    ValueType::QualifiedSymbol,
                    ValueType::Bool,
                ])),
            ]),)
        );
        assert_eq!(v_uqsym!("uqsym").value_type(), ValueType::UnqualifiedSymbol);
        assert_eq!(
            v_qsym!("p", "qsym").value_type(),
            ValueType::QualifiedSymbol
        );
        assert_eq!(v_bool!(true).value_type(), ValueType::Bool);
        assert_eq!(v_str!("str").value_type(), ValueType::String);
        assert_eq!(v_v![1, 0].value_type(), ValueType::Semver);
        assert_eq!(
            v_lang_kira![1, 0].value_type(),
            ValueType::LanguageDirective
        );
        assert_eq!(v_func!(qsym!("p", "f1")).value_type(), ValueType::Function);
        assert_eq!(
            v_bq!(v_qsym!("p", "f1")).value_type(),
            ValueType::Backquote(Box::new(ValueType::QualifiedSymbol))
        );
        assert_eq!(
            v_comma!(v_qsym!("p", "f1")).value_type(),
            ValueType::Comma(Box::new(ValueType::QualifiedSymbol))
        );
        assert_eq!(
            v_splice!(v_qsym!("p", "f1")).value_type(),
            ValueType::Splice(Box::new(ValueType::QualifiedSymbol))
        );
    }

    struct SimpleEnvironment;

    fn simplemacro1() -> Result<TryCompilationResult<ValueTypesRc>> {
        Result::Ok(TryCompilationResult::Compiled(CompilationResult {
            result: Box::new(LiteralEvaluator::new(v_str!("Hello world!").convert())),
            types: BTreeSet::from_iter(vec![ValueType::String]),
        }))
    }

    fn simplemacro2() -> Result<TryCompilationResult<ValueTypesRc>> {
        Result::Ok(TryCompilationResult::Compiled(CompilationResult {
            result: Box::new(LiteralEvaluator::new(v_bool!(true).convert())),
            types: BTreeSet::from_iter(vec![ValueType::Bool]),
        }))
    }

    fn compile_simplefunc1(
        params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
    ) -> Result<BTreeSet<ValueType>> {
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
        _env: &mut dyn Environment<ValueTypesRc>,
        params: Vec<Value<ValueTypesRc>>,
    ) -> Result<Value<ValueTypesRc>> {
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

    impl Environment<ValueTypesRc> for SimpleEnvironment {
        fn as_dyn_mut(&mut self) -> &mut (dyn Environment<ValueTypesRc> + 'static) {
            self as &mut (dyn Environment<ValueTypesRc> + 'static)
        }

        fn resolve_symbol_get_variable(
            &self,
            name: &ValueUnqualifiedSymbol<StringTypesString>,
        ) -> Option<ValueQualifiedSymbol<StringTypesString>> {
            Option::Some(ValueQualifiedSymbol {
                package: "pvar".to_string(),
                name: name.0.clone(),
            })
        }

        fn compile_variable(
            &self,
            name: &ValueQualifiedSymbol<StringTypesString>,
        ) -> Option<BTreeSet<ValueType>> {
            match (&*name.package, &*name.name) {
                ("pvar", "var1") => Option::Some(BTreeSet::from_iter(vec![ValueType::String])),
                ("pvar", "var2") => Option::Some(BTreeSet::from_iter(vec![ValueType::Bool])),
                _ => Option::None,
            }
        }

        fn evaluate_variable(
            &self,
            name: &ValueQualifiedSymbol<StringTypesString>,
        ) -> Result<Value<ValueTypesRc>> {
            match (&*name.package, &*name.name) {
                ("pvar", "var1") => Result::Ok(Value::String(ValueString("str".to_string()))),
                ("pvar", "var2") => Result::Ok(Value::Bool(ValueBool(true))),
                _ => Result::Err(Error::new(ErrorKind::ValueNotDefined, "Value not defined")),
            }
        }

        fn evaluate_function(
            &mut self,
            name: &ValueQualifiedSymbol<StringTypesString>,
            params: Vec<Value<ValueTypesRc>>,
        ) -> Result<Value<ValueTypesRc>> {
            match (&*name.package, &*name.name) {
                ("p", "simplefunc1") => simplefunc1(self, params),
                _ => Result::Err(Error::new(ErrorKind::ValueNotDefined, "Value not defined")),
            }
        }

        fn resolve_symbol_get_macro(
            &self,
            name: &ValueUnqualifiedSymbol<StringTypesString>,
        ) -> Option<ValueQualifiedSymbol<StringTypesString>> {
            Option::Some(ValueQualifiedSymbol {
                package: "p".to_string(),
                name: name.0.clone(),
            })
        }

        fn compile_macro(
            &mut self,
            name: &ValueQualifiedSymbol<StringTypesString>,
            params: ValueList<ValueTypesRc>,
        ) -> Option<Result<TryCompilationResult<ValueTypesRc>>> {
            match (&*name.package, &*name.name) {
                ("p", "simplemacro1") => Option::Some(simplemacro1()),
                ("p", "simplemacro2") => Option::Some(simplemacro2()),
                ("p", "simplefunc1") => self.compile_function_from_macro(name, params),
                _ => Option::None,
            }
        }

        fn compile_function(
            &self,
            name: &ValueQualifiedSymbol<StringTypesString>,
            params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
        ) -> Option<Result<BTreeSet<ValueType>>> {
            match (&*name.package, &*name.name) {
                ("p", "simplefunc1") => Option::Some(compile_simplefunc1(params)),
                _ => Option::None,
            }
        }
    }

    fn test_compile_and_evaluate(
        env: &mut SimpleEnvironment,
        code: Value<ValueTypesStatic>,
        result: Value<ValueTypesStatic>,
        types: BTreeSet<ValueType>,
    ) {
        let mut comp = env.compile(code.convert()).unwrap();
        assert_eq!(comp.types, types);
        assert_eq!(comp.result.evaluate(env).unwrap(), result);
    }

    #[test]
    fn test_evaluate_literal() {
        let mut env = SimpleEnvironment;

        let mut comp = LiteralEvaluator::new(v_str!("Hello world!").convert());
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("Hello world!"));

        let mut comp = LiteralEvaluator::new(v_bool!(true).convert());
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_bool!(true));
    }

    #[test]
    fn test_evaluate_variable() {
        let mut env = SimpleEnvironment;

        let mut comp = VariableEvaluator::new(qsym!("pvar", "var1").convert());
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("str"));

        let mut comp = VariableEvaluator::new(qsym!("pvar", "var2").convert());
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_bool!(true));

        let mut comp = VariableEvaluator::new(qsym!("pvar", "var3").convert());
        assert_eq!(
            comp.evaluate(&mut env).unwrap_err().kind,
            ErrorKind::ValueNotDefined
        );
    }

    #[test]
    fn test_evaluate_function() {
        let mut env = SimpleEnvironment;

        let mut comp = FunctionCallEvaluator::new(
            func!(qsym!("p", "simplefunc1")).convert(),
            vec![Box::new(LiteralEvaluator::new(
                v_str!("Hello world!").convert(),
            ))],
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("Hello world!"));

        let mut comp = FunctionCallEvaluator::new(
            func!(qsym!("p", "simplefunc1")).convert(),
            vec![Box::new(LiteralEvaluator::new(v_bool!(true).convert()))],
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_bool!(true));
    }

    #[test]
    fn test_evaluate_concatenate_lists() {
        let mut env = SimpleEnvironment;

        let mut comp = ConcatenateListsEvaluator::new(vec![
            ListItem::List(Box::new(LiteralEvaluator::new(
                v_list!(v_str!("str")).convert(),
            ))),
            ListItem::List(Box::new(LiteralEvaluator::new(
                v_list!(v_bool!(true)).convert(),
            ))),
        ]);
        assert_eq!(
            comp.evaluate(&mut env).unwrap(),
            v_list!(v_str!("str"), v_bool!(true))
        );

        let mut comp = ConcatenateListsEvaluator::new(vec![ListItem::List(Box::new(
            LiteralEvaluator::new(v_bool!(true).convert()),
        ))]);
        assert_eq!(
            comp.evaluate(&mut env).unwrap_err().kind,
            ErrorKind::IncorrectType
        );
    }

    #[test]
    fn test_compile_and_evaluate_literal() {
        let mut env = SimpleEnvironment;
        test_compile_and_evaluate(
            &mut env,
            v_list!(),
            v_list!(),
            BTreeSet::from_iter(vec![ValueType::List(BTreeSet::new())]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_bool!(true),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_str!("Hello world!"),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_v![1, 0],
            v_v![1, 0],
            BTreeSet::from_iter(vec![ValueType::Semver]),
        );
    }

    #[test]
    fn test_compile_and_evaluate_variable() {
        let mut env = SimpleEnvironment;
        test_compile_and_evaluate(
            &mut env,
            v_uqsym!("var1"),
            v_str!("str"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_uqsym!("var2"),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_uqsym!("var3").convert()).unwrap_err().kind,
            ErrorKind::ValueNotDefined
        );

        test_compile_and_evaluate(
            &mut env,
            v_qsym!("pvar", "var1"),
            v_str!("str"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_qsym!("pvar", "var2"),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_qsym!("pvar", "var3").convert())
                .unwrap_err()
                .kind,
            ErrorKind::ValueNotDefined
        );
    }

    #[test]
    fn test_compile_and_evaluate_macro() {
        let mut env = SimpleEnvironment;

        test_compile_and_evaluate(
            &mut env,
            v_list!(v_uqsym!("simplemacro1")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_list!(v_uqsym!("simplemacro2")),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
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
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_list!(v_qsym!("p", "simplemacro2")),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
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
        let mut env = SimpleEnvironment;

        test_compile_and_evaluate(
            &mut env,
            v_list!(v_uqsym!("simplefunc1"), v_str!("Hello world!")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_list!(v_uqsym!("simplefunc1"), v_bool!(true)),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
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
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            &mut env,
            v_list!(v_qsym!("p", "simplefunc1"), v_bool!(true)),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_list!(v_qsym!("p", "simplefunc1")).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectParams
        );
    }
}
