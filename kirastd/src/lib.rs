use ryuk_lispcore::env::*;
use ryuk_lispcore::error::*;
use ryuk_lispcore::value::*;
use std::collections::BTreeSet;

#[derive(Debug)]
struct IfEvaluator<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    test: Box<dyn Evaluator<T>>,
    then: Box<dyn Evaluator<T>>,
    els: Box<dyn Evaluator<T>>,
}

impl<T> IfEvaluator<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn new(
        test: Box<dyn Evaluator<T>>,
        then: Box<dyn Evaluator<T>>,
        els: Box<dyn Evaluator<T>>,
    ) -> Self {
        Self { test, then, els }
    }
}

impl<T> Evaluator<T> for IfEvaluator<T>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>> {
        use std::convert::TryInto;

        let b: ValueBool = self.test.evaluate(env)?.try_into()?;
        if b.0 {
            self.then.evaluate(env)
        } else {
            self.els.evaluate(env)
        }
    }
}

pub fn compile_if<T>(
    env: &mut dyn Environment<T>,
    mut params: ValueList<T>,
) -> Result<CompilationResult<T>>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    use std::iter::FromIterator;

    let mut types = BTreeSet::new();

    let test;
    match params.next() {
        Option::Some(test_item) => {
            let test_comp = env.compile(test_item)?;
            if test_comp.types != BTreeSet::from_iter(vec![ValueType::Bool]) {
                return Result::Err(Error::new(ErrorKind::IncorrectType, "Incorrect type"));
            }
            test = test_comp.result;
        }
        _ => {
            return Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            ))
        }
    }

    let then;
    match params.next() {
        Option::Some(then_item) => {
            let then_comp = env.compile(then_item)?;
            types.append(&mut then_comp.types.clone());
            then = then_comp.result;
        }
        _ => {
            return Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            ))
        }
    }

    let els;
    match params.next() {
        Option::Some(els_item) => {
            let els_comp = env.compile(els_item)?;
            types.append(&mut els_comp.types.clone());
            els = els_comp.result;
        }
        Option::None => {
            types.insert(ValueType::List(BTreeSet::new()));
            els = Box::new(LiteralEvaluator::new(Value::List(ValueList(Option::None))));
        }
    }

    match params.next() {
        Option::Some(_) => {
            return Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            ))
        }
        _ => (),
    }

    Result::Ok(CompilationResult {
        result: Box::new(IfEvaluator::new(test, then, els)),
        types,
    })
}

pub fn compile_quote<T>(
    _env: &mut dyn Environment<T>,
    mut params: ValueList<T>,
) -> Result<CompilationResult<T>>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    use std::iter::FromIterator;

    let result;
    match params.next() {
        Option::Some(val) => result = val,
        _ => {
            return Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            ))
        }
    }

    match params.next() {
        Option::Some(_) => {
            return Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            ))
        }
        _ => (),
    }

    let types = BTreeSet::from_iter(vec![result.value_type()]);
    Result::Ok(CompilationResult {
        result: Box::new(LiteralEvaluator::new(result)),
        types,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ryuk_lispcore::*;

    struct SimpleEnvironment;

    impl Environment<ValueTypesRc> for SimpleEnvironment {
        fn as_dyn_mut(&mut self) -> &mut (dyn Environment<ValueTypesRc> + 'static) {
            self as &mut (dyn Environment<ValueTypesRc> + 'static)
        }

        fn resolve_symbol_get_variable(
            &self,
            _name: &ValueUnqualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>,
        ) -> Option<ValueQualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>> {
            Option::None
        }

        fn compile_variable(
            &self,
            _name: &ValueQualifiedSymbol<String>,
        ) -> Option<BTreeSet<ValueType>> {
            Option::None
        }

        fn evaluate_variable(
            &self,
            _name: &ValueQualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>,
        ) -> Result<Value<ValueTypesRc>> {
            Result::Err(Error::new(ErrorKind::ValueNotDefined, "Value not defined"))
        }

        fn evaluate_function(
            &mut self,
            _name: &ValueQualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>,
            _params: Vec<Value<ValueTypesRc>>,
        ) -> Result<Value<ValueTypesRc>> {
            Result::Err(Error::new(ErrorKind::ValueNotDefined, "Value not defined"))
        }

        fn resolve_symbol_get_macro(
            &self,
            _name: &ValueUnqualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>,
        ) -> Option<ValueQualifiedSymbol<<ValueTypesRc as ValueTypes>::StringRef>> {
            Option::None
        }

        fn compile_macro(
            &mut self,
            name: &ValueQualifiedSymbol<String>,
            params: ValueList<ValueTypesRc>,
        ) -> Option<Result<TryCompilationResult<ValueTypesRc>>> {
            use std::borrow::Borrow;

            match (name.package.borrow(), name.name.borrow()) {
                ("std", "if") => Option::Some(match compile_if(self, params) {
                    Result::Ok(r) => Result::Ok(TryCompilationResult::Compiled(r)),
                    Result::Err(e) => Result::Err(e),
                }),
                _ => Option::None,
            }
        }

        fn compile_function(
            &self,
            _name: &ValueQualifiedSymbol<String>,
            _params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
        ) -> Option<Result<BTreeSet<ValueType>>> {
            Option::None
        }
    }

    #[test]
    fn test_evaluate_if() {
        let mut env = SimpleEnvironment;

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_bool!(true).convert())),
            Box::new(LiteralEvaluator::new(v_str!("yes").convert())),
            Box::new(LiteralEvaluator::new(v_str!("no").convert())),
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("yes"));

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_bool!(false).convert())),
            Box::new(LiteralEvaluator::new(v_str!("yes").convert())),
            Box::new(LiteralEvaluator::new(v_str!("no").convert())),
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("no"));

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_bool!(true).convert())),
            Box::new(LiteralEvaluator::new(v_str!("yes").convert())),
            Box::new(LiteralEvaluator::new(v_list!().convert())),
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("yes"));

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_bool!(false).convert())),
            Box::new(LiteralEvaluator::new(v_str!("yes").convert())),
            Box::new(LiteralEvaluator::new(v_list!().convert())),
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_list!());

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_str!("true").convert())),
            Box::new(LiteralEvaluator::new(v_str!("yes").convert())),
            Box::new(LiteralEvaluator::new(v_list!().convert())),
        );
        assert_eq!(
            comp.evaluate(&mut env).unwrap_err().kind,
            ErrorKind::IncorrectType
        );
    }

    #[test]
    fn test_compile_and_evaluate_if() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;

        let mut comp = compile_if(
            &mut env,
            list!(v_bool!(true), v_str!("yes"), v_str!("no")).convert(),
        )
        .unwrap();
        assert_eq!(comp.result.evaluate(&mut env).unwrap(), v_str!("yes"));
        assert_eq!(comp.types, BTreeSet::from_iter(vec![ValueType::String]));

        let mut comp = compile_if(
            &mut env,
            list!(v_bool!(false), v_str!("yes"), v_str!("no")).convert(),
        )
        .unwrap();
        assert_eq!(comp.result.evaluate(&mut env).unwrap(), v_str!("no"));
        assert_eq!(comp.types, BTreeSet::from_iter(vec![ValueType::String]));

        let mut comp = compile_if(&mut env, list!(v_bool!(true), v_str!("yes")).convert()).unwrap();
        assert_eq!(comp.result.evaluate(&mut env).unwrap(), v_str!("yes"));
        assert_eq!(
            comp.types,
            BTreeSet::from_iter(vec![ValueType::List(BTreeSet::new()), ValueType::String,])
        );

        let mut comp =
            compile_if(&mut env, list!(v_bool!(false), v_str!("yes")).convert()).unwrap();
        assert_eq!(comp.result.evaluate(&mut env).unwrap(), v_list!());
        assert_eq!(
            comp.types,
            BTreeSet::from_iter(vec![ValueType::List(BTreeSet::new()), ValueType::String,])
        );

        assert_eq!(
            compile_if(&mut env, list!().convert()).unwrap_err().kind,
            ErrorKind::IncorrectParams
        );

        assert_eq!(
            compile_if(&mut env, list!(v_bool!(true)).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectParams
        );

        assert_eq!(
            compile_if(
                &mut env,
                list!(v_bool!(true), v_list!(), v_list!(), v_list!()).convert()
            )
            .unwrap_err()
            .kind,
            ErrorKind::IncorrectParams
        );

        assert_eq!(
            compile_if(&mut env, list!(v_str!("str")).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );
    }

    #[test]
    fn test_compile_and_evaluate_quote() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;

        let mut comp = compile_quote(&mut env, list!(v_str!("str")).convert()).unwrap();
        assert_eq!(comp.result.evaluate(&mut env).unwrap(), v_str!("str"));
        assert_eq!(comp.types, BTreeSet::from_iter(vec![ValueType::String]));

        let mut comp = compile_quote(&mut env, list!(v_qsym!("std", "if")).convert()).unwrap();
        assert_eq!(
            comp.result.evaluate(&mut env).unwrap(),
            v_qsym!("std", "if")
        );
        assert_eq!(
            comp.types,
            BTreeSet::from_iter(vec![ValueType::QualifiedSymbol])
        );

        let mut comp = compile_quote(
            &mut env,
            list!(v_list!(v_qsym!("std", "if"), v_bool!(true))).convert(),
        )
        .unwrap();
        assert_eq!(
            comp.result.evaluate(&mut env).unwrap(),
            v_list!(v_qsym!("std", "if"), v_bool!(true))
        );
        assert_eq!(
            comp.types,
            BTreeSet::from_iter(vec![ValueType::List(BTreeSet::from_iter(vec![
                ValueType::QualifiedSymbol,
                ValueType::Bool,
            ]),)])
        );

        assert_eq!(
            compile_quote(&mut env, list!().convert()).unwrap_err().kind,
            ErrorKind::IncorrectParams
        );

        assert_eq!(
            compile_quote(&mut env, list!(v_list!(), v_list!()).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectParams
        );
    }
}
