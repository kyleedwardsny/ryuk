use ryuk_lispcore::env::*;
use ryuk_lispcore::error::*;
use ryuk_lispcore::value::*;
use ryuk_lispcore::*;
use std::collections::BTreeSet;

#[derive(Debug)]
struct IfEvaluator<C, D>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    test: Box<dyn Evaluator<C, D>>,
    then: Box<dyn Evaluator<C, D>>,
    els: Box<dyn Evaluator<C, D>>,
}

impl<C, D> IfEvaluator<C, D>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    pub fn new(
        test: Box<dyn Evaluator<C, D>>,
        then: Box<dyn Evaluator<C, D>>,
        els: Box<dyn Evaluator<C, D>>,
    ) -> Self {
        Self { test, then, els }
    }
}

impl<C, D> Evaluator<C, D> for IfEvaluator<C, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    fn evaluate(&mut self, env: &mut dyn Environment<C, D>) -> Result<Value<D>, D> {
        use std::convert::TryInto;

        let b: ValueBool = self.test.evaluate(env)?.try_into().unwrap();
        if b.0 {
            self.then.evaluate(env)
        } else {
            self.els.evaluate(env)
        }
    }
}

pub fn compile_if<C, D>(
    env: &mut dyn Environment<C, D>,
    mut params: ValueList<C>,
) -> Result<CompilationResult<C, D>, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    use std::iter::FromIterator;

    let mut return_type;

    let test;
    match params.next() {
        Option::Some(test_item) => {
            let test_comp = env.compile(test_item)?;
            if test_comp.return_type
                != ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::Bool)))
            {
                return Result::Err(e_type_error!(D));
            }
            test = test_comp.result;
        }
        _ => {
            return Result::Err(e_program_error!(D));
        }
    }

    let then;
    match params.next() {
        Option::Some(then_item) => {
            let then_comp = env.compile(then_item)?;
            return_type = then_comp.return_type;
            then = then_comp.result;
        }
        _ => {
            return Result::Err(e_program_error!(D));
        }
    }

    let els;
    match params.next() {
        Option::Some(els_item) => {
            let mut els_comp = env.compile(els_item)?;
            return_type.append(&mut els_comp.return_type);
            els = els_comp.result;
        }
        Option::None => {
            return_type.append(&mut ValueType::Some(BTreeSet::from_iter(std::iter::once(
                ValueTypeSome::List(ValueType::Some(BTreeSet::new())),
            ))));
            els = Box::new(LiteralEvaluator::new(Value::<ValueTypesStatic>::List(
                ValueList(Option::None),
            )));
        }
    }

    match params.next() {
        Option::Some(_) => {
            return Result::Err(e_program_error!(D));
        }
        _ => (),
    }

    Result::Ok(CompilationResult {
        result: Box::new(IfEvaluator::new(test, then, els)),
        return_type,
    })
}

pub fn compile_quote<C, D>(
    _env: &mut dyn Environment<C, D>,
    mut params: ValueList<C>,
) -> Result<CompilationResult<C, D>, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    use std::iter::FromIterator;

    let result;
    match params.next() {
        Option::Some(val) => result = val,
        _ => {
            return Result::Err(e_program_error!(D));
        }
    }

    match params.next() {
        Option::Some(_) => {
            return Result::Err(e_program_error!(D));
        }
        _ => (),
    }

    let return_type = ValueType::Some(BTreeSet::from_iter(std::iter::once(result.value_type())));
    Result::Ok(CompilationResult {
        result: Box::new(LiteralEvaluator::new(result)),
        return_type,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    struct SimpleEnvironment;

    impl<C, D> Environment<C, D> for SimpleEnvironment
    where
        C: ValueTypes + ?Sized + 'static,
        D: ValueTypesMut + ?Sized + 'static,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        fn as_dyn_mut(&mut self) -> &mut (dyn Environment<C, D> + 'static) {
            self as &mut (dyn Environment<C, D> + 'static)
        }

        fn resolve_symbol_get_variable(
            &self,
            _name: &ValueUnqualifiedSymbol<C::StringTypes>,
        ) -> Option<ValueQualifiedSymbol<C::StringTypes>> {
            Option::None
        }

        fn compile_variable(
            &self,
            _name: &ValueQualifiedSymbol<C::StringTypes>,
        ) -> Option<ValueType> {
            Option::None
        }

        fn evaluate_variable(
            &self,
            _name: &ValueQualifiedSymbol<C::StringTypes>,
        ) -> Result<Value<D>, D> {
            Result::Err(e_unbound_variable!(D))
        }

        fn evaluate_function(
            &mut self,
            _name: &ValueQualifiedSymbol<C::StringTypes>,
            _params: Vec<Value<D>>,
        ) -> Result<Value<D>, D> {
            Result::Err(e_undefined_function!(D))
        }

        fn resolve_symbol_get_macro(
            &self,
            _name: &ValueUnqualifiedSymbol<C::StringTypes>,
        ) -> Option<ValueQualifiedSymbol<C::StringTypes>> {
            Option::None
        }

        fn compile_macro(
            &mut self,
            name: &ValueQualifiedSymbol<C::StringTypes>,
            params: ValueList<C>,
        ) -> Option<Result<TryCompilationResult<C, D>, D>> {
            match (
                C::StringTypes::string_ref_to_str(&name.package),
                C::StringTypes::string_ref_to_str(&name.name),
            ) {
                ("std", "if") => Option::Some(match compile_if(self, params) {
                    Result::Ok(r) => Result::Ok(TryCompilationResult::Compiled(r)),
                    Result::Err(e) => Result::Err(e),
                }),
                _ => Option::None,
            }
        }

        fn compile_function(
            &self,
            _name: &ValueQualifiedSymbol<C::StringTypes>,
            _params: &mut dyn Iterator<Item = &ValueType>,
        ) -> Option<Result<ValueType, D>> {
            Option::None
        }
    }

    #[test]
    fn test_evaluate_if() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_bool!(true))),
            Box::new(LiteralEvaluator::new(v_str!("yes"))),
            Box::new(LiteralEvaluator::new(v_str!("no"))),
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_str!("yes"));

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_bool!(false))),
            Box::new(LiteralEvaluator::new(v_str!("yes"))),
            Box::new(LiteralEvaluator::new(v_str!("no"))),
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_str!("no"));

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_bool!(true))),
            Box::new(LiteralEvaluator::new(v_str!("yes"))),
            Box::new(LiteralEvaluator::new(v_list!())),
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_str!("yes"));

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_bool!(false))),
            Box::new(LiteralEvaluator::new(v_str!("yes"))),
            Box::new(LiteralEvaluator::new(v_list!())),
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_list!());
    }

    #[test]
    #[should_panic]
    fn test_evaluate_if_bad_test() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = IfEvaluator::new(
            Box::new(LiteralEvaluator::new(v_str!("true"))),
            Box::new(LiteralEvaluator::new(v_str!("yes"))),
            Box::new(LiteralEvaluator::new(v_list!())),
        );
        comp.evaluate(env).ok();
    }

    #[test]
    fn test_compile_and_evaluate_if() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = compile_if(env, list!(v_bool!(true), v_str!("yes"), v_str!("no"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_str!("yes"));
        assert_eq!(
            comp.return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::String)))
        );

        let mut comp = compile_if(env, list!(v_bool!(false), v_str!("yes"), v_str!("no"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_str!("no"));
        assert_eq!(
            comp.return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::String)))
        );

        let mut comp = compile_if(env, list!(v_bool!(true), v_str!("yes"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_str!("yes"));
        assert_eq!(
            comp.return_type,
            ValueType::Some(BTreeSet::from_iter(vec![
                ValueTypeSome::List(ValueType::Some(BTreeSet::new())),
                ValueTypeSome::String
            ]))
        );

        let mut comp = compile_if(env, list!(v_bool!(false), v_str!("yes"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_list!());
        assert_eq!(
            comp.return_type,
            ValueType::Some(BTreeSet::from_iter(vec![
                ValueTypeSome::List(ValueType::Some(BTreeSet::new())),
                ValueTypeSome::String
            ]))
        );

        assert_eq!(
            compile_if(env, list!()).unwrap_err(),
            e_program_error!(ValueTypesRc)
        );

        assert_eq!(
            compile_if(env, list!(v_bool!(true))).unwrap_err(),
            e_program_error!(ValueTypesRc)
        );

        assert_eq!(
            compile_if(env, list!(v_bool!(true), v_list!(), v_list!(), v_list!())).unwrap_err(),
            e_program_error!(ValueTypesRc)
        );

        assert_eq!(
            compile_if(env, list!(v_str!("str"))).unwrap_err(),
            e_type_error!(ValueTypesRc)
        );
    }

    #[test]
    fn test_compile_and_evaluate_quote() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = compile_quote(env, list!(v_str!("str"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_str!("str"));
        assert_eq!(
            comp.return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::String)))
        );

        let mut comp = compile_quote(env, list!(v_qsym!("std", "if"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_qsym!("std", "if"));
        assert_eq!(
            comp.return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(
                ValueTypeSome::QualifiedSymbol
            )))
        );

        let mut comp =
            compile_quote(env, list!(v_list!(v_qsym!("std", "if"), v_bool!(true)))).unwrap();
        assert_eq!(
            comp.result.evaluate(env).unwrap(),
            v_list!(v_qsym!("std", "if"), v_bool!(true))
        );
        assert_eq!(
            comp.return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::List(
                ValueType::Some(BTreeSet::from_iter(vec![
                    ValueTypeSome::QualifiedSymbol,
                    ValueTypeSome::Bool,
                ])),
            ))))
        );

        assert_eq!(
            compile_quote(env, list!()).unwrap_err(),
            e_program_error!(ValueTypesRc)
        );

        assert_eq!(
            compile_quote(env, list!(v_list!(), v_list!())).unwrap_err(),
            e_program_error!(ValueTypesRc)
        );
    }
}
