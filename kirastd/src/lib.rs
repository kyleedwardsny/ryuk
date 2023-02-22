use ryuk_lispcore::env::*;
use ryuk_lispcore::error::*;
use ryuk_lispcore::helper::*;
use ryuk_lispcore::value::*;
use std::collections::BTreeSet;

#[derive(Debug)]
struct IfEvaluator {
    test: Box<dyn Evaluator>,
    then: Box<dyn Evaluator>,
    els: Box<dyn Evaluator>,
}

impl IfEvaluator {
    pub fn new(
        test: Box<dyn Evaluator>,
        then: Box<dyn Evaluator>,
        els: Box<dyn Evaluator>,
    ) -> Self {
        Self { test, then, els }
    }
}

impl Evaluator for IfEvaluator {
    fn evaluate(&mut self, env: &mut dyn Environment) -> Result<Value> {
        let b: ValueBool = self.test.evaluate(env)?.try_into().unwrap();
        if b.0 {
            self.then.evaluate(env)
        } else {
            self.els.evaluate(env)
        }
    }
}

pub fn compile_if(env: &mut dyn Environment, mut params: ValueList) -> Result<CompilationResult> {
    let helper = MacroParameterHelper::new()
        .compiled(ValueType::from(ValueTypeSome::Bool))
        .compiled(ValueType::Any)
        .optional_compiled(ValueType::Any);

    let (test, then, els) = helper.consume_parameters(env, &mut params)?;
    let mut els = els.unwrap_or_else(|| CompilationResult {
        result: Box::new(LiteralEvaluator::new(Value::List(ValueList(Option::None)))),
        return_type: ValueType::from(ValueTypeSome::List(ValueType::Some(BTreeSet::new()))),
    });

    let mut return_type = then.return_type;
    return_type.append(&mut els.return_type);

    Result::Ok(CompilationResult {
        result: Box::new(IfEvaluator::new(test.result, then.result, els.result)),
        return_type,
    })
}

pub fn compile_quote(
    env: &mut dyn Environment,
    mut params: ValueList,
) -> Result<CompilationResult> {
    let helper = MacroParameterHelper::new().literal::<Value>();

    let (literal,) = helper.consume_parameters(env, &mut params)?;
    let return_type = ValueType::from(literal.value_type());

    Result::Ok(CompilationResult {
        result: Box::new(LiteralEvaluator::new(literal)),
        return_type,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ryuk_lispcore::*;

    struct SimpleEnvironment;

    impl Environment for SimpleEnvironment {
        fn as_dyn_mut(&mut self) -> &mut (dyn Environment + 'static) {
            self as &mut (dyn Environment + 'static)
        }

        fn resolve_symbol_get_variable(
            &self,
            _name: &ValueUnqualifiedSymbol,
        ) -> Option<ValueQualifiedSymbol> {
            Option::None
        }

        fn compile_variable(&self, _name: &ValueQualifiedSymbol) -> Option<ValueType> {
            Option::None
        }

        fn evaluate_variable(&self, _name: &ValueQualifiedSymbol) -> Result<Value> {
            Result::Err(e_unbound_variable!())
        }

        fn evaluate_function(
            &mut self,
            _name: &ValueQualifiedSymbol,
            _params: Vec<Value>,
        ) -> Result<Value> {
            Result::Err(e_undefined_function!())
        }

        fn resolve_symbol_get_macro(
            &self,
            _name: &ValueUnqualifiedSymbol,
        ) -> Option<ValueQualifiedSymbol> {
            Option::None
        }

        fn compile_macro(
            &mut self,
            name: &ValueQualifiedSymbol,
            params: ValueList,
        ) -> Option<Result<TryCompilationResult>> {
            match (&*name.package, &*name.name) {
                ("std", "if") => Option::Some(match compile_if(self, params) {
                    Result::Ok(r) => Result::Ok(TryCompilationResult::Compiled(r)),
                    Result::Err(e) => Result::Err(e),
                }),
                _ => Option::None,
            }
        }

        fn compile_function(
            &self,
            _name: &ValueQualifiedSymbol,
            _params: &mut dyn Iterator<Item = &ValueType>,
        ) -> Option<Result<ValueType>> {
            Option::None
        }
    }

    #[test]
    fn test_evaluate_if() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment;

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
        let env = &mut env as &mut dyn Environment;

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
        let env = &mut env as &mut dyn Environment;

        let mut comp = compile_if(env, list!(v_bool!(true), v_str!("yes"), v_str!("no"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_str!("yes"));
        assert_eq!(comp.return_type, ValueType::from(ValueTypeSome::String));

        let mut comp = compile_if(env, list!(v_bool!(false), v_str!("yes"), v_str!("no"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_str!("no"));
        assert_eq!(comp.return_type, ValueType::from(ValueTypeSome::String));

        let mut comp = compile_if(env, list!(v_bool!(true), v_str!("yes"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_str!("yes"));
        assert_eq!(
            comp.return_type,
            ValueType::from_iter(vec![
                ValueTypeSome::List(ValueType::Some(BTreeSet::new())),
                ValueTypeSome::String
            ])
        );

        let mut comp = compile_if(env, list!(v_bool!(false), v_str!("yes"))).unwrap();
        assert_eq!(comp.result.evaluate(env).unwrap(), v_list!());
        assert_eq!(
            comp.return_type,
            ValueType::from_iter(vec![
                ValueTypeSome::List(ValueType::Some(BTreeSet::new())),
                ValueTypeSome::String
            ])
        );

        assert_eq!(compile_if(env, list!()).unwrap_err(), e_program_error!());

        assert_eq!(
            compile_if(env, list!(v_bool!(true))).unwrap_err(),
            e_program_error!()
        );

        assert_eq!(
            compile_if(env, list!(v_bool!(true), v_list!(), v_list!(), v_list!())).unwrap_err(),
            e_program_error!()
        );

        assert_eq!(
            compile_if(env, list!(v_str!("str"))).unwrap_err(),
            e_type_error!()
        );
    }

    #[test]
    fn test_compile_and_evaluate_quote() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment;

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

        assert_eq!(compile_quote(env, list!()).unwrap_err(), e_program_error!());

        assert_eq!(
            compile_quote(env, list!(v_list!(), v_list!())).unwrap_err(),
            e_program_error!()
        );
    }
}
