use ryuk_lispcore::*;

#[derive(Debug)]
struct If<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    test: Box<dyn CompilationResultType<T>>,
    then: Box<dyn CompilationResultType<T>>,
    els: Option<Box<dyn CompilationResultType<T>>>,
}

impl<T> If<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn new(
        test: Box<dyn CompilationResultType<T>>,
        then: Box<dyn CompilationResultType<T>>,
        els: Option<Box<dyn CompilationResultType<T>>>,
    ) -> Self {
        If { test, then, els }
    }
}

impl<T> CompilationResultType<T> for If<T>
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
            (&mut self.els)
                .as_mut()
                .map_or_else(|| Result::Ok(Value::Nil), |comp| comp.evaluate(env))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    struct SimpleEnvironment;

    impl Environment<ValueTypesRc> for SimpleEnvironment {
        fn as_dyn_mut(&mut self) -> &mut (dyn Environment<ValueTypesRc> + 'static) {
            self as &mut (dyn Environment<ValueTypesRc> + 'static)
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
            _name: &ValueQualifiedSymbol<String>,
            _v: LispList<ValueTypesRc>,
        ) -> Option<Result<TryCompilationResult<ValueTypesRc>>> {
            Option::None
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

        let mut comp = If::new(
            Box::new(Literal::new(v_bool!(true).convert())),
            Box::new(Literal::new(v_str!("yes").convert())),
            Option::Some(Box::new(Literal::new(v_str!("no").convert()))),
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("yes"));

        let mut comp = If::new(
            Box::new(Literal::new(v_bool!(false).convert())),
            Box::new(Literal::new(v_str!("yes").convert())),
            Option::Some(Box::new(Literal::new(v_str!("no").convert()))),
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("no"));

        let mut comp = If::new(
            Box::new(Literal::new(v_bool!(true).convert())),
            Box::new(Literal::new(v_str!("yes").convert())),
            Option::None,
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_str!("yes"));

        let mut comp = If::new(
            Box::new(Literal::new(v_bool!(false).convert())),
            Box::new(Literal::new(v_str!("yes").convert())),
            Option::None,
        );
        assert_eq!(comp.evaluate(&mut env).unwrap(), v_nil!());

        let mut comp = If::new(
            Box::new(Literal::new(v_str!("true").convert())),
            Box::new(Literal::new(v_str!("yes").convert())),
            Option::None,
        );
        assert_eq!(
            comp.evaluate(&mut env).unwrap_err().kind,
            ErrorKind::IncorrectType
        );
    }
}
