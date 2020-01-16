use ryuk_lispcore::*;
use std::collections::BTreeSet;

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

pub fn compile_if<T>(
    env: &mut dyn Environment<T>,
    mut v: LispList<T>,
) -> Result<CompilationResult<T>>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    use std::iter::FromIterator;

    let mut types = BTreeSet::new();

    let test;
    match v.next() {
        Option::Some(LispListItem::Item(test_item)) => {
            let test_comp = env.compile(test_item)?;
            if test_comp.types
                != BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::Bool)])
            {
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
    match v.next() {
        Option::Some(LispListItem::Item(then_item)) => {
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
    match v.next() {
        Option::Some(LispListItem::Item(els_item)) => {
            let els_comp = env.compile(els_item)?;
            types.append(&mut els_comp.types.clone());
            els = Option::Some(els_comp.result);
        }
        Option::None => {
            types.insert(ValueType::NonList(ValueTypeNonList::Nil));
            els = Option::None;
        }
        _ => {
            return Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            ))
        }
    }

    match v.next() {
        Option::Some(_) => {
            return Result::Err(Error::new(
                ErrorKind::IncorrectParams,
                "Incorrect parameters",
            ))
        }
        _ => (),
    }

    Result::Ok(CompilationResult {
        result: Box::new(If::new(test, then, els)),
        types,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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
            name: &ValueQualifiedSymbol<String>,
            v: LispList<ValueTypesRc>,
        ) -> Option<Result<TryCompilationResult<ValueTypesRc>>> {
            use std::borrow::Borrow;

            match (name.package.borrow(), name.name.borrow()) {
                ("std", "if") => Option::Some(match compile_if(self, v) {
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

    fn test_compile_and_evaluate(
        env: &mut SimpleEnvironment,
        code: Value<ValueTypesStatic>,
        result: Value<ValueTypesStatic>,
        types: BTreeSet<ValueType>,
    ) {
        use super::*;

        let mut comp = env.compile(code.convert()).unwrap();
        assert_eq!(comp.types, types);
        assert_eq!(comp.result.evaluate(env).unwrap(), result);
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

    #[test]
    fn test_compile_and_evaluate_if() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;

        test_compile_and_evaluate(
            &mut env,
            v_list!(
                v_qsym!("std", "if"),
                v_bool!(true),
                v_str!("yes"),
                v_str!("no")
            ),
            v_str!("yes"),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::String)]),
        );

        test_compile_and_evaluate(
            &mut env,
            v_list!(
                v_qsym!("std", "if"),
                v_bool!(false),
                v_str!("yes"),
                v_str!("no")
            ),
            v_str!("no"),
            BTreeSet::from_iter(vec![ValueType::NonList(ValueTypeNonList::String)]),
        );

        test_compile_and_evaluate(
            &mut env,
            v_list!(v_qsym!("std", "if"), v_bool!(true), v_str!("yes")),
            v_str!("yes"),
            BTreeSet::from_iter(vec![
                ValueType::NonList(ValueTypeNonList::Nil),
                ValueType::NonList(ValueTypeNonList::String),
            ]),
        );

        test_compile_and_evaluate(
            &mut env,
            v_list!(v_qsym!("std", "if"), v_bool!(false), v_str!("yes")),
            v_nil!(),
            BTreeSet::from_iter(vec![
                ValueType::NonList(ValueTypeNonList::Nil),
                ValueType::NonList(ValueTypeNonList::String),
            ]),
        );

        assert_eq!(
            env.compile(v_list!(v_qsym!("std", "if")).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectParams
        );
        assert_eq!(
            env.compile(v_list!(v_qsym!("std", "if"), v_bool!(true)).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectParams
        );
        assert_eq!(
            env.compile(
                v_list!(
                    v_qsym!("std", "if"),
                    v_bool!(true),
                    v_nil!(),
                    v_nil!(),
                    v_nil!()
                )
                .convert()
            )
            .unwrap_err()
            .kind,
            ErrorKind::IncorrectParams
        );
        assert_eq!(
            env.compile(v_list!(v_qsym!("std", "if"), v_str!("str")).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectType
        );
        assert_eq!(
            env.compile(v_cons!(v_qsym!("std", "if"), v_cons!(v_bool!(true), v_nil!())).convert())
                .unwrap_err()
                .kind,
            ErrorKind::IncorrectParams
        );
        assert_eq!(
            env.compile(
                v_cons!(
                    v_qsym!("std", "if"),
                    v_cons!(v_bool!(true), v_cons!(v_nil!(), v_str!("str")))
                )
                .convert()
            )
            .unwrap_err()
            .kind,
            ErrorKind::IncorrectParams
        );
    }
}
