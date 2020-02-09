use crate::env::*;
use crate::error::*;
use crate::value::*;
use std::convert::TryInto;
use std::marker::PhantomData;

pub trait MacroParameterConsumer<C, D>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    type ParameterType;

    fn consume_parameter(
        &self,
        env: &mut dyn Environment<C, D>,
        params: &mut ValueList<C>,
    ) -> Result<Self::ParameterType, D>;
}

pub struct LiteralMacroParameterConsumer<T>(PhantomData<T>);

impl<T> LiteralMacroParameterConsumer<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<C, D, T> MacroParameterConsumer<C, D> for LiteralMacroParameterConsumer<T>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
    Value<C>: TryInto<T>,
{
    type ParameterType = T;

    fn consume_parameter(
        &self,
        _env: &mut dyn Environment<C, D>,
        params: &mut ValueList<C>,
    ) -> Result<Self::ParameterType, D> {
        params
            .next()
            .ok_or(e_program_error!(D))?
            .try_into()
            .map_err(|_| e_type_error!(D))
    }
}

pub struct CompiledMacroParameterConsumer(ValueType);

impl CompiledMacroParameterConsumer {
    pub fn new(expected_type: ValueType) -> Self {
        Self(expected_type)
    }
}

impl<C, D> MacroParameterConsumer<C, D> for CompiledMacroParameterConsumer
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    type ParameterType = CompilationResult<C, D>;

    fn consume_parameter(
        &self,
        env: &mut dyn Environment<C, D>,
        params: &mut ValueList<C>,
    ) -> Result<Self::ParameterType, D> {
        let comp = env.compile(params.next().ok_or(e_program_error!(D))?)?;
        if self.0.contains(&comp.return_type) {
            Result::Ok(comp)
        } else {
            Result::Err(e_type_error!(D))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

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
            _name: &ValueQualifiedSymbol<C::StringTypes>,
            _params: ValueList<C>,
        ) -> Option<Result<TryCompilationResult<C, D>, D>> {
            Option::None
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
    fn test_literal_macro_parameter_consumer() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let con = LiteralMacroParameterConsumer::<ValueString<StringTypesStatic>>::new();
        let mut l = list!(v_str!("str"), v_bool!(true));

        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap(),
            str!("str")
        );
        assert_eq!(l, list!(v_bool!(true)));
        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap_err(),
            e_type_error!(ValueTypesRc)
        );
        assert_eq!(l, list!());
        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap_err(),
            e_program_error!(ValueTypesRc)
        );
        assert_eq!(l, list!());
    }

    #[test]
    fn test_compiled_macro_parameter_consumer() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let con = CompiledMacroParameterConsumer::new(ValueType::Some(BTreeSet::from_iter(vec![
            ValueTypeSome::String,
            ValueTypeSome::Bool,
        ])));
        let mut l = list!(v_str!("str"), v_bool!(true), v_list!());

        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap()
                .return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::String)))
        );
        assert_eq!(l, list!(v_bool!(true), v_list!()));
        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap()
                .return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::Bool)))
        );
        assert_eq!(l, list!(v_list!()));
        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap_err(),
            e_type_error!(ValueTypesRc)
        );
        assert_eq!(l, list!());
        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap_err(),
            e_program_error!(ValueTypesRc)
        );
        assert_eq!(l, list!());
    }
}
