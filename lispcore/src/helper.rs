use crate::env::*;
use crate::error::*;
use crate::value::*;
use std::convert::TryInto;
use std::marker::PhantomData;

pub struct MacroParameterHelper<T>(T);

impl MacroParameterHelper<()> {
    pub fn new() -> Self {
        Self(())
    }
}

macro_rules! impl_helper_impl {
    ($env:ident, $params:ident, $($i:tt: $t:ident),*) => {
        impl<$($t),*> MacroParameterHelper<($($t,)*)> {
            pub fn param<T>(self, next: T) -> MacroParameterHelper<($($t,)* T,)> {
                MacroParameterHelper(($((self.0).$i,)* next,))
            }

            pub fn literal<T>(self) -> MacroParameterHelper<($($t,)* LiteralMacroParameterConsumer<T>,)> {
                self.param(LiteralMacroParameterConsumer::new())
            }

            pub fn optional_literal<T>(self) -> MacroParameterHelper<($($t,)* OptionalLiteralMacroParameterConsumer<T>,)> {
                self.param(OptionalLiteralMacroParameterConsumer::new())
            }

            pub fn compiled(self, expected_type: ValueType) -> MacroParameterHelper<($($t,)* CompiledMacroParameterConsumer,)> {
                self.param(CompiledMacroParameterConsumer::new(expected_type))
            }

            pub fn optional_compiled(self, expected_type: ValueType) -> MacroParameterHelper<($($t,)* OptionalCompiledMacroParameterConsumer,)> {
                self.param(OptionalCompiledMacroParameterConsumer::new(expected_type))
            }

            pub fn consume_parameters<CT, DT>(
                &self,
                $env: &mut dyn Environment<CT, DT>,
                $params: &mut ValueList<CT>
            ) -> Result<($($t::ParameterType,)*), DT>
            where
                CT: ValueTypes + ?Sized,
                DT: ValueTypesMut + ?Sized,
                DT::StringTypes: StringTypesMut,
                DT::SemverTypes: SemverTypesMut,
                $($t: MacroParameterConsumer<CT, DT>),*
            {
                let result = ($((self.0).$i.consume_parameter($env, $params)?,)*);
                $params.next().map_or_else(|| Result::Ok(result), |_| Result::Err(e_program_error!(DT)))
            }
        }
    };
}

macro_rules! impl_helper {
    () => {
        impl_helper_impl!(_env, _params,);
    };
    ($($i:tt: $t:ident),*) => {
        impl_helper_impl!(env, params, $($i: $t),*);
    };
}

impl_helper!();
impl_helper!(0: A);
impl_helper!(0: A, 1: B);
impl_helper!(0: A, 1: B, 2: C);
impl_helper!(0: A, 1: B, 2: C, 3: D);
impl_helper!(0: A, 1: B, 2: C, 3: D, 4: E);
impl_helper!(0: A, 1: B, 2: C, 3: D, 4: E, 5: F);
impl_helper!(0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G);
impl_helper!(0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H);
impl_helper!(0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I);
impl_helper!(0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J);
impl_helper!(
    0: A,
    1: B,
    2: C,
    3: D,
    4: E,
    5: F,
    6: G,
    7: H,
    8: I,
    9: J,
    10: K
);
impl_helper!(
    0: A,
    1: B,
    2: C,
    3: D,
    4: E,
    5: F,
    6: G,
    7: H,
    8: I,
    9: J,
    10: K,
    11: L
);

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
        env: &mut dyn Environment<C, D>,
        params: &mut ValueList<C>,
    ) -> Result<Self::ParameterType, D> {
        OptionalLiteralMacroParameterConsumer::<T>::new()
            .consume_parameter(env, params)
            .transpose()
            .ok_or(e_program_error!(D))?
    }
}

pub struct OptionalLiteralMacroParameterConsumer<T>(PhantomData<T>);

impl<T> OptionalLiteralMacroParameterConsumer<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<C, D, T> MacroParameterConsumer<C, D> for OptionalLiteralMacroParameterConsumer<T>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
    Value<C>: TryInto<T>,
{
    type ParameterType = Option<T>;

    fn consume_parameter(
        &self,
        _env: &mut dyn Environment<C, D>,
        params: &mut ValueList<C>,
    ) -> Result<Self::ParameterType, D> {
        params
            .next()
            .map(|p| p.try_into())
            .transpose()
            .map_err(|_| e_type_error!(D))
    }
}

pub struct CompiledMacroParameterConsumer(OptionalCompiledMacroParameterConsumer);

impl CompiledMacroParameterConsumer {
    pub fn new(expected_type: ValueType) -> Self {
        Self(OptionalCompiledMacroParameterConsumer::new(expected_type))
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
        self.0
            .consume_parameter(env, params)
            .transpose()
            .ok_or(e_program_error!(D))?
    }
}

pub struct OptionalCompiledMacroParameterConsumer(ValueType);

impl OptionalCompiledMacroParameterConsumer {
    pub fn new(expected_type: ValueType) -> Self {
        Self(expected_type)
    }
}

impl<C, D> MacroParameterConsumer<C, D> for OptionalCompiledMacroParameterConsumer
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    type ParameterType = Option<CompilationResult<C, D>>;

    fn consume_parameter(
        &self,
        env: &mut dyn Environment<C, D>,
        params: &mut ValueList<C>,
    ) -> Result<Self::ParameterType, D> {
        params
            .next()
            .map(|p| {
                let comp = env.compile(p)?;
                if self.0.contains(&comp.return_type) {
                    Result::Ok(comp)
                } else {
                    Result::Err(e_type_error!(D))
                }
            })
            .transpose()
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
    fn test_macro_parameter_helper() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let helper = MacroParameterHelper::new()
            .literal::<ValueString<StringTypesStatic>>()
            .compiled(ValueType::Some(BTreeSet::from_iter(vec![
                ValueTypeSome::Bool,
                ValueTypeSome::UnqualifiedSymbol,
            ])))
            .optional_literal::<ValueBool>()
            .optional_compiled(ValueType::Some(BTreeSet::from_iter(std::iter::once(
                ValueTypeSome::String,
            ))));

        let (s1, b1, b2, s2) = helper
            .consume_parameters(
                env,
                &mut list!(
                    v_str!("str1"),
                    v_bool!(true),
                    v_bool!(false),
                    v_str!("str2")
                ),
            )
            .unwrap();
        assert_eq!(s1, str!("str1"));
        assert_eq!(
            b1.return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::Bool)))
        );
        assert_eq!(b2.unwrap(), bool!(false));
        assert_eq!(
            s2.unwrap().return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::String)))
        );

        assert_eq!(
            helper
                .consume_parameters(
                    env,
                    &mut list!(
                        v_str!("str1"),
                        v_bool!(true),
                        v_bool!(false),
                        v_str!("str2"),
                        v_str!("str3")
                    )
                )
                .unwrap_err(),
            e_program_error!(ValueTypesRc)
        );

        let (s1, b1, b2, s2) = helper
            .consume_parameters(
                env,
                &mut list!(v_str!("str1"), v_bool!(true), v_bool!(false)),
            )
            .unwrap();
        assert_eq!(s1, str!("str1"));
        assert_eq!(
            b1.return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::Bool)))
        );
        assert_eq!(b2.unwrap(), bool!(false));
        assert!(s2.is_none());

        let (s1, b1, b2, s2) = helper
            .consume_parameters(env, &mut list!(v_str!("str1"), v_bool!(true)))
            .unwrap();
        assert_eq!(s1, str!("str1"));
        assert_eq!(
            b1.return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::Bool)))
        );
        assert!(b2.is_none());
        assert!(s2.is_none());

        assert_eq!(
            helper
                .consume_parameters(
                    env,
                    &mut list!(v_str!("str1"), v_bool!(true), v_bool!(false), v_list!())
                )
                .unwrap_err(),
            e_type_error!(ValueTypesRc)
        );

        assert_eq!(
            helper
                .consume_parameters(
                    env,
                    &mut list!(
                        v_str!("str1"),
                        v_bool!(true),
                        v_str!("str2"),
                        v_str!("str3")
                    )
                )
                .unwrap_err(),
            e_type_error!(ValueTypesRc)
        );

        assert_eq!(
            helper
                .consume_parameters(
                    env,
                    &mut list!(v_str!("str1"), v_bool!(true), v_str!("str2"))
                )
                .unwrap_err(),
            e_type_error!(ValueTypesRc)
        );
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
    fn test_optional_literal_macro_parameter_consumer() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let con = OptionalLiteralMacroParameterConsumer::<ValueString<StringTypesStatic>>::new();
        let mut l = list!(v_str!("str"), v_bool!(true));

        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap(),
            Option::Some(str!("str"))
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
                .unwrap(),
            Option::None
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

    #[test]
    fn test_optional_compiled_macro_parameter_consumer() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let con = OptionalCompiledMacroParameterConsumer::new(ValueType::Some(
            BTreeSet::from_iter(vec![ValueTypeSome::String, ValueTypeSome::Bool]),
        ));
        let mut l = list!(v_str!("str"), v_bool!(true), v_list!());

        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap()
                .unwrap()
                .return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::String)))
        );
        assert_eq!(l, list!(v_bool!(true), v_list!()));
        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap()
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
        assert!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, env, &mut l)
                .unwrap()
                .is_none()
        );
        assert_eq!(l, list!());
    }
}
