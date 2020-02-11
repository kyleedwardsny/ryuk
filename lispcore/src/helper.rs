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

            pub fn consume_parameters(
                &self,
                $env: &mut dyn Environment,
                $params: &mut ValueList
            ) -> Result<($($t::ParameterType,)*)>
            where
                $($t: MacroParameterConsumer),*
            {
                let result = ($((self.0).$i.consume_parameter($env, $params)?,)*);
                $params.next().map_or_else(|| Result::Ok(result), |_| Result::Err(e_program_error!()))
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

pub trait MacroParameterConsumer {
    type ParameterType;

    fn consume_parameter(
        &self,
        env: &mut dyn Environment,
        params: &mut ValueList,
    ) -> Result<Self::ParameterType>;
}

pub struct LiteralMacroParameterConsumer<T>(PhantomData<T>);

impl<T> LiteralMacroParameterConsumer<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<T> MacroParameterConsumer for LiteralMacroParameterConsumer<T>
where
    Value: TryInto<T>,
{
    type ParameterType = T;

    fn consume_parameter(
        &self,
        env: &mut dyn Environment,
        params: &mut ValueList,
    ) -> Result<Self::ParameterType> {
        OptionalLiteralMacroParameterConsumer::<T>::new()
            .consume_parameter(env, params)
            .transpose()
            .ok_or(e_program_error!())?
    }
}

pub struct OptionalLiteralMacroParameterConsumer<T>(PhantomData<T>);

impl<T> OptionalLiteralMacroParameterConsumer<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<T> MacroParameterConsumer for OptionalLiteralMacroParameterConsumer<T>
where
    Value: TryInto<T>,
{
    type ParameterType = Option<T>;

    fn consume_parameter(
        &self,
        _env: &mut dyn Environment,
        params: &mut ValueList,
    ) -> Result<Self::ParameterType> {
        params
            .next()
            .map(|p| p.try_into())
            .transpose()
            .map_err(|_| e_type_error!())
    }
}

pub struct CompiledMacroParameterConsumer(OptionalCompiledMacroParameterConsumer);

impl CompiledMacroParameterConsumer {
    pub fn new(expected_type: ValueType) -> Self {
        Self(OptionalCompiledMacroParameterConsumer::new(expected_type))
    }
}

impl MacroParameterConsumer for CompiledMacroParameterConsumer {
    type ParameterType = CompilationResult;

    fn consume_parameter(
        &self,
        env: &mut dyn Environment,
        params: &mut ValueList,
    ) -> Result<Self::ParameterType> {
        self.0
            .consume_parameter(env, params)
            .transpose()
            .ok_or(e_program_error!())?
    }
}

pub struct OptionalCompiledMacroParameterConsumer(ValueType);

impl OptionalCompiledMacroParameterConsumer {
    pub fn new(expected_type: ValueType) -> Self {
        Self(expected_type)
    }
}

impl MacroParameterConsumer for OptionalCompiledMacroParameterConsumer {
    type ParameterType = Option<CompilationResult>;

    fn consume_parameter(
        &self,
        env: &mut dyn Environment,
        params: &mut ValueList,
    ) -> Result<Self::ParameterType> {
        params
            .next()
            .map(|p| {
                let comp = env.compile(p)?;
                if self.0.contains(&comp.return_type) {
                    Result::Ok(comp)
                } else {
                    Result::Err(e_type_error!())
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
            _name: &ValueQualifiedSymbol,
            _params: ValueList,
        ) -> Option<Result<TryCompilationResult>> {
            Option::None
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
    fn test_macro_parameter_helper() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment;

        let helper = MacroParameterHelper::new()
            .literal::<ValueString>()
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
            e_program_error!()
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
            e_type_error!()
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
            e_type_error!()
        );

        assert_eq!(
            helper
                .consume_parameters(
                    env,
                    &mut list!(v_str!("str1"), v_bool!(true), v_str!("str2"))
                )
                .unwrap_err(),
            e_type_error!()
        );
    }

    #[test]
    fn test_literal_macro_parameter_consumer() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment;

        let con = LiteralMacroParameterConsumer::<ValueString>::new();
        let mut l = list!(v_str!("str"), v_bool!(true));

        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap(),
            str!("str")
        );
        assert_eq!(l, list!(v_bool!(true)));
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap_err(),
            e_type_error!()
        );
        assert_eq!(l, list!());
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap_err(),
            e_program_error!()
        );
        assert_eq!(l, list!());
    }

    #[test]
    fn test_optional_literal_macro_parameter_consumer() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment;

        let con = OptionalLiteralMacroParameterConsumer::<ValueString>::new();
        let mut l = list!(v_str!("str"), v_bool!(true));

        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap(),
            Option::Some(str!("str"))
        );
        assert_eq!(l, list!(v_bool!(true)));
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap_err(),
            e_type_error!()
        );
        assert_eq!(l, list!());
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap(),
            Option::None
        );
        assert_eq!(l, list!());
    }

    #[test]
    fn test_compiled_macro_parameter_consumer() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment;

        let con = CompiledMacroParameterConsumer::new(ValueType::Some(BTreeSet::from_iter(vec![
            ValueTypeSome::String,
            ValueTypeSome::Bool,
        ])));
        let mut l = list!(v_str!("str"), v_bool!(true), v_list!());

        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l)
                .unwrap()
                .return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::String)))
        );
        assert_eq!(l, list!(v_bool!(true), v_list!()));
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l)
                .unwrap()
                .return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::Bool)))
        );
        assert_eq!(l, list!(v_list!()));
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap_err(),
            e_type_error!()
        );
        assert_eq!(l, list!());
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap_err(),
            e_program_error!()
        );
        assert_eq!(l, list!());
    }

    #[test]
    fn test_optional_compiled_macro_parameter_consumer() {
        use std::iter::FromIterator;

        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment;

        let con = OptionalCompiledMacroParameterConsumer::new(ValueType::Some(
            BTreeSet::from_iter(vec![ValueTypeSome::String, ValueTypeSome::Bool]),
        ));
        let mut l = list!(v_str!("str"), v_bool!(true), v_list!());

        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l)
                .unwrap()
                .unwrap()
                .return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::String)))
        );
        assert_eq!(l, list!(v_bool!(true), v_list!()));
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l)
                .unwrap()
                .unwrap()
                .return_type,
            ValueType::Some(BTreeSet::from_iter(std::iter::once(ValueTypeSome::Bool)))
        );
        assert_eq!(l, list!(v_list!()));
        assert_eq!(
            MacroParameterConsumer::consume_parameter(&con, env, &mut l).unwrap_err(),
            e_type_error!()
        );
        assert_eq!(l, list!());
        assert!(MacroParameterConsumer::consume_parameter(&con, env, &mut l)
            .unwrap()
            .is_none());
        assert_eq!(l, list!());
    }
}
