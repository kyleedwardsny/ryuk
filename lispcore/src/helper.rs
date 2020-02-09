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

    fn consume_parameter(&self, params: &mut ValueList<C>) -> Result<Self::ParameterType, D>;
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

    fn consume_parameter(&self, params: &mut ValueList<C>) -> Result<Self::ParameterType, D> {
        if let Option::Some(param) = params.next() {
            param.try_into().map_err(|_| e_type_error!(D))
        } else {
            Result::Err(e_program_error!(D))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_macro_parameter_consumer() {
        let con = LiteralMacroParameterConsumer::<ValueString<StringTypesStatic>>::new();

        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(
                &con,
                &mut list!(v_str!("str"))
            )
            .unwrap(),
            str!("str")
        );
        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(
                &con,
                &mut list!(v_bool!(true))
            )
            .unwrap_err(),
            e_type_error!(ValueTypesRc)
        );
        assert_eq!(
            MacroParameterConsumer::<_, ValueTypesRc>::consume_parameter(&con, &mut list!())
                .unwrap_err(),
            e_program_error!(ValueTypesRc)
        );
    }
}
