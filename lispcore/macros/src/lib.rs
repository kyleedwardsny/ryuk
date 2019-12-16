extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span as Span2;
use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use std::env::var;
use syn::{parse_quote, punctuated::Punctuated, Ident, ItemTrait, TypeParamBound};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn get_cast_to_trait() -> Result<Ident> {
    let strval = var("RYUK_CAST_TO_TRAIT")?;
    Result::Ok(Ident::new(&strval, Span2::call_site()))
}

fn get_value_cast_traits() -> Result<Vec<Ident>> {
    let strval = var("RYUK_VALUE_CAST_TRAITS")?;
    let mut traits = Vec::<Ident>::new();

    for t in strval.split(',') {
        traits.push(Ident::new(t, Span2::call_site()));
    }

    Result::Ok(traits)
}

#[proc_macro_attribute]
pub fn cast_to_trait(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // No-op
    item
}

fn value_trait_impl(item: TokenStream) -> Result<TokenStream> {
    let cast_to_trait = get_cast_to_trait()?;
    let mut value_trait: ItemTrait = syn::parse(item)?;

    value_trait.supertraits = Punctuated::new();
    for t in get_value_cast_traits()? {
        let trait_type: TypeParamBound =
            TypeParamBound::Trait(parse_quote!(#cast_to_trait<dyn #t>));
        let mut tokens = TokenStream2::new();
        trait_type.to_tokens(&mut tokens);
        value_trait.supertraits.push(trait_type);
    }

    let mut tokens = TokenStream2::new();
    value_trait.to_tokens(&mut tokens);
    Result::Ok(TokenStream::from(tokens))
}

#[proc_macro_attribute]
pub fn value_trait(_attr: TokenStream, item: TokenStream) -> TokenStream {
    value_trait_impl(item).expect("Error updating value trait")
}

#[proc_macro_attribute]
pub fn value_cast_trait(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // No-op
    item
}
