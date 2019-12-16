extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span as Span2;
use proc_macro2::TokenStream as TokenStream2;
use quote::ToTokens;
use std::env::var;
use syn::{
    parse_quote, punctuated::Punctuated, Expr, Ident, ItemImpl, ItemStruct, ItemTrait,
    TypeParamBound,
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn get_cast_to_trait() -> Result<Ident> {
    let strval = var("RYUK_CAST_TO_TRAIT")?;
    Result::Ok(Ident::new(&strval, Span2::call_site()))
}

fn get_cast_to_fn() -> Result<Ident> {
    let strval = var("RYUK_CAST_TO_FN")?;
    Result::Ok(Ident::new(&strval, Span2::call_site()))
}

fn get_value_trait() -> Result<Ident> {
    let strval = var("RYUK_VALUE_TRAIT")?;
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

#[proc_macro_attribute]
pub fn cast_to_fn(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // No-op
    item
}

fn value_trait_impl(item: TokenStream) -> Result<TokenStream> {
    let cast_to_trait = get_cast_to_trait()?;
    let mut value_trait: ItemTrait = syn::parse(item)?;

    value_trait.supertraits = Punctuated::new();
    for t in get_value_cast_traits()? {
        let trait_type = TypeParamBound::Trait(parse_quote!(#cast_to_trait<dyn #t>));
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

fn value_type_impl(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let cast_to_trait = get_cast_to_trait()?;
    let cast_to_fn = get_cast_to_fn()?;
    let value_trait = get_value_trait()?;
    let struct_def: ItemStruct = syn::parse(item)?;
    let struct_name = &struct_def.ident;
    let value_type: Ident = syn::parse(attr)?;

    let mut tokens = TokenStream2::new();
    struct_def.to_tokens(&mut tokens);

    let value_impl: ItemImpl = parse_quote! {
        impl #value_trait for #struct_name { }
    };
    value_impl.to_tokens(&mut tokens);

    for t in get_value_cast_traits()? {
        let result: Expr = if t == value_type {
            parse_quote!(Option::Some(self))
        } else {
            parse_quote!(Option::None)
        };
        let cast_to_impl: ItemImpl = parse_quote! {
            impl #cast_to_trait<#t> for #struct_name {
                fn #cast_to_fn(&self) -> Option<&(dyn #t + 'static)> { #result }
            }
        };
        cast_to_impl.to_tokens(&mut tokens);
    }

    Result::Ok(TokenStream::from(tokens))
}

#[proc_macro_attribute]
pub fn value_type(attr: TokenStream, item: TokenStream) -> TokenStream {
    value_type_impl(attr, item).expect("Error updating value type")
}
