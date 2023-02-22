use crate::value::*;

use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse_quote, Ident, Path, PathArguments, PathSegment, Token};

fn crate_name(name: &str) -> &str {
    if std::env::var("CARGO_CRATE_NAME").expect("Error reading CARGO_CRATE_NAME") == name {
        "crate"
    } else {
        name
    }
}

fn fixup_crate(mut path: Path) -> Path {
    assert!(path.leading_colon.is_some());
    let ident = &path.segments.first().unwrap().ident;
    let name = ident.to_string();
    let span = ident.span();
    let new_name = crate_name(&name);
    *path.segments.first_mut().unwrap() = PathSegment {
        ident: Ident::new(new_name, span),
        arguments: PathArguments::None,
    };
    if new_name == "crate" {
        path.leading_colon = None;
    }
    path
}

macro_rules! parse_quote_fixup_crate {
    ($p:path) => {
        fixup_crate(parse_quote!($p))
    };
}

impl ToTokens for Value {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        match &*self {
            Value::List(list) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::List);
                let tokens = list.to_token_stream();
                quote!(#path(#tokens))
            }
            Value::UnqualifiedSymbol(sym) => {
                let path =
                    parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::UnqualifiedSymbol);
                let tokens = sym.to_token_stream();
                quote!(#path(#tokens))
            }
            Value::QualifiedSymbol(sym) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::QualifiedSymbol);
                let tokens = sym.to_token_stream();
                quote!(#path(#tokens))
            }
            Value::Bool(bool) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::Bool);
                let tokens = bool.to_token_stream();
                quote!(#path(#tokens))
            }
            Value::String(str) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::String);
                let tokens = str.to_token_stream();
                quote!(#path(#tokens))
            }
            Value::Semver(ver) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::Semver);
                let tokens = ver.to_token_stream();
                quote!(#path(#tokens))
            }
            Value::Function(_) => panic!("Function cannot be converted to tokens"),
            Value::Backquote(bq) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::Backquote);
                let tokens = bq.to_token_stream();
                quote!(#path(#tokens))
            }
            Value::Comma(comma) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::Comma);
                let tokens = comma.to_token_stream();
                quote!(#path(#tokens))
            }
            Value::Splice(splice) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value::Splice);
                let tokens = splice.to_token_stream();
                quote!(#path(#tokens))
            }
        }
        .to_tokens(out_tokens);
    }
}

impl ToTokens for ValueList {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueList);
        let tokens = match &self.0 {
            None => quote!(::std::option::Option::None),
            Some(cons) => {
                let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Cons);
                let tokens = cons.to_token_stream();
                quote!(::std::option::Option::<::std::rc::Rc::<#path>>::Some(::std::rc::Rc::<#path>::new(#tokens)))
            }
        };
        quote!(#path(#tokens)).to_tokens(out_tokens);
    }
}

impl ToTokens for Cons {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let cons_path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Cons);
        let car_tokens = self.car.to_token_stream();
        let cdr_tokens = self.cdr.to_token_stream();
        quote!(#cons_path { car: #car_tokens, cdr: #cdr_tokens }).to_tokens(tokens);
    }
}

impl ToTokens for ValueUnqualifiedSymbol {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueUnqualifiedSymbol);
        let tokens = self.0.as_str().to_token_stream();
        quote!(#path(#tokens.to_string())).to_tokens(out_tokens);
    }
}

impl ToTokens for ValueQualifiedSymbol {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueQualifiedSymbol);
        let package_tokens = self.package.as_str().to_token_stream();
        let name_tokens = self.name.as_str().to_token_stream();
        quote!(#path { package: #package_tokens.to_string(), name: #name_tokens.to_string(), })
            .to_tokens(out_tokens);
    }
}

impl ToTokens for ValueBool {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueBool);
        let tokens = self.0.to_token_stream();
        quote!(#path(#tokens)).to_tokens(out_tokens);
    }
}

impl ToTokens for ValueString {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueString);
        let tokens = self.0.as_str().to_token_stream();
        quote!(#path(#tokens.to_string())).to_tokens(out_tokens);
    }
}

impl ToTokens for ValueSemver {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueSemver);
        let major_tokens = self.major.to_token_stream();
        let rest_tokens = (&self.rest)
            .into_iter()
            .map(|c| {
                let mut s = c.to_token_stream();
                s.extend([<Token![,]>::default().to_token_stream()]);
                s
            })
            .collect::<TokenStream>();
        quote!(#path { major: #major_tokens, rest: ::std::vec::Vec::<u64>::from_iter([#rest_tokens]), }).to_tokens(out_tokens);
    }
}

impl ToTokens for ValueBackquote {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let bq_path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueBackquote);
        let value_path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value);
        let tokens = self.0.to_token_stream();
        quote!(#bq_path(::std::boxed::Box::<#value_path>::new(#tokens))).to_tokens(out_tokens);
    }
}

impl ToTokens for ValueComma {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let comma_path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueComma);
        let value_path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value);
        let tokens = self.0.to_token_stream();
        quote!(#comma_path(::std::boxed::Box::<#value_path>::new(#tokens))).to_tokens(out_tokens);
    }
}

impl ToTokens for ValueSplice {
    fn to_tokens(&self, out_tokens: &mut TokenStream) {
        let splice_path = parse_quote_fixup_crate!(::ryuk_lispcore::value::ValueSplice);
        let value_path = parse_quote_fixup_crate!(::ryuk_lispcore::value::Value);
        let tokens = self.0.to_token_stream();
        quote!(#splice_path(::std::boxed::Box::<#value_path>::new(#tokens))).to_tokens(out_tokens);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use ryuk_lispmacros::kira;

    use quote::{quote, ToTokens};
    use serial_test::serial;
    use std::rc::Rc;
    use syn::parse_quote;

    #[test]
    #[serial]
    fn test_crate_name() {
        std::env::set_var("CARGO_CRATE_NAME", "c1");
        assert_eq!(crate_name("c1"), "crate");
        assert_eq!(crate_name("c2"), "c2");
    }

    #[test]
    #[serial]
    #[should_panic]
    fn test_crate_name_no_env() {
        std::env::remove_var("CARGO_CRATE_NAME");
        crate_name("c1");
    }

    #[test]
    #[serial]
    fn test_fixup_crate() {
        std::env::set_var("CARGO_CRATE_NAME", "c1");
        assert_eq!(
            fixup_crate(parse_quote!(::c1::submod::func))
                .to_token_stream()
                .to_string(),
            quote!(crate::submod::func).to_string()
        );
        assert_eq!(
            fixup_crate(parse_quote!(::c2::Struct))
                .to_token_stream()
                .to_string(),
            quote!(::c2::Struct).to_string()
        );
    }

    #[test]
    #[serial]
    fn test_parse_quote_fixup_crate() {
        std::env::set_var("CARGO_CRATE_NAME", "c1");
        assert_eq!(
            parse_quote_fixup_crate!(::c1::Struct)
                .to_token_stream()
                .to_string(),
            quote!(crate::Struct).to_string()
        );
        assert_eq!(
            parse_quote_fixup_crate!(::c2).to_token_stream().to_string(),
            quote!(::c2).to_string()
        );
    }

    #[test]
    fn test_kira_macro() {
        assert_eq!(
            kira!("(())"),
            Value::List(ValueList(Some(Rc::new(Cons {
                car: Value::List(ValueList(None)),
                cdr: ValueList(None)
            }))))
        );
        assert_eq!(
            kira!("uqsym"),
            Value::UnqualifiedSymbol(ValueUnqualifiedSymbol("uqsym".to_string()))
        );
        assert_eq!(
            kira!("pkg:qsym"),
            Value::QualifiedSymbol(ValueQualifiedSymbol {
                package: "pkg".to_string(),
                name: "qsym".to_string()
            })
        );
        assert_eq!(kira!("#t"), Value::Bool(ValueBool(true)));
        assert_eq!(kira!("#f"), Value::Bool(ValueBool(false)));
        assert_eq!(
            kira!("\"str\""),
            Value::String(ValueString("str".to_string()))
        );
        assert_eq!(
            kira!("#v1"),
            Value::Semver(ValueSemver {
                major: 1,
                rest: Vec::new()
            })
        );
        assert_eq!(
            kira!("#v2.3.4"),
            Value::Semver(ValueSemver {
                major: 2,
                rest: vec![3, 4]
            })
        );
        assert_eq!(
            kira!("`(,a ,@b)"),
            Value::Backquote(ValueBackquote(Box::new(Value::List(ValueList(Some(
                Rc::new(Cons {
                    car: Value::Comma(ValueComma(Box::new(Value::UnqualifiedSymbol(
                        ValueUnqualifiedSymbol("a".to_string())
                    )))),
                    cdr: ValueList(Some(Rc::new(Cons {
                        car: Value::Splice(ValueSplice(Box::new(Value::UnqualifiedSymbol(
                            ValueUnqualifiedSymbol("b".to_string())
                        )))),
                        cdr: ValueList(None)
                    })))
                })
            ))))))
        );
    }
}
