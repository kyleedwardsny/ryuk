use ryuk_lispcore::value::Value;
use ryuk_lispparser::LispParser;

use quote::ToTokens;
use syn::{parse_macro_input, LitStr};

#[proc_macro]
pub fn kira(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let lit_str = parse_macro_input!(item as LitStr);
    let str = lit_str.value();
    let mut parser = LispParser::new(str.chars().peekable());
    let atom = parser
        .next()
        .expect("Expected exactly one Lisp value in string")
        .expect(&format!("Error parsing Lisp value: \"{}\"", str));
    assert!(
        parser.next().is_none(),
        "Expected exactly one Lisp value in string"
    );
    let value: Value = atom
        .try_into()
        .expect("Expected Lisp value, got language directive");
    value.to_token_stream().into()
}
