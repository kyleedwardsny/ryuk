use std::fs::read_to_string;
use std::process::exit;
use syn::{Ident, Item};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

struct ParseData {
    cast_to_trait: Option<Ident>,
    value_trait: Option<Ident>,
    value_cast_traits: Vec<Ident>,
}

#[derive(Debug)]
struct Error {
    message: String,
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

fn check_option_some<'o, T>(name: &str, opt: &'o Option<T>) -> Result<&'o T> {
    match opt {
        Option::Some(t) => Result::Ok(t),
        Option::None => Result::Err(Box::new(Error {
            message: format!("{} is None, should be Some", name),
        })),
    }
}

fn try_set_trait(name: &str, t: &mut Option<Ident>, ident: &Ident) -> Result<()> {
    if t.is_some() {
        return Result::Err(Box::new(Error {
            message: format!("{} has already been used", name),
        }));
    }
    *t = Option::Some(ident.clone());
    Result::Ok(())
}

fn write_env_var(name: &str, val: &str) {
    println!("cargo:rustc-env={}={}", name, val);
}

fn parse_items(parse_data: &mut ParseData, items: impl IntoIterator<Item = Item>) -> Result<()> {
    for i in items {
        match i {
            Item::Trait(t) => {
                for a in t.attrs {
                    if a.path.segments.len() == 1 {
                        let s = &a.path.segments[0];
                        let name = s.ident.to_string();
                        match &*name {
                            "cast_to_trait" => try_set_trait(
                                "cast_to_trait",
                                &mut parse_data.cast_to_trait,
                                &t.ident,
                            )?,
                            "value_trait" => {
                                try_set_trait("value_trait", &mut parse_data.value_trait, &t.ident)?
                            }
                            "value_cast_trait" => {
                                parse_data.value_cast_traits.push(t.ident.clone())
                            }
                            _ => (),
                        }
                    }
                }
            }
            Item::Mod(m) => {
                if let Option::Some((_, content)) = m.content {
                    parse_items(parse_data, content)?;
                }
            }
            _ => (),
        }
    }

    Result::Ok(())
}

fn parse_file(filename: &str) -> Result<()> {
    let contents = read_to_string(filename)?;
    let f = syn::parse_file(&contents)?;

    let mut parse_data = ParseData {
        cast_to_trait: Option::None,
        value_trait: Option::None,
        value_cast_traits: Vec::new(),
    };
    parse_items(&mut parse_data, f.items)?;

    let cast_to_trait = check_option_some("cast_to_trait", &parse_data.cast_to_trait)?;
    let value_trait = check_option_some("value_trait", &parse_data.value_trait)?;

    let mut first = true;
    let mut value_cast_traits = String::new();
    for t in parse_data.value_cast_traits {
        if !first {
            value_cast_traits.push(',');
        }
        first = false;
        value_cast_traits += &t.to_string();
    }

    write_env_var("RYUK_CAST_TO_TRAIT", &cast_to_trait.to_string());
    write_env_var("RYUK_VALUE_TRAIT", &value_trait.to_string());
    write_env_var("RYUK_VALUE_CAST_TRAITS", &value_cast_traits);

    Result::Ok(())
}

fn main() {
    match parse_file("src/lib.rs") {
        Result::Ok(()) => (),
        Result::Err(e) => {
            eprintln!("Could not parse file: {}", e);
            exit(1);
        }
    }
}
