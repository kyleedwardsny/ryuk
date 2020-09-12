use ryuk_lispcore::error::*;
use ryuk_lispcore::list::ListItem;
use ryuk_lispcore::value::*;
use ryuk_lispcore::*;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::iter::Peekable;

macro_rules! eq_match {
    ($lhs: expr, $rhs:expr, { $(($lpat:pat, $rpat:pat) => $result:expr,)* }) => {
        match $lhs {
            $($lpat => match $rhs {
                $rpat => $result,
                _ => false,
            }),*
        }
    };
}

macro_rules! e_parse_error {
    () => {
        e_std_cond!("parse-error")
    };
}

macro_rules! e_end_of_file {
    () => {
        e_std_cond!("end-of-file")
    };
}

macro_rules! e_unexpected_lang {
    () => {
        e_std_cond!("unexpected-lang")
    };
}

macro_rules! e_missing_lang {
    () => {
        e_std_cond!("missing-lang")
    };
}

#[derive(Debug)]
pub enum LanguageDirective {
    Kira(ValueSemver),
    Other(String),
}

impl Clone for LanguageDirective {
    fn clone(&self) -> Self {
        match self {
            LanguageDirective::Kira(v) => LanguageDirective::Kira(v.clone()),
            LanguageDirective::Other(name) => LanguageDirective::Other(name.clone()),
        }
    }
}

impl PartialEq<LanguageDirective> for LanguageDirective {
    fn eq(&self, rhs: &LanguageDirective) -> bool {
        eq_match!(self, rhs, {
            (LanguageDirective::Kira(v1), LanguageDirective::Kira(v2)) => v1 == v2,
            (LanguageDirective::Other(n1), LanguageDirective::Other(n2)) => n1 == n2,
        })
    }
}

#[macro_export]
macro_rules! lang_kira_ref {
    ($major:expr, $rest:expr) => {
        $crate::LanguageDirective::Kira(vref!($major, $rest))
    };
}

#[macro_export]
macro_rules! lang_kira {
    [$major:expr] => {
        lang_kira_ref!($major, vec![])
    };

    [$major:expr, $($rest:expr),*] => {
        lang_kira_ref!($major, vec![$($rest as u64),*])
    };
}

#[macro_export]
macro_rules! lang_other {
    ($name:expr) => {
        $crate::LanguageDirective::Other($name.into())
    };
}

#[derive(Debug)]
pub enum Atom {
    LanguageDirective(LanguageDirective),
    Value(Value),
}

impl TryFrom<Atom> for Value {
    type Error = Error;
    fn try_from(value: Atom) -> Result<Value> {
        match value {
            Atom::Value(v) => Result::Ok(v),
            Atom::LanguageDirective(_) => Result::Err(e_unexpected_lang!()),
        }
    }
}

impl TryFrom<Atom> for Box<Value> {
    type Error = Error;
    fn try_from(value: Atom) -> Result<Box<Value>> {
        let v: Value = value.try_into()?;
        Result::Ok(v.into())
    }
}

impl TryFrom<Atom> for LanguageDirective {
    type Error = Error;
    fn try_from(value: Atom) -> Result<LanguageDirective> {
        match value {
            Atom::Value(_) => Result::Err(e_missing_lang!()),
            Atom::LanguageDirective(l) => Result::Ok(l),
        }
    }
}

pub struct LispParser<I>
where
    I: Iterator<Item = char>,
{
    reader: Peekable<I>,
}

impl<I> LispParser<I>
where
    I: Iterator<Item = char>,
{
    pub fn new(reader: Peekable<I>) -> Self {
        Self { reader }
    }
}

#[derive(Clone, Copy, Debug)]
struct BackquoteStatus {
    depth: u32,
    status: ListItem<()>,
}

impl BackquoteStatus {
    pub fn new() -> Self {
        Self {
            depth: 0,
            status: ListItem::List(()),
        }
    }

    pub fn backquote(&self) -> Self {
        Self {
            depth: self.depth + 1,
            status: ListItem::List(()),
        }
    }

    pub fn list_item(&self) -> Self {
        Self {
            depth: self.depth,
            status: ListItem::Item(()),
        }
    }

    pub fn comma(&self) -> Result<Self> {
        if self.depth == 0 {
            Result::Err(e_parse_error!())
        } else {
            Result::Ok(Self {
                depth: self.depth - 1,
                status: ListItem::List(()),
            })
        }
    }

    pub fn splice(&self) -> Result<Self> {
        if self.depth == 0 || self.status != ListItem::Item(()) {
            Result::Err(e_parse_error!())
        } else {
            Result::Ok(Self {
                depth: self.depth - 1,
                status: ListItem::List(()),
            })
        }
    }
}

impl<I> Iterator for LispParser<I>
where
    I: Iterator<Item = char>,
{
    type Item = Result<Atom>;

    fn next(&mut self) -> Option<Self::Item> {
        read_impl(&mut self.reader, BackquoteStatus::new()).transpose()
    }
}

fn is_token_char(c: char) -> bool {
    if let 'a'..='z' | 'A'..='Z' | '0'..='9' | '.' | '#' | '/' | '-' = c {
        true
    } else {
        false
    }
}

fn skip_whitespace<I>(peekable: &mut Peekable<I>)
where
    I: Iterator<Item = char>,
{
    let mut comment = false;
    while let Option::Some(c) = peekable.peek() {
        if comment {
            if *c == '\n' {
                comment = false;
            }
            peekable.next();
        } else if *c == ';' {
            comment = true;
            peekable.next();
        } else if *c == ' ' || *c == '\n' {
            peekable.next();
        } else {
            break;
        }
    }
}

fn read_delimited<I>(
    peekable: &mut Peekable<I>,
    delimiter: char,
    bq: BackquoteStatus,
) -> Result<Option<Value>>
where
    I: Iterator<Item = char>,
{
    skip_whitespace(peekable);
    if let Option::Some(c) = peekable.peek() {
        if *c == delimiter {
            peekable.next();
            Result::Ok(Option::None)
        } else {
            Result::Ok(Option::Some(
                read_impl(peekable, bq)?
                    .ok_or(e_end_of_file!())?
                    .try_into()?,
            ))
        }
    } else {
        Result::Err(e_end_of_file!())
    }
}

fn read_list<I>(peekable: &mut Peekable<I>, bq: BackquoteStatus) -> Result<ValueList>
where
    I: Iterator<Item = char>,
{
    Result::Ok(ValueList(
        match read_delimited(peekable, ')', bq.list_item())? {
            Option::Some(v) => Option::Some(
                Cons {
                    car: v,
                    cdr: read_list(peekable, bq)?,
                }
                .into(),
            ),
            Option::None => Option::None,
        },
    ))
}

fn read_string<I>(peekable: &mut Peekable<I>, end: char) -> Result<String>
where
    I: Iterator<Item = char>,
{
    let mut result = String::new();
    let mut backslash = false;
    for c in peekable {
        if backslash {
            result.push(c);
            backslash = false;
        } else if c == end {
            return Result::Ok(result);
        } else if c == '\\' {
            backslash = true;
        } else {
            result.push(c);
        }
    }

    Result::Err(e_end_of_file!())
}

fn read_language_directive<I>(peekable: &mut Peekable<I>) -> Result<LanguageDirective>
where
    I: Iterator<Item = char>,
{
    skip_whitespace(peekable);

    let t = read_token(peekable).try_unwrap_token()?;
    Result::Ok(if t == "kira" {
        skip_whitespace(peekable);
        LanguageDirective::Kira(parse_semver(&read_token(peekable).try_unwrap_token()?)?)
    } else {
        LanguageDirective::Other(t)
    })
}

fn read_macro<I>(peekable: &mut Peekable<I>) -> Result<Atom>
where
    I: Iterator<Item = char>,
{
    if let Option::Some(&c) = peekable.peek() {
        if c == 'v' {
            peekable.next();
            Result::Ok(Atom::Value(
                Value::Semver(parse_semver(&read_token(peekable).try_unwrap_token()?)?).into(),
            ))
        } else {
            let t = read_token(peekable).try_unwrap_token()?;
            match &*t {
                "lang" => {
                    Result::Ok(Atom::LanguageDirective(read_language_directive(peekable)?).into())
                }
                "t" => Result::Ok(Atom::Value(Value::Bool(ValueBool(true)).into())),
                "f" => Result::Ok(Atom::Value(Value::Bool(ValueBool(false)).into())),
                _ => Result::Err(e_parse_error!()),
            }
        }
    } else {
        Result::Err(e_end_of_file!())
    }
}

enum ReadTokenResult {
    ValidToken(String),
    InvalidToken(String),
}

impl ReadTokenResult {
    pub fn try_unwrap_token(self) -> Result<String> {
        match self {
            Self::ValidToken(t) => Result::Ok(t),
            Self::InvalidToken(_) => Result::Err(e_parse_error!()),
        }
    }
}

fn read_token<I>(peekable: &mut Peekable<I>) -> ReadTokenResult
where
    I: Iterator<Item = char>,
{
    let mut token = String::new();

    let mut valid = false;
    while let Option::Some(c) = peekable.peek() {
        let c = *c;
        if is_token_char(c) {
            peekable.next();
            token.push(c);
            if c != '.' {
                valid = true;
            }
        } else {
            break;
        }
    }

    if valid {
        ReadTokenResult::ValidToken(token)
    } else {
        ReadTokenResult::InvalidToken(token)
    }
}

fn read_impl<I>(peekable: &mut Peekable<I>, bq: BackquoteStatus) -> Result<Option<Atom>>
where
    I: Iterator<Item = char>,
{
    skip_whitespace(peekable);
    if let Option::Some(&c) = peekable.peek() {
        if c == '(' {
            peekable.next();
            Result::Ok(Option::Some(Atom::Value(Value::List(read_list(
                peekable, bq,
            )?))))
        } else if c == '#' {
            peekable.next();
            Result::Ok(Option::Some(read_macro(peekable)?))
        } else if c == '"' {
            peekable.next();
            Result::Ok(Option::Some(Atom::Value(Value::String(ValueString(
                read_string(peekable, '"')?,
            )))))
        } else if c == '`' {
            peekable.next();
            Result::Ok(Option::Some(Atom::Value(Value::Backquote(ValueBackquote(
                read_impl(peekable, bq.backquote())?
                    .ok_or(e_end_of_file!())?
                    .try_into()?,
            )))))
        } else if c == ',' {
            peekable.next();
            match peekable.peek() {
                Option::Some(&c2) => Result::Ok(Option::Some(Atom::Value(if c2 == '@' {
                    peekable.next();
                    Value::Splice(ValueSplice(
                        read_impl(peekable, bq.splice()?)?
                            .ok_or(e_end_of_file!())?
                            .try_into()?,
                    ))
                } else {
                    Value::Comma(ValueComma(
                        read_impl(peekable, bq.comma()?)?
                            .ok_or(e_end_of_file!())?
                            .try_into()?,
                    ))
                }))),
                Option::None => Result::Err(e_end_of_file!()),
            }
        } else if c == '\'' {
            peekable.next();
            Result::Ok(Option::Some(Atom::Value(Value::List(ValueList(
                Option::Some(
                    Cons {
                        car: Value::QualifiedSymbol(ValueQualifiedSymbol {
                            package: "std".into(),
                            name: "quote".into(),
                        }),
                        cdr: ValueList(Option::Some(
                            Cons {
                                car: read_impl(peekable, bq)?
                                    .ok_or(e_end_of_file!())?
                                    .try_into()?,
                                cdr: ValueList(Option::None),
                            }
                            .into(),
                        )),
                    }
                    .into(),
                ),
            )))))
        } else if is_token_char(c) {
            match read_token(peekable) {
                ReadTokenResult::ValidToken(t1) => match peekable.peek() {
                    Option::Some(':') => {
                        peekable.next();
                        Result::Ok(Option::Some(Atom::Value(Value::QualifiedSymbol(
                            ValueQualifiedSymbol {
                                package: t1.to_lowercase(),
                                name: read_token(peekable).try_unwrap_token()?.to_lowercase(),
                            },
                        ))))
                    }
                    _ => Result::Ok(Option::Some(Atom::Value(Value::UnqualifiedSymbol(
                        ValueUnqualifiedSymbol(t1.to_lowercase()),
                    )))),
                },
                ReadTokenResult::InvalidToken(_) => Result::Err(e_parse_error!()),
            }
        } else {
            peekable.next();
            Result::Err(e_parse_error!())
        }
    } else {
        Result::Ok(Option::None)
    }
}

fn parse_semver(s: &str) -> Result<ValueSemver> {
    let mut major = Option::None;
    let mut rest = Vec::new();

    for component_str in s.split('.') {
        let mut component = 0u64;
        let mut first = true;
        for c in component_str.chars() {
            if component == 0 && !first {
                return Result::Err(e_parse_error!());
            }
            if let '0'..='9' = c {
                component *= 10;
                component += c as u64 - '0' as u64;
            } else {
                return Result::Err(e_parse_error!());
            }
            first = false;
        }
        if first {
            return Result::Err(e_parse_error!());
        }
        match &mut major {
            Option::None => major = Option::Some(component),
            Option::Some(_) => rest.push(component),
        }
    }

    match major {
        Option::Some(major) => Result::Ok(ValueSemver { major, rest }),
        Option::None => Result::Err(e_parse_error!()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! a2v {
        ($a:expr) => {
            TryInto::<Value>::try_into($a).unwrap()
        };
    }

    macro_rules! a2l {
        ($a:expr) => {
            TryInto::<LanguageDirective>::try_into($a).unwrap()
        };
    }

    #[test]
    fn test_lang_kira_macro() {
        let l1: super::LanguageDirective = lang_kira![1];
        match l1 {
            super::LanguageDirective::Kira(v) => {
                assert_eq!(v.major, 1);
                assert_eq!(v.rest, vec![]);
            }
            _ => panic!("Expected a Value::LanguageDirective with Kira"),
        }

        let l2: super::LanguageDirective = lang_kira![1, 0];
        match l2 {
            super::LanguageDirective::Kira(v) => {
                assert_eq!(v.major, 1);
                assert_eq!(v.rest, vec![0]);
            }
            _ => panic!("Expected a Value::LanguageDirective with Kira"),
        }
    }

    #[test]
    fn test_lang_other_macro() {
        let l1: super::LanguageDirective = lang_other!("not-kira");
        match l1 {
            super::LanguageDirective::Other(n) => {
                assert_eq!(n, "not-kira");
            }
            _ => panic!("Expected a Value::LanguageDirective with other"),
        }
    }

    #[test]
    fn test_lang_equality() {
        assert_eq!(lang_kira![1, 0], lang_kira![1, 0]);
        assert_eq!(lang_other!("not-kira"), lang_other!("not-kira"));
        assert_ne!(lang_kira![1, 0], lang_kira![1, 1]);
        assert_ne!(lang_kira![1, 0], lang_other!("not-kira"));
        assert_ne!(lang_other!("not-kira"), lang_other!("something-else"));
    }

    #[test]
    fn test_parse_semver() {
        assert_eq!(parse_semver("1").unwrap(), v![1]);

        assert_eq!(parse_semver("2.0").unwrap(), v![2, 0]);

        assert_eq!(parse_semver("3.5.10").unwrap(), v![3, 5, 10]);

        assert_eq!(parse_semver("3.05").unwrap_err(), e_parse_error!());

        assert_eq!(parse_semver("").unwrap_err(), e_parse_error!());

        assert_eq!(parse_semver("5.").unwrap_err(), e_parse_error!());

        assert_eq!(parse_semver(".5").unwrap_err(), e_parse_error!());

        assert_eq!(parse_semver("3.a").unwrap_err(), e_parse_error!());
    }

    #[test]
    fn test_read_unqualified_symbol() {
        let s = "uqsym1 UQSYM2\nUqSym3  \n   uqsym4";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("uqsym1"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("uqsym2"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("uqsym3"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("uqsym4"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_qualified_symbol() {
        let s = "pa1:qsym1 PA2:QSYM2\nPa3:QSym3  \n   pa4:qsym4 pa5: qsym5 pa6::qsym6";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_qsym!("pa1", "qsym1"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_qsym!("pa2", "qsym2"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_qsym!("pa3", "qsym3"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_qsym!("pa4", "qsym4"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("qsym5"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("qsym6"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_bool() {
        let s = "#t #f\n#t  ";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_bool!(true));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_bool!(false));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_bool!(true));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_invalid_macro() {
        let s = "#T #F #t#f  ";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_string() {
        let s = "\"a\"  \"b \\\"\" \"\\n\n\\\\c\"  \"d";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_str!("a"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_str!("b \""));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_str!("n\n\\c"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_end_of_file!());
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_quote() {
        let s = "'a '";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_list!(v_qsym!("std", "quote"), v_uqsym!("a"))
        );
        assert_eq!(i.next().unwrap().unwrap_err(), e_end_of_file!());
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_backquote() {
        let s = concat!(
            "`a `,b `(c) `(,@d) `(,e) `((,f) (,@g) ,h) `,@i `(j ,@k) ,l ,@m `,,n `,,@o ``,,p ",
            "``,,,q `(`(,,r)) `(`(s ,@t)) ``(,,@u) ``(,,v) ``(,@,w) ``(,@(,@x)) ``(,(,y)) (,z) ",
            "(,@aa) `(,(,ab)) `(,(ac ,@ad)) `(,(ae (,@af))) ``(,(,(ah (,ai)))) ",
            "``(,(aj ,((,ak)))) `(`(,(al ,,@am))) `(`(an ,,@ao)) `(`(ap ,@,@aq))"
        );
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_bq!(v_uqsym!("a")));
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_comma!(v_uqsym!("b")))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_list!(v_uqsym!("c")))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_list!(v_splice!(v_uqsym!("d"))))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_list!(v_comma!(v_uqsym!("e"))))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_list!(
                v_list!(v_comma!(v_uqsym!("f"))),
                v_list!(v_splice!(v_uqsym!("g"))),
                v_comma!(v_uqsym!("h"))
            ))
        );
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("i"));
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_list!(v_uqsym!("j"), v_splice!(v_uqsym!("k"))))
        );
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("l"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("m"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("n"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("o"));
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_bq!(v_comma!(v_comma!(v_uqsym!("p")))))
        );
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("q"));
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_list!(v_bq!(v_list!(v_comma!(v_comma!(v_uqsym!("r")))))))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_list!(v_bq!(v_list!(
                v_uqsym!("s"),
                v_splice!(v_uqsym!("t"))
            ))))
        );
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("u"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_bq!(v_list!(v_comma!(v_comma!(v_uqsym!("v"))))))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_bq!(v_list!(v_splice!(v_comma!(v_uqsym!("w"))))))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_bq!(v_list!(v_splice!(v_list!(v_splice!(v_uqsym!("x")))))))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_bq!(v_bq!(v_list!(v_comma!(v_list!(v_comma!(v_uqsym!("y")))))))
        );
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("z"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("aa"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("ab"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("ad"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("af"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("ai"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("ak"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("am"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("ao"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("aq"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
    }

    #[test]
    fn test_read_v() {
        let s = "#v1.5  #v3\n#v2.5.4   #v3.05 #va.2 #V1.5";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_v![1, 5]);
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_v![3]);
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_v![2, 5, 4]);
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_lang() {
        let s = "#lang kira 1.0 #lang\nnot-kira #lang Kira 1.0  \n  #lang ( #lang kira 1.a #Lang kira 1.0\n#lang kira 1.01";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(a2l!(i.next().unwrap().unwrap()), lang_kira![1, 0]);
        assert_eq!(a2l!(i.next().unwrap().unwrap()), lang_other!("not-kira"));
        assert_eq!(a2l!(i.next().unwrap().unwrap()), lang_other!("Kira"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("1.0"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("kira"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("1.0"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_list() {
        let s = "(s1 s2 p3:s3)(p4:s4\n ' p5:s5 s6 ) ( s7 () \"s8\") (#t . #f) ( s9 . s10 s11 ( . (a a:. (a";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_list!(v_uqsym!("s1"), v_uqsym!("s2"), v_qsym!("p3", "s3"))
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_list!(
                v_qsym!("p4", "s4"),
                v_list!(v_qsym!("std", "quote"), v_qsym!("p5", "s5")),
                v_uqsym!("s6")
            )
        );
        assert_eq!(
            a2v!(i.next().unwrap().unwrap()),
            v_list!(v_uqsym!("s7"), v_list!(), v_str!("s8"))
        );
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_bool!(false));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("s10"));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_uqsym!("s11"));
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_parse_error!());
        assert_eq!(i.next().unwrap().unwrap_err(), e_end_of_file!());
        assert!(i.next().is_none());
    }

    #[test]
    fn test_comment() {
        let s = " #t;Hello\n  #f ; world! #t\n \"a;b\"";
        let mut i = LispParser::new(s.chars().peekable());
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_bool!(true));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_bool!(false));
        assert_eq!(a2v!(i.next().unwrap().unwrap()), v_str!("a;b"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_iterator() {
        let s = "() () ()";
        let mut num = 0;
        for v in LispParser::new(s.chars().peekable()) {
            num += 1;
            assert_eq!(a2v!(v.unwrap()), v_list!());
        }
        assert_eq!(num, 3);
    }
}
