use ryuk_lisptypes::*;
use std::borrow::BorrowMut;
use std::fmt::Formatter;
use std::iter::Peekable;
use std::marker::PhantomData;

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub error: Box<dyn std::error::Error>,
}

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    EndOfFile,
    IoError,
    InvalidToken,
    InvalidCharacter,
    InvalidVersionComponent,
}

impl Error {
    pub fn new<E>(kind: ErrorKind, error: E) -> Error
    where
        E: Into<Box<dyn std::error::Error>>,
    {
        Error {
            kind,
            error: error.into(),
        }
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::new(ErrorKind::IoError, e)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
        self.error.fmt(formatter)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct LispParser<T, I>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
{
    reader: Peekable<I>,
    phantom_types: PhantomData<T>,
}

impl<T, I> LispParser<T, I>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
{
    pub fn new(reader: Peekable<I>) -> Self {
        Self {
            reader,
            phantom_types: PhantomData,
        }
    }
}

impl<T, I> Iterator for LispParser<T, I>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
    for<'a> <T::VersionTypes as VersionTypes>::Version: Extend<&'a u64>,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
    &'static str: Into<T::StringRef>,
    <T::VersionTypes as VersionTypes>::VersionRef:
        Default + BorrowMut<<T::VersionTypes as VersionTypes>::Version>,
{
    type Item = Result<T::ValueRef>;

    fn next(&mut self) -> Option<Self::Item> {
        match read_impl(&mut self.reader) {
            Result::Ok(r) => match r {
                ReadImplResult::Value(v) => Option::Some(Result::Ok(v)),
                ReadImplResult::InvalidToken(t) => Option::Some(Result::Err(Error::new(
                    ErrorKind::InvalidToken,
                    format!("Invalid token: '{}'", t),
                ))),
                ReadImplResult::EndOfFile => Option::None,
            },
            Result::Err(e) => Option::Some(Result::Err(e)),
        }
    }
}

fn is_token_char(c: char) -> bool {
    if let 'a'..='z' | 'A'..='Z' | '0'..='9' | '.' | '#' = c {
        true
    } else {
        false
    }
}

fn skip_whitespace<I: Iterator<Item = char>>(peekable: &mut Peekable<I>) -> Result<()> {
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
    Result::Ok(())
}

enum ReadDelimitedResult<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
{
    Value(T::ValueRef),
    InvalidToken(String),
    EndDelimiter,
}

fn read_delimited<T, I>(
    peekable: &mut Peekable<I>,
    delimiter: char,
) -> Result<ReadDelimitedResult<T>>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
    for<'a> <T::VersionTypes as VersionTypes>::Version: Extend<&'a u64>,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
    &'static str: Into<T::StringRef>,
    <T::VersionTypes as VersionTypes>::VersionRef:
        Default + BorrowMut<<T::VersionTypes as VersionTypes>::Version>,
{
    skip_whitespace(peekable)?;
    if let Option::Some(c) = peekable.peek() {
        if *c == delimiter {
            peekable.next();
            Result::Ok(ReadDelimitedResult::EndDelimiter)
        } else {
            match read_impl(peekable)? {
                ReadImplResult::Value(v) => Result::Ok(ReadDelimitedResult::Value(v)),
                ReadImplResult::InvalidToken(t) => Result::Ok(ReadDelimitedResult::InvalidToken(t)),
                ReadImplResult::EndOfFile => Result::Err(Error::new(
                    ErrorKind::EndOfFile,
                    "End of file reached".to_string(),
                )),
            }
        }
    } else {
        Result::Err(Error::new(
            ErrorKind::EndOfFile,
            "End of file reached".to_string(),
        ))
    }
}

fn read_list<T, I>(peekable: &mut Peekable<I>, allow_dot: bool) -> Result<T::ValueRef>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
    for<'a> <T::VersionTypes as VersionTypes>::Version: Extend<&'a u64>,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
    &'static str: Into<T::StringRef>,
    <T::VersionTypes as VersionTypes>::VersionRef:
        Default + BorrowMut<<T::VersionTypes as VersionTypes>::Version>,
{
    match read_delimited(peekable, ')')? {
        ReadDelimitedResult::Value(v) => Result::Ok(
            Value::<T>::Cons(ValueCons {
                car: v,
                cdr: read_list(peekable, true)?,
            })
            .into(),
        ),
        ReadDelimitedResult::InvalidToken(t) => match (allow_dot, &*t) {
            (true, ".") => match read_delimited(peekable, ')')? {
                ReadDelimitedResult::Value(cdr) => match read_delimited::<T, I>(peekable, ')')? {
                    ReadDelimitedResult::EndDelimiter => Result::Ok(cdr),
                    _ => Result::Err(Error::new(
                        ErrorKind::InvalidToken,
                        "Expected ')', got something else",
                    )),
                },
                _ => Result::Err(Error::new(
                    ErrorKind::InvalidToken,
                    "Expected value, got something else",
                )),
            },
            _ => Result::Err(Error::new(
                ErrorKind::InvalidToken,
                format!("Invalid token: '{}'", t),
            )),
        },
        ReadDelimitedResult::EndDelimiter => Result::Ok(Value::Nil.into()),
    }
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

    Result::Err(Error::new(ErrorKind::EndOfFile, "End of file reached"))
}

fn read_macro<T, I>(peekable: &mut Peekable<I>) -> Result<T::ValueRef>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
    for<'a> <T::VersionTypes as VersionTypes>::Version: Extend<&'a u64>,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
    <T::VersionTypes as VersionTypes>::VersionRef:
        Default + BorrowMut<<T::VersionTypes as VersionTypes>::Version>,
{
    if let Option::Some(&c) = peekable.peek() {
        if c == 'v' {
            peekable.next();
            match read_token(peekable)? {
                ReadTokenResult::ValidToken(t) => {
                    Result::Ok(Value::Version(parse_version(&t)?).into())
                }
                ReadTokenResult::InvalidToken(t) => Result::Err(Error::new(
                    ErrorKind::InvalidToken,
                    format!("Invalid token: '{}'", t),
                )),
            }
        } else {
            match read_token(peekable)? {
                ReadTokenResult::ValidToken(t) => match &*t {
                    "t" => Result::Ok(Value::Bool(ValueBool(true)).into()),
                    "f" => Result::Ok(Value::Bool(ValueBool(false)).into()),
                    _ => Result::Err(Error::new(
                        ErrorKind::InvalidToken,
                        format!("Invalid macro: '{}'", t),
                    )),
                },
                ReadTokenResult::InvalidToken(t) => Result::Err(Error::new(
                    ErrorKind::InvalidToken,
                    format!("Invalid token: '{}'", t),
                )),
            }
        }
    } else {
        Result::Err(Error::new(
            ErrorKind::EndOfFile,
            "End of file reached".to_string(),
        ))
    }
}

enum ReadTokenResult {
    ValidToken(String),
    InvalidToken(String),
}

fn read_token<I>(peekable: &mut Peekable<I>) -> Result<ReadTokenResult>
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

    Result::Ok(if valid {
        ReadTokenResult::ValidToken(token)
    } else {
        ReadTokenResult::InvalidToken(token)
    })
}

enum ReadImplResult<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
{
    Value(T::ValueRef),
    InvalidToken(String),
    EndOfFile,
}

fn read_impl<T, I>(peekable: &mut Peekable<I>) -> Result<ReadImplResult<T>>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::VersionTypes as VersionTypes>::Version: IntoIterator<Item = &'a u64>,
    for<'a> <T::VersionTypes as VersionTypes>::Version: Extend<&'a u64>,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
    &'static str: Into<T::StringRef>,
    <T::VersionTypes as VersionTypes>::VersionRef:
        Default + BorrowMut<<T::VersionTypes as VersionTypes>::Version>,
{
    skip_whitespace(peekable)?;
    if let Option::Some(&c) = peekable.peek() {
        if c == '(' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(read_list(peekable, false)?))
        } else if c == '#' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(read_macro(peekable)?))
        } else if c == '"' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(
                Value::String(ValueString(read_string(peekable, '"')?.into())).into(),
            ))
        } else if c == '\'' {
            peekable.next();
            match read_impl(peekable)? {
                ReadImplResult::Value(v) => Result::Ok(ReadImplResult::Value(
                    Value::Cons(ValueCons {
                        car: Value::QualifiedSymbol(ValueQualifiedSymbol {
                            package: "std".into(),
                            name: "quote".into(),
                        })
                        .into(),
                        cdr: Value::Cons(ValueCons {
                            car: v,
                            cdr: Value::Nil.into(),
                        })
                        .into(),
                    })
                    .into(),
                )),
                ReadImplResult::InvalidToken(t) => Result::Err(Error::new(
                    ErrorKind::InvalidToken,
                    format!("Invalid token: '{}'", t),
                )),
                ReadImplResult::EndOfFile => {
                    Result::Err(Error::new(ErrorKind::EndOfFile, "End of file reached"))
                }
            }
        } else if is_token_char(c) {
            match read_token(peekable)? {
                ReadTokenResult::ValidToken(t1) => match peekable.peek() {
                    Option::Some(':') => {
                        peekable.next();
                        match read_token(peekable)? {
                            ReadTokenResult::ValidToken(t2) => Result::Ok(ReadImplResult::Value(
                                Value::QualifiedSymbol(ValueQualifiedSymbol {
                                    package: t1.to_lowercase().into(),
                                    name: t2.to_lowercase().into(),
                                })
                                .into(),
                            )),
                            ReadTokenResult::InvalidToken(t) => Result::Err(Error::new(
                                ErrorKind::InvalidToken,
                                format!("Invalid token: '{}'", t),
                            )),
                        }
                    }
                    _ => Result::Ok(ReadImplResult::Value(
                        Value::UnqualifiedSymbol(ValueUnqualifiedSymbol(t1.to_lowercase().into()))
                            .into(),
                    )),
                },
                ReadTokenResult::InvalidToken(t) => Result::Ok(ReadImplResult::InvalidToken(t)),
            }
        } else {
            peekable.next();
            Result::Err(Error::new(
                ErrorKind::InvalidCharacter,
                format!("Invalid character: '{}'", c),
            ))
        }
    } else {
        Result::Ok(ReadImplResult::EndOfFile)
    }
}

fn parse_version<V>(s: &str) -> Result<ValueVersion<V>>
where
    V: VersionTypes,
    for<'a> &'a V::Version: IntoIterator<Item = &'a u64>,
    for<'a> V::Version: Extend<&'a u64>,
    V::VersionRef: Default + BorrowMut<V::Version>,
{
    let mut result = V::VersionRef::default();

    for component_str in s.split('.') {
        let mut component = 0u64;
        let mut first = true;
        for c in component_str.chars() {
            if component == 0 && !first {
                return Result::Err(Error::new(
                    ErrorKind::InvalidVersionComponent,
                    format!("Invalid version component: '{}'", component_str),
                ));
            }
            if let '0'..='9' = c {
                component *= 10;
                component += c as u64 - '0' as u64;
            } else {
                return Result::Err(Error::new(
                    ErrorKind::InvalidCharacter,
                    format!("Invalid character: '{}'", c),
                ));
            }
            first = false;
        }
        if first {
            return Result::Err(Error::new(
                ErrorKind::InvalidVersionComponent,
                "Invalid version component: ''",
            ));
        }
        result.borrow_mut().extend(&[component]);
    }

    Result::Ok(ValueVersion(result))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_version() {
        assert_eq!(
            parse_version::<VersionTypesVec>("1").unwrap(),
            ValueVersion::<VersionTypesVec>(vec![1u64])
        );

        assert_eq!(
            parse_version::<VersionTypesVec>("2.0").unwrap(),
            ValueVersion::<VersionTypesVec>(vec![2u64, 0u64])
        );

        assert_eq!(
            parse_version::<VersionTypesVec>("3.5.10").unwrap(),
            ValueVersion::<VersionTypesVec>(vec![3u64, 5u64, 10u64])
        );

        assert_eq!(
            parse_version::<VersionTypesVec>("3.05").unwrap_err().kind,
            crate::ErrorKind::InvalidVersionComponent
        );

        assert_eq!(
            parse_version::<VersionTypesVec>("").unwrap_err().kind,
            crate::ErrorKind::InvalidVersionComponent
        );

        assert_eq!(
            parse_version::<VersionTypesVec>("5.").unwrap_err().kind,
            crate::ErrorKind::InvalidVersionComponent
        );

        assert_eq!(
            parse_version::<VersionTypesVec>(".5").unwrap_err().kind,
            crate::ErrorKind::InvalidVersionComponent
        );

        assert_eq!(
            parse_version::<VersionTypesVec>("3.a").unwrap_err().kind,
            crate::ErrorKind::InvalidCharacter
        );
    }

    #[test]
    fn test_read_unqualified_symbol() {
        let s = "uqsym1 UQSYM2\nUqSym3  \n   uqsym4";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *uqsym!("uqsym1"));
        assert_eq!(*i.next().unwrap().unwrap(), *uqsym!("uqsym2"));
        assert_eq!(*i.next().unwrap().unwrap(), *uqsym!("uqsym3"));
        assert_eq!(*i.next().unwrap().unwrap(), *uqsym!("uqsym4"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_qualified_symbol() {
        let s = "pa1:qsym1 PA2:QSYM2\nPa3:QSym3  \n   pa4:qsym4 pa5: qsym5 pa6::qsym6";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *qsym!("pa1", "qsym1"));
        assert_eq!(*i.next().unwrap().unwrap(), *qsym!("pa2", "qsym2"));
        assert_eq!(*i.next().unwrap().unwrap(), *qsym!("pa3", "qsym3"));
        assert_eq!(*i.next().unwrap().unwrap(), *qsym!("pa4", "qsym4"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(*i.next().unwrap().unwrap(), *uqsym!("qsym5"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidCharacter
        );
        assert_eq!(*i.next().unwrap().unwrap(), *uqsym!("qsym6"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_bool() {
        let s = "#t #f\n#t  ";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *bool!(true));
        assert_eq!(*i.next().unwrap().unwrap(), *bool!(false));
        assert_eq!(*i.next().unwrap().unwrap(), *bool!(true));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_invalid_macro() {
        let s = "#T #F #t#f  ";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_string() {
        let s = "\"a\"  \"b \\\"\" \"\\n\n\\\\c\"  \"d";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *str!("a"));
        assert_eq!(*i.next().unwrap().unwrap(), *str!("b \""));
        assert_eq!(*i.next().unwrap().unwrap(), *str!("n\n\\c"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::EndOfFile
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_quote() {
        let s = "'a '";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(
            *i.next().unwrap().unwrap(),
            *list!(qsym!("std", "quote"), uqsym!("a"))
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::EndOfFile
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_v() {
        let s = "#v1.5  #v3\n#v2.5.4   #v3.05 #va.2 #V1.5";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *v![1, 5]);
        assert_eq!(*i.next().unwrap().unwrap(), *v![3]);
        assert_eq!(*i.next().unwrap().unwrap(), *v![2, 5, 4]);
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidVersionComponent
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_list() {
        let s = "(s1 s2 p3:s3)(p4:s4\n ' p5:s5 s6 ) ( s7 () \"s8\") (#t . #f) ( s9 . s10 s11 ( . (a a:. (a";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(
            *i.next().unwrap().unwrap(),
            *list!(uqsym!("s1"), uqsym!("s2"), qsym!("p3", "s3"))
        );
        assert_eq!(
            *i.next().unwrap().unwrap(),
            *list!(
                qsym!("p4", "s4"),
                list!(qsym!("std", "quote"), qsym!("p5", "s5")),
                uqsym!("s6")
            )
        );
        assert_eq!(
            *i.next().unwrap().unwrap(),
            *list!(uqsym!("s7"), nil!(), str!("s8"))
        );
        assert_eq!(
            *i.next().unwrap().unwrap(),
            *cons!(bool!(true), bool!(false))
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::EndOfFile
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_comment() {
        let s = " #t;Hello\n  #f ; world! #t\n \"a;b\"";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *bool!(true));
        assert_eq!(*i.next().unwrap().unwrap(), *bool!(false));
        assert_eq!(*i.next().unwrap().unwrap(), *str!("a;b"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_iterator() {
        let s = "() () ()";
        let mut num = 0;
        for v in LispParser::<ValueTypesRc, _>::new(s.chars().peekable()) {
            num += 1;
            assert_eq!(*v.unwrap(), *nil!());
        }
        assert_eq!(num, 3);
    }
}
