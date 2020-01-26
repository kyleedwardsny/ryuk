use ryuk_lispcore::list::ListItem;
use ryuk_lispcore::value::*;
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
    InvalidSemverComponent,
    IllegalComma,
    IllegalSplice,
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
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = char>,
{
    reader: Peekable<I>,
    phantom_types: PhantomData<T>,
}

impl<T, I> LispParser<T, I>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = char>,
{
    pub fn new(reader: Peekable<I>) -> Self {
        Self {
            reader,
            phantom_types: PhantomData,
        }
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
            Result::Err(Error::new(ErrorKind::IllegalComma, "Illegal comma"))
        } else {
            Result::Ok(Self {
                depth: self.depth - 1,
                status: ListItem::List(()),
            })
        }
    }

    pub fn splice(&self) -> Result<Self> {
        if self.depth == 0 || self.status != ListItem::Item(()) {
            Result::Err(Error::new(ErrorKind::IllegalSplice, "Illegal splice"))
        } else {
            Result::Ok(Self {
                depth: self.depth - 1,
                status: ListItem::List(()),
            })
        }
    }
}

impl<T, I> Iterator for LispParser<T, I>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = char>,
{
    type Item = Result<Value<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        match read_impl(&mut self.reader, BackquoteStatus::new()) {
            Result::Ok(r) => match r {
                ReadImplResult::Value(v) => Option::Some(Result::Ok(v)),
                ReadImplResult::EndOfFile => Option::None,
            },
            Result::Err(e) => Option::Some(Result::Err(e)),
        }
    }
}

fn is_token_char(c: char) -> bool {
    if let 'a'..='z' | 'A'..='Z' | '0'..='9' | '.' | '#' | '/' | '-' = c {
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

fn read_delimited<T, I>(
    peekable: &mut Peekable<I>,
    delimiter: char,
    bq: BackquoteStatus,
) -> Result<Option<Value<T>>>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = char>,
{
    skip_whitespace(peekable)?;
    if let Option::Some(c) = peekable.peek() {
        if *c == delimiter {
            peekable.next();
            Result::Ok(Option::None)
        } else {
            match read_impl(peekable, bq)? {
                ReadImplResult::Value(v) => Result::Ok(Option::Some(v)),
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

fn read_list<T, I>(peekable: &mut Peekable<I>, bq: BackquoteStatus) -> Result<ValueList<T>>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = char>,
{
    Result::Ok(ValueList(
        match read_delimited(peekable, ')', bq.list_item())? {
            Option::Some(v) => Option::Some(T::cons_ref_from_cons(Cons {
                car: v,
                cdr: read_list(peekable, bq)?,
            })),
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

    Result::Err(Error::new(ErrorKind::EndOfFile, "End of file reached"))
}

fn read_language_directive<S, V, I>(
    peekable: &mut Peekable<I>,
) -> Result<ValueLanguageDirective<S, V>>
where
    S: StringTypesMut + ?Sized,
    V: SemverTypesMut + ?Sized,
    I: Iterator<Item = char>,
{
    skip_whitespace(peekable)?;

    let t = read_token(peekable)?.try_unwrap_token()?;
    Result::Ok(if t == "kira" {
        skip_whitespace(peekable)?;
        ValueLanguageDirective::Kira(parse_semver(&read_token(peekable)?.try_unwrap_token()?)?)
    } else {
        ValueLanguageDirective::Other(S::string_ref_from_string(t))
    })
}

fn read_macro<T, I>(peekable: &mut Peekable<I>) -> Result<Value<T>>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = char>,
{
    if let Option::Some(&c) = peekable.peek() {
        if c == 'v' {
            peekable.next();
            Result::Ok(
                Value::Semver(parse_semver(&read_token(peekable)?.try_unwrap_token()?)?).into(),
            )
        } else {
            let t = read_token(peekable)?.try_unwrap_token()?;
            match &*t {
                "lang" => {
                    Result::Ok(Value::LanguageDirective(read_language_directive(peekable)?).into())
                }
                "t" => Result::Ok(Value::Bool(ValueBool(true)).into()),
                "f" => Result::Ok(Value::Bool(ValueBool(false)).into()),
                _ => Result::Err(Error::new(
                    ErrorKind::InvalidToken,
                    format!("Invalid macro: '{}'", t),
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

impl ReadTokenResult {
    pub fn try_unwrap_token(self) -> Result<String> {
        match self {
            Self::ValidToken(t) => Result::Ok(t),
            Self::InvalidToken(t) => Result::Err(Error::new(
                ErrorKind::InvalidToken,
                format!("Invalid token: '{}'", t),
            )),
        }
    }
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
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
{
    Value(Value<T>),
    EndOfFile,
}

impl<T> ReadImplResult<T>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
{
    pub fn try_unwrap_value(self) -> Result<Value<T>> {
        match self {
            Self::Value(v) => Result::Ok(v),
            Self::EndOfFile => Result::Err(Error::new(ErrorKind::EndOfFile, "End of file reached")),
        }
    }
}

fn read_impl<T, I>(peekable: &mut Peekable<I>, bq: BackquoteStatus) -> Result<ReadImplResult<T>>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = char>,
{
    skip_whitespace(peekable)?;
    if let Option::Some(&c) = peekable.peek() {
        if c == '(' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(Value::List(read_list(peekable, bq)?)))
        } else if c == '#' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(read_macro(peekable)?))
        } else if c == '"' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(Value::String(ValueString(
                T::StringTypes::string_ref_from_string(read_string(peekable, '"')?),
            ))))
        } else if c == '`' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(Value::Backquote(ValueBackquote(
                T::value_ref_from_value(read_impl(peekable, bq.backquote())?.try_unwrap_value()?),
            ))))
        } else if c == ',' {
            peekable.next();
            match peekable.peek() {
                Option::Some(&c2) => Result::Ok(ReadImplResult::Value(if c2 == '@' {
                    peekable.next();
                    Value::Splice(ValueSplice(T::value_ref_from_value(
                        read_impl(peekable, bq.splice()?)?.try_unwrap_value()?,
                    )))
                } else {
                    Value::Comma(ValueComma(T::value_ref_from_value(
                        read_impl(peekable, bq.comma()?)?.try_unwrap_value()?,
                    )))
                })),
                Option::None => {
                    Result::Err(Error::new(ErrorKind::EndOfFile, "End of file reached"))
                }
            }
        } else if c == '\'' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(Value::List(ValueList(Option::Some(
                T::cons_ref_from_cons(Cons {
                    car: Value::QualifiedSymbol(ValueQualifiedSymbol {
                        package: T::StringTypes::string_ref_from_static_str("std"),
                        name: T::StringTypes::string_ref_from_static_str("quote"),
                    }),
                    cdr: ValueList(Option::Some(T::cons_ref_from_cons(Cons {
                        car: read_impl(peekable, bq)?.try_unwrap_value()?,
                        cdr: ValueList(Option::None),
                    }))),
                }),
            )))))
        } else if is_token_char(c) {
            match read_token(peekable)? {
                ReadTokenResult::ValidToken(t1) => match peekable.peek() {
                    Option::Some(':') => {
                        peekable.next();
                        Result::Ok(ReadImplResult::Value(Value::QualifiedSymbol(
                            ValueQualifiedSymbol {
                                package: T::StringTypes::string_ref_from_string(t1.to_lowercase()),
                                name: T::StringTypes::string_ref_from_string(
                                    read_token(peekable)?.try_unwrap_token()?.to_lowercase(),
                                ),
                            },
                        )))
                    }
                    _ => Result::Ok(ReadImplResult::Value(Value::UnqualifiedSymbol(
                        ValueUnqualifiedSymbol(T::StringTypes::string_ref_from_string(
                            t1.to_lowercase(),
                        )),
                    ))),
                },
                ReadTokenResult::InvalidToken(t) => Result::Err(Error::new(
                    ErrorKind::InvalidToken,
                    format!("Invalid token: '{}'", t),
                )),
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

fn parse_semver<V>(s: &str) -> Result<ValueSemver<V>>
where
    V: SemverTypesMut + ?Sized,
{
    let mut major = Option::None;
    let mut rest = V::semver_ref_default();

    for component_str in s.split('.') {
        let mut component = 0u64;
        let mut first = true;
        for c in component_str.chars() {
            if component == 0 && !first {
                return Result::Err(Error::new(
                    ErrorKind::InvalidSemverComponent,
                    format!("Invalid semver component: '{}'", component_str),
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
                ErrorKind::InvalidSemverComponent,
                "Invalid semver component: ''",
            ));
        }
        match &mut major {
            Option::None => major = Option::Some(component),
            Option::Some(_) => V::semver_ref_extend(&mut rest, std::iter::once(component)),
        }
    }

    match major {
        Option::Some(major) => Result::Ok(ValueSemver { major, rest }),
        Option::None => Result::Err(Error::new(
            ErrorKind::InvalidSemverComponent,
            "Invalid semver component: ''",
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ryuk_lispcore::*;

    #[test]
    fn test_parse_semver() {
        assert_eq!(parse_semver::<SemverTypesVec>("1").unwrap(), v![1]);

        assert_eq!(parse_semver::<SemverTypesVec>("2.0").unwrap(), v![2, 0]);

        assert_eq!(
            parse_semver::<SemverTypesVec>("3.5.10").unwrap(),
            v![3, 5, 10]
        );

        assert_eq!(
            parse_semver::<SemverTypesVec>("3.05").unwrap_err().kind,
            crate::ErrorKind::InvalidSemverComponent
        );

        assert_eq!(
            parse_semver::<SemverTypesVec>("").unwrap_err().kind,
            crate::ErrorKind::InvalidSemverComponent
        );

        assert_eq!(
            parse_semver::<SemverTypesVec>("5.").unwrap_err().kind,
            crate::ErrorKind::InvalidSemverComponent
        );

        assert_eq!(
            parse_semver::<SemverTypesVec>(".5").unwrap_err().kind,
            crate::ErrorKind::InvalidSemverComponent
        );

        assert_eq!(
            parse_semver::<SemverTypesVec>("3.a").unwrap_err().kind,
            crate::ErrorKind::InvalidCharacter
        );
    }

    #[test]
    fn test_read_unqualified_symbol() {
        let s = "uqsym1 UQSYM2\nUqSym3  \n   uqsym4";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("uqsym1"));
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("uqsym2"));
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("uqsym3"));
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("uqsym4"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_qualified_symbol() {
        let s = "pa1:qsym1 PA2:QSYM2\nPa3:QSym3  \n   pa4:qsym4 pa5: qsym5 pa6::qsym6";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(i.next().unwrap().unwrap(), v_qsym!("pa1", "qsym1"));
        assert_eq!(i.next().unwrap().unwrap(), v_qsym!("pa2", "qsym2"));
        assert_eq!(i.next().unwrap().unwrap(), v_qsym!("pa3", "qsym3"));
        assert_eq!(i.next().unwrap().unwrap(), v_qsym!("pa4", "qsym4"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("qsym5"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidCharacter
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("qsym6"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_bool() {
        let s = "#t #f\n#t  ";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(i.next().unwrap().unwrap(), v_bool!(true));
        assert_eq!(i.next().unwrap().unwrap(), v_bool!(false));
        assert_eq!(i.next().unwrap().unwrap(), v_bool!(true));
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
        assert_eq!(i.next().unwrap().unwrap(), v_str!("a"));
        assert_eq!(i.next().unwrap().unwrap(), v_str!("b \""));
        assert_eq!(i.next().unwrap().unwrap(), v_str!("n\n\\c"));
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
            i.next().unwrap().unwrap(),
            v_list!(v_qsym!("std", "quote"), v_uqsym!("a"))
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::EndOfFile
        );
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
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(i.next().unwrap().unwrap(), v_bq!(v_uqsym!("a")));
        assert_eq!(i.next().unwrap().unwrap(), v_bq!(v_comma!(v_uqsym!("b"))));
        assert_eq!(i.next().unwrap().unwrap(), v_bq!(v_list!(v_uqsym!("c"))));
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_list!(v_splice!(v_uqsym!("d"))))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_list!(v_comma!(v_uqsym!("e"))))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_list!(
                v_list!(v_comma!(v_uqsym!("f"))),
                v_list!(v_splice!(v_uqsym!("g"))),
                v_comma!(v_uqsym!("h"))
            ))
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("i"));
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_list!(v_uqsym!("j"), v_splice!(v_uqsym!("k"))))
        );
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::IllegalComma);
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("l"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("m"));
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::IllegalComma);
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("n"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("o"));
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_bq!(v_comma!(v_comma!(v_uqsym!("p")))))
        );
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::IllegalComma);
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("q"));
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_list!(v_bq!(v_list!(v_comma!(v_comma!(v_uqsym!("r")))))))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_list!(v_bq!(v_list!(
                v_uqsym!("s"),
                v_splice!(v_uqsym!("t"))
            ))))
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("u"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_bq!(v_list!(v_comma!(v_comma!(v_uqsym!("v"))))))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_bq!(v_list!(v_splice!(v_comma!(v_uqsym!("w"))))))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_bq!(v_list!(v_splice!(v_list!(v_splice!(v_uqsym!("x")))))))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_bq!(v_bq!(v_list!(v_comma!(v_list!(v_comma!(v_uqsym!("y")))))))
        );
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::IllegalComma);
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("z"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("aa"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::IllegalComma);
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("ab"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("ad"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("af"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::IllegalComma);
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("ai"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::IllegalComma);
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("ak"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("am"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("ao"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::IllegalSplice
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("aq"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            ErrorKind::InvalidCharacter
        );
    }

    #[test]
    fn test_read_v() {
        let s = "#v1.5  #v3\n#v2.5.4   #v3.05 #va.2 #V1.5";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(i.next().unwrap().unwrap(), v_v![1, 5]);
        assert_eq!(i.next().unwrap().unwrap(), v_v![3]);
        assert_eq!(i.next().unwrap().unwrap(), v_v![2, 5, 4]);
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidSemverComponent
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
    fn test_read_lang() {
        let s = "#lang kira 1.0 #lang\nnot-kira #lang Kira 1.0  \n  #lang ( #lang kira 1.a #Lang kira 1.0\n#lang kira 1.01";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(i.next().unwrap().unwrap(), v_lang_kira![1, 0]);
        assert_eq!(i.next().unwrap().unwrap(), v_lang_other!("not-kira"));
        assert_eq!(i.next().unwrap().unwrap(), v_lang_other!("Kira"));
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("1.0"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("kira"));
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("1.0"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidSemverComponent
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_list() {
        let s = "(s1 s2 p3:s3)(p4:s4\n ' p5:s5 s6 ) ( s7 () \"s8\") (#t . #f) ( s9 . s10 s11 ( . (a a:. (a";
        let mut i = LispParser::<ValueTypesRc, _>::new(s.chars().peekable());
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_list!(v_uqsym!("s1"), v_uqsym!("s2"), v_qsym!("p3", "s3"))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_list!(
                v_qsym!("p4", "s4"),
                v_list!(v_qsym!("std", "quote"), v_qsym!("p5", "s5")),
                v_uqsym!("s6")
            )
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            v_list!(v_uqsym!("s7"), v_list!(), v_str!("s8"))
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(i.next().unwrap().unwrap(), v_bool!(false));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidCharacter
        );
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("s10"));
        assert_eq!(i.next().unwrap().unwrap(), v_uqsym!("s11"));
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
        assert_eq!(i.next().unwrap().unwrap(), v_bool!(true));
        assert_eq!(i.next().unwrap().unwrap(), v_bool!(false));
        assert_eq!(i.next().unwrap().unwrap(), v_str!("a;b"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_iterator() {
        let s = "() () ()";
        let mut num = 0;
        for v in LispParser::<ValueTypesRc, _>::new(s.chars().peekable()) {
            num += 1;
            assert_eq!(v.unwrap(), v_list!());
        }
        assert_eq!(num, 3);
    }
}
