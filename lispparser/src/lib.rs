use ryuk_lisptypes::*;
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

pub trait LispValues<T>
where
    T: ValueTypes,
{
    type Iter: Iterator<Item = Result<T::ValueRef>>;

    fn lisp_values(self) -> Self::Iter;
}

pub struct PeekableCharLispIterator<T, I>
where
    T: ValueTypes,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
{
    reader: Peekable<I>,
    phantom_types: PhantomData<T>,
}

impl<T, I> Iterator for PeekableCharLispIterator<T, I>
where
    T: ValueTypes,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
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

impl<T, I> LispValues<T> for Peekable<I>
where
    T: ValueTypes,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
{
    type Iter = PeekableCharLispIterator<T, I>;

    fn lisp_values(self) -> Self::Iter {
        PeekableCharLispIterator {
            reader: self,
            phantom_types: PhantomData,
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
    while let Option::Some(c) = peekable.peek() {
        if *c == ' ' || *c == '\n' {
            peekable.next();
        } else {
            break;
        }
    }
    Result::Ok(())
}

enum ReadDelimitedResult<T>
where
    T: ValueTypes,
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
    T: ValueTypes,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
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

fn read_list<T, I>(peekable: &mut Peekable<I>) -> Result<T::ValueRef>
where
    T: ValueTypes,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
{
    match read_delimited(peekable, ')')? {
        ReadDelimitedResult::Value(v) => Result::Ok(
            Value::<T>::Cons(ValueCons {
                car: v,
                cdr: read_list(peekable)?,
            })
            .into(),
        ),
        ReadDelimitedResult::InvalidToken(t) => match &*t {
            "." => match read_delimited(peekable, ')')? {
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
    T: ValueTypes,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
{
    if let Option::Some(_) = peekable.peek() {
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

pub enum ReadImplResult<T>
where
    T: ValueTypes,
{
    Value(T::ValueRef),
    InvalidToken(String),
    EndOfFile,
}

pub fn read_impl<T, I>(peekable: &mut Peekable<I>) -> Result<ReadImplResult<T>>
where
    T: ValueTypes,
    I: Iterator<Item = char>,
    Value<T>: Into<T::ValueRef>,
    String: Into<T::StringRef>,
{
    skip_whitespace(peekable)?;
    if let Option::Some(c) = peekable.peek() {
        if *c == '(' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(read_list(peekable)?))
        } else if *c == '#' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(read_macro(peekable)?))
        } else if *c == '"' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(
                Value::String(ValueString(read_string(peekable, '"')?.into())).into(),
            ))
        } else if is_token_char(*c) {
            match read_token(peekable)? {
                ReadTokenResult::ValidToken(t) => Result::Ok(ReadImplResult::Value(
                    Value::Symbol(ValueSymbol(t.to_lowercase().into())).into(),
                )),
                ReadTokenResult::InvalidToken(t) => Result::Ok(ReadImplResult::InvalidToken(t)),
            }
        } else {
            Result::Err(Error::new(
                ErrorKind::InvalidCharacter,
                format!("Invalid character: '{}'", c),
            ))
        }
    } else {
        Result::Ok(ReadImplResult::EndOfFile)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    #[derive(Debug)]
    struct ValueTypesRc;

    impl ValueTypes for ValueTypesRc {
        type ValueRef = Rc<Value<Self>>;
        type StringRef = String;
    }

    #[test]
    fn test_read_symbol() {
        let s = "sym SYM2\nSym3  \n   sym4";
        let mut i = LispValues::<ValueTypesRc>::lisp_values(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *sym!("sym"));
        assert_eq!(*i.next().unwrap().unwrap(), *sym!("sym2"));
        assert_eq!(*i.next().unwrap().unwrap(), *sym!("sym3"));
        assert_eq!(*i.next().unwrap().unwrap(), *sym!("sym4"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_bool() {
        let s = "#t #f\n#t  ";
        let mut i = LispValues::<ValueTypesRc>::lisp_values(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *bool!(true));
        assert_eq!(*i.next().unwrap().unwrap(), *bool!(false));
        assert_eq!(*i.next().unwrap().unwrap(), *bool!(true));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_invalid_macro() {
        let s = "#T #F #t#f  ";
        let mut i = LispValues::<ValueTypesRc>::lisp_values(s.chars().peekable());
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
        let s = "\"a\"  \"b \\\"\" \"\\n\nc\"  \"d";
        let mut i = LispValues::<ValueTypesRc>::lisp_values(s.chars().peekable());
        assert_eq!(*i.next().unwrap().unwrap(), *str!("a"));
        assert_eq!(*i.next().unwrap().unwrap(), *str!("b \""));
        assert_eq!(*i.next().unwrap().unwrap(), *str!("n\nc"));
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::EndOfFile
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_list() {
        let s = "(s1 s2 s3)(s4\n s5 s6 ) ( s7 () \"s8\") (#t . #f) ( s9 . s10 s11 (a";
        let mut i = LispValues::<ValueTypesRc>::lisp_values(s.chars().peekable());
        assert_eq!(
            *i.next().unwrap().unwrap(),
            *list!(sym!("s1"), sym!("s2"), sym!("s3"))
        );
        assert_eq!(
            *i.next().unwrap().unwrap(),
            *list!(sym!("s4"), sym!("s5"), sym!("s6"))
        );
        assert_eq!(
            *i.next().unwrap().unwrap(),
            *list!(sym!("s7"), nil!(), str!("s8"))
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
            crate::ErrorKind::EndOfFile
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_iterator() {
        let s = "() () ()";
        let mut num = 0;
        for v in LispValues::<ValueTypesRc>::lisp_values(s.chars().peekable()) {
            num += 1;
            assert_eq!(*v.unwrap(), *nil!());
        }
        assert_eq!(num, 3);
    }
}
