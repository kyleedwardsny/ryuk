use ryuk_lisptypes::*;
use std::borrow::Cow;
use std::fmt::Formatter;
use std::iter::Peekable;
use std::rc::Rc;

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

pub trait LispValues {
    type Iter: Iterator<Item = Result<ValueRef>>;

    fn lisp_values(self) -> Self::Iter;
}

pub struct PeekableCharLispIterator<I: Iterator<Item = char>> {
    reader: Peekable<I>,
}

impl<I: Iterator<Item = char>> Iterator for PeekableCharLispIterator<I> {
    type Item = Result<ValueRef>;

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

impl<I: Iterator<Item = char>> LispValues for Peekable<I> {
    type Iter = PeekableCharLispIterator<I>;

    fn lisp_values(self) -> Self::Iter {
        PeekableCharLispIterator { reader: self }
    }
}

fn is_token_char(c: char) -> bool {
    if let 'a'..='z' | '0'..='9' | '.' | '#' = c {
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

enum ReadDelimitedResult {
    Value(ValueRef),
    InvalidToken(String),
    EndDelimiter,
}

fn read_delimited<I: Iterator<Item = char>>(
    peekable: &mut Peekable<I>,
    delimiter: char,
) -> Result<ReadDelimitedResult> {
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

fn read_list<I: Iterator<Item = char>>(peekable: &mut Peekable<I>) -> Result<ValueRef> {
    match read_delimited(peekable, ')')? {
        ReadDelimitedResult::Value(v) => {
            Result::Ok(ValueRef::Owned(Rc::new(Value::Cons(ValueCons {
                car: SizedHolder(v),
                cdr: SizedHolder(read_list(peekable)?),
            }))))
        }
        ReadDelimitedResult::InvalidToken(t) => match &*t {
            "." => match read_delimited(peekable, ')')? {
                ReadDelimitedResult::Value(cdr) => match read_delimited(peekable, ')')? {
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
        ReadDelimitedResult::EndDelimiter => Result::Ok(ValueRef::Borrowed(&Value::Nil)),
    }
}

fn read_macro<I: Iterator<Item = char>>(peekable: &mut Peekable<I>) -> Result<ValueRef> {
    if let Option::Some(_) = peekable.peek() {
        match read_token(peekable)? {
            ReadTokenResult::ValidToken(t) => match &*t {
                "t" => Result::Ok(ValueRef::Borrowed(&Value::Bool(ValueBool(true)))),
                "f" => Result::Ok(ValueRef::Borrowed(&Value::Bool(ValueBool(false)))),
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

fn read_token<I: Iterator<Item = char>>(peekable: &mut Peekable<I>) -> Result<ReadTokenResult> {
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

pub enum ReadImplResult {
    Value(ValueRef),
    InvalidToken(String),
    EndOfFile,
}

pub fn read_impl<I: Iterator<Item = char>>(peekable: &mut Peekable<I>) -> Result<ReadImplResult> {
    skip_whitespace(peekable)?;
    if let Option::Some(c) = peekable.peek() {
        if *c == '(' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(read_list(peekable)?))
        } else if *c == '#' {
            peekable.next();
            Result::Ok(ReadImplResult::Value(read_macro(peekable)?))
        } else if is_token_char(*c) {
            match read_token(peekable)? {
                ReadTokenResult::ValidToken(t) => Result::Ok(ReadImplResult::Value(
                    ValueRef::Owned(Rc::new(Value::Symbol(ValueSymbol(Cow::Owned(t))))),
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

    #[test]
    fn test_read_symbol() {
        let s = "sym sym2\nsym3  \n   sym4";
        let mut i = s.chars().peekable().lisp_values();
        assert_eq!(i.next().unwrap().unwrap(), sym!("sym"));
        assert_eq!(i.next().unwrap().unwrap(), sym!("sym2"));
        assert_eq!(i.next().unwrap().unwrap(), sym!("sym3"));
        assert_eq!(i.next().unwrap().unwrap(), sym!("sym4"));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_bool() {
        let s = "#t #f\n#t  ";
        let mut i = s.chars().peekable().lisp_values();
        assert_eq!(i.next().unwrap().unwrap(), bool!(true));
        assert_eq!(i.next().unwrap().unwrap(), bool!(false));
        assert_eq!(i.next().unwrap().unwrap(), bool!(true));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_invalid_macro() {
        let s = "#t#f  ";
        let mut i = s.chars().peekable().lisp_values();
        assert_eq!(
            i.next().unwrap().unwrap_err().kind,
            crate::ErrorKind::InvalidToken
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_list() {
        let s = "(s1 s2 s3)(s4\n s5 s6 ) ( s7 () s8) (#t . #f) ( s9 . s10 s11 (a";
        let mut i = s.chars().peekable().lisp_values();
        assert_eq!(
            i.next().unwrap().unwrap(),
            list!(sym!("s1"), sym!("s2"), sym!("s3"))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            list!(sym!("s4"), sym!("s5"), sym!("s6"))
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            list!(sym!("s7"), nil!(), sym!("s8"))
        );
        assert_eq!(i.next().unwrap().unwrap(), cons!(bool!(true), bool!(false)));
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
        for v in s.chars().peekable().lisp_values() {
            num += 1;
            assert_eq!(v.unwrap(), nil!());
        }
        assert_eq!(num, 3);
    }
}
