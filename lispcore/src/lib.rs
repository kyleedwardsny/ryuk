use std::borrow::{Cow, ToOwned};
use std::fmt::Formatter;
use std::iter::Peekable;
use std::rc::Rc;

// Workaround for a bug in rustc. See
// https://github.com/rust-lang/rust/issues/47032.
#[derive(Debug)]
pub struct SizedHolder<T>(T);

#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
    error: Box<dyn std::error::Error>,
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

#[derive(Debug, PartialEq)]
pub struct ValueSymbol {
    pub name: Cow<'static, str>,
}

#[derive(Debug)]
pub struct ValueCons {
    pub car: SizedHolder<ValueRef>,
    pub cdr: SizedHolder<ValueRef>,
}

impl PartialEq for ValueCons {
    fn eq(&self, other: &Self) -> bool {
        *self.car.0 == *other.car.0 && *self.cdr.0 == *other.cdr.0
    }
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Nil,
    Symbol(ValueSymbol),
    Cons(ValueCons),
    Bool(bool),
}

impl ToOwned for Value {
    type Owned = Rc<Value>;

    fn to_owned(&self) -> Self::Owned {
        Rc::new(match self {
            Value::Nil => Value::Nil,
            Value::Symbol(ValueSymbol { name }) => {
                Value::Symbol(ValueSymbol { name: name.clone() })
            }
            Value::Cons(ValueCons { car, cdr }) => Value::Cons(ValueCons {
                car: SizedHolder(car.0.clone()),
                cdr: SizedHolder(cdr.0.clone()),
            }),
            Value::Bool(b) => Value::Bool(*b),
        })
    }
}

pub type ValueRef = Cow<'static, Value>;

pub trait LispValues {
    type Iter: Iterator<Item = Result<Value>>;

    fn lisp_values(self) -> Self::Iter;
}

pub struct PeekableCharLispIterator<I: Iterator<Item = char>> {
    reader: Peekable<I>,
}

impl<I: Iterator<Item = char>> Iterator for PeekableCharLispIterator<I> {
    type Item = Result<Value>;

    fn next(&mut self) -> Option<Self::Item> {
        match syntax::read_impl(&mut self.reader) {
            Result::Ok(r) => match r {
                syntax::ReadImplResult::Value(v) => Option::Some(Result::Ok(v)),
                syntax::ReadImplResult::InvalidToken(t) => Option::Some(Result::Err(Error::new(
                    ErrorKind::InvalidToken,
                    format!("Invalid token: '{}'", t),
                ))),
                syntax::ReadImplResult::EndOfFile => Option::None,
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

mod syntax {
    use super::*;

    fn is_token_char(c: char) -> bool {
        if let 'a'..='z' | '0'..='9' | '.' = c {
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
        Value(Value),
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
                    ReadImplResult::InvalidToken(t) => {
                        Result::Ok(ReadDelimitedResult::InvalidToken(t))
                    }
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

    fn read_list<I: Iterator<Item = char>>(peekable: &mut Peekable<I>) -> Result<Value> {
        match read_delimited(peekable, ')')? {
            ReadDelimitedResult::Value(v) => Result::Ok(Value::Cons(ValueCons {
                car: SizedHolder(ValueRef::Owned(Rc::new(v))),
                cdr: SizedHolder(ValueRef::Owned(Rc::new(read_list(peekable)?))),
            })),
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
            ReadDelimitedResult::EndDelimiter => Result::Ok(Value::Nil),
        }
    }

    fn read_macro<I: Iterator<Item = char>>(peekable: &mut Peekable<I>) -> Result<Value> {
        if let Option::Some(_) = peekable.peek() {
            match read_token(peekable)? {
                ReadTokenResult::ValidToken(t) => match &*t {
                    "t" => Result::Ok(Value::Bool(true)),
                    "f" => Result::Ok(Value::Bool(false)),
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
        Value(Value),
        InvalidToken(String),
        EndOfFile,
    }

    pub fn read_impl<I: Iterator<Item = char>>(
        peekable: &mut Peekable<I>,
    ) -> Result<ReadImplResult> {
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
                    ReadTokenResult::ValidToken(t) => {
                        Result::Ok(ReadImplResult::Value(Value::Symbol(ValueSymbol {
                            name: Cow::Owned(t),
                        })))
                    }
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_symbol() {
        let s = "sym sym2\nsym3  \n   sym4";
        let mut i = s.chars().peekable().lisp_values();
        assert_eq!(
            i.next().unwrap().unwrap(),
            Value::Symbol(ValueSymbol {
                name: Cow::Borrowed("sym")
            })
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            Value::Symbol(ValueSymbol {
                name: Cow::Borrowed("sym2")
            })
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            Value::Symbol(ValueSymbol {
                name: Cow::Borrowed("sym3")
            })
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            Value::Symbol(ValueSymbol {
                name: Cow::Borrowed("sym4")
            })
        );
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_bool() {
        let s = "#t #f\n#t  ";
        let mut i = s.chars().peekable().lisp_values();
        assert_eq!(i.next().unwrap().unwrap(), Value::Bool(true));
        assert_eq!(i.next().unwrap().unwrap(), Value::Bool(false));
        assert_eq!(i.next().unwrap().unwrap(), Value::Bool(true));
        assert!(i.next().is_none());
    }

    #[test]
    fn test_read_list() {
        let s = "(s1 s2 s3)(s4\n s5 s6 ) ( s7 () s8) (#t . #f) ( s9 . s10 s11 (a";
        let mut i = s.chars().peekable().lisp_values();
        assert_eq!(
            i.next().unwrap().unwrap(),
            Value::Cons(ValueCons {
                car: SizedHolder(Cow::Borrowed(&Value::Symbol(ValueSymbol {
                    name: Cow::Borrowed("s1")
                }))),
                cdr: SizedHolder(Cow::Borrowed(&Value::Cons(ValueCons {
                    car: SizedHolder(Cow::Borrowed(&Value::Symbol(ValueSymbol {
                        name: Cow::Borrowed("s2")
                    }))),
                    cdr: SizedHolder(Cow::Borrowed(&Value::Cons(ValueCons {
                        car: SizedHolder(Cow::Borrowed(&Value::Symbol(ValueSymbol {
                            name: Cow::Borrowed("s3")
                        }))),
                        cdr: SizedHolder(Cow::Borrowed(&Value::Nil)),
                    }))),
                }))),
            })
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            Value::Cons(ValueCons {
                car: SizedHolder(Cow::Borrowed(&Value::Symbol(ValueSymbol {
                    name: Cow::Borrowed("s4")
                }))),
                cdr: SizedHolder(Cow::Borrowed(&Value::Cons(ValueCons {
                    car: SizedHolder(Cow::Borrowed(&Value::Symbol(ValueSymbol {
                        name: Cow::Borrowed("s5")
                    }))),
                    cdr: SizedHolder(Cow::Borrowed(&Value::Cons(ValueCons {
                        car: SizedHolder(Cow::Borrowed(&Value::Symbol(ValueSymbol {
                            name: Cow::Borrowed("s6")
                        }))),
                        cdr: SizedHolder(Cow::Borrowed(&Value::Nil)),
                    }))),
                }))),
            })
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            Value::Cons(ValueCons {
                car: SizedHolder(Cow::Borrowed(&Value::Symbol(ValueSymbol {
                    name: Cow::Borrowed("s7")
                }))),
                cdr: SizedHolder(Cow::Borrowed(&Value::Cons(ValueCons {
                    car: SizedHolder(Cow::Borrowed(&Value::Nil)),
                    cdr: SizedHolder(Cow::Borrowed(&Value::Cons(ValueCons {
                        car: SizedHolder(Cow::Borrowed(&Value::Symbol(ValueSymbol {
                            name: Cow::Borrowed("s8")
                        }))),
                        cdr: SizedHolder(Cow::Borrowed(&Value::Nil)),
                    }))),
                }))),
            })
        );
        assert_eq!(
            i.next().unwrap().unwrap(),
            Value::Cons(ValueCons {
                car: SizedHolder(Cow::Borrowed(&Value::Bool(true))),
                cdr: SizedHolder(Cow::Borrowed(&Value::Bool(false))),
            })
        );
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::InvalidToken);
        assert_eq!(i.next().unwrap().unwrap_err().kind, ErrorKind::EndOfFile);
        assert!(i.next().is_none());
    }

    #[test]
    fn test_iterator() {
        let s = "() () ()";
        let mut num = 0;
        for v in s.chars().peekable().lisp_values() {
            num += 1;
            assert_eq!(v.unwrap(), Value::Nil);
        }
        assert_eq!(num, 3);
    }
}
