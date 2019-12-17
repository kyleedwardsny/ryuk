use std::borrow::Cow;
use std::fmt::Formatter;
use std::io::BufRead;
use std::ops::Deref;
use std::rc::Rc;

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
    pub car: ValueRef,
    pub cdr: ValueRef,
}

impl PartialEq for ValueCons {
    fn eq(&self, other: &Self) -> bool {
        *self.car == *other.car && *self.cdr == *other.cdr
    }
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Nil,
    Symbol(ValueSymbol),
    Cons(ValueCons),
    Bool(bool),
}

#[derive(Debug)]
pub enum ValueRef {
    Static(&'static Value),
    Owned(Rc<Value>),
}

impl Deref for ValueRef {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        match self {
            ValueRef::Static(v) => v,
            ValueRef::Owned(v) => &*v,
        }
    }
}

pub trait LispRead {
    fn read_value(&mut self) -> Result<Value>;
}

impl<R: BufRead> LispRead for R {
    fn read_value(&mut self) -> Result<Value> {
        match syntax::read_impl(self)? {
            syntax::ReadImplResult::Value(v) => Result::Ok(v),
            syntax::ReadImplResult::InvalidToken(t) => Result::Err(Error::new(
                ErrorKind::InvalidToken,
                format!("Invalid token: '{}'", t),
            )),
        }
    }
}

mod syntax {
    use super::*;

    fn is_token_char(c: char) -> bool {
        if let 'a'..='z' | '0'..='9' = c {
            true
        } else {
            false
        }
    }

    fn skip_whitespace(reader: &mut impl BufRead) -> Result<()> {
        loop {
            let mut num = 0;
            let buf = reader.fill_buf()?;
            if buf.len() == 0 {
                return Result::Ok(());
            }
            for b in buf {
                let c = *b as char;
                if c == ' ' || c == '\n' {
                    num += 1;
                } else {
                    reader.consume(num);
                    return Result::Ok(());
                }
            }
            reader.consume(num);
        }
    }

    enum ReadDelimitedResult {
        Value(Value),
        EndDelimiter,
    }

    fn read_delimited(reader: &mut impl BufRead, delimiter: char) -> Result<ReadDelimitedResult> {
        skip_whitespace(reader)?;
        let buf = reader.fill_buf()?;
        if buf.len() > 0 {
            if buf[0] as char == delimiter {
                reader.consume(1);
                Result::Ok(ReadDelimitedResult::EndDelimiter)
            } else {
                match read_impl(reader)? {
                    ReadImplResult::Value(v) => Result::Ok(ReadDelimitedResult::Value(v)),
                    ReadImplResult::InvalidToken(t) => Result::Err(Error::new(
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

    fn read_list(reader: &mut impl BufRead) -> Result<Value> {
        match read_delimited(reader, ')')? {
            ReadDelimitedResult::Value(v) => Result::Ok(Value::Cons(ValueCons {
                car: ValueRef::Owned(Rc::new(v)),
                cdr: ValueRef::Owned(Rc::new(read_list(reader)?)),
            })),
            ReadDelimitedResult::EndDelimiter => Result::Ok(Value::Nil),
        }
    }

    fn read_macro(reader: &mut impl BufRead) -> Result<Value> {
        let buf = reader.fill_buf()?;
        if buf.len() > 0 {
            match read_token(reader)? {
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

    fn read_token(reader: &mut impl BufRead) -> Result<ReadTokenResult> {
        let mut token = String::new();

        loop {
            let buf = reader.fill_buf()?;
            let mut num = 0;
            let mut done = true;
            for b in buf {
                let c = *b as char;
                done = false;
                if is_token_char(c) {
                    num += 1;
                    token.push(c);
                } else {
                    done = true;
                    break;
                }
            }
            reader.consume(num);
            if done {
                break;
            }
        }

        let mut valid = false;
        for c in token.chars() {
            if c != '.' {
                valid = true;
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
    }

    pub fn read_impl(reader: &mut impl BufRead) -> Result<ReadImplResult> {
        skip_whitespace(reader)?;
        let buf = reader.fill_buf()?;
        if buf.len() > 0 {
            let c = buf[0] as char;
            if c == '(' {
                reader.consume(1);
                Result::Ok(ReadImplResult::Value(read_list(reader)?))
            } else if c == '#' {
                reader.consume(1);
                Result::Ok(ReadImplResult::Value(read_macro(reader)?))
            } else if is_token_char(c) {
                match read_token(reader)? {
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
            Result::Err(Error::new(
                ErrorKind::EndOfFile,
                "End of file reached".to_string(),
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_symbol() {
        let mut s = b"sym sym2\nsym3  \n   sym4" as &[u8];
        assert_eq!(
            s.read_value().unwrap(),
            Value::Symbol(ValueSymbol {
                name: Cow::Borrowed("sym")
            })
        );
        assert_eq!(
            s.read_value().unwrap(),
            Value::Symbol(ValueSymbol {
                name: Cow::Borrowed("sym2")
            })
        );
        assert_eq!(
            s.read_value().unwrap(),
            Value::Symbol(ValueSymbol {
                name: Cow::Borrowed("sym3")
            })
        );
        assert_eq!(
            s.read_value().unwrap(),
            Value::Symbol(ValueSymbol {
                name: Cow::Borrowed("sym4")
            })
        );
        assert_eq!(s.read_value().unwrap_err().kind, ErrorKind::EndOfFile);
    }

    #[test]
    fn test_read_bool() {
        let mut s = b"#t #f\n#t  " as &[u8];
        assert_eq!(s.read_value().unwrap(), Value::Bool(true));
        assert_eq!(s.read_value().unwrap(), Value::Bool(false));
        assert_eq!(s.read_value().unwrap(), Value::Bool(true));
        assert_eq!(s.read_value().unwrap_err().kind, ErrorKind::EndOfFile);
    }

    #[test]
    fn test_read_list() {
        let mut s = b"(s1 s2 s3)(s4\n s5 s6 ) ( s7 () s8) (#t #f)" as &[u8];
        assert_eq!(
            s.read_value().unwrap(),
            Value::Cons(ValueCons {
                car: ValueRef::Static(&Value::Symbol(ValueSymbol {
                    name: Cow::Borrowed("s1")
                })),
                cdr: ValueRef::Static(&Value::Cons(ValueCons {
                    car: ValueRef::Static(&Value::Symbol(ValueSymbol {
                        name: Cow::Borrowed("s2")
                    })),
                    cdr: ValueRef::Static(&Value::Cons(ValueCons {
                        car: ValueRef::Static(&Value::Symbol(ValueSymbol {
                            name: Cow::Borrowed("s3")
                        })),
                        cdr: ValueRef::Static(&Value::Nil),
                    })),
                })),
            })
        );
        assert_eq!(
            s.read_value().unwrap(),
            Value::Cons(ValueCons {
                car: ValueRef::Static(&Value::Symbol(ValueSymbol {
                    name: Cow::Borrowed("s4")
                })),
                cdr: ValueRef::Static(&Value::Cons(ValueCons {
                    car: ValueRef::Static(&Value::Symbol(ValueSymbol {
                        name: Cow::Borrowed("s5")
                    })),
                    cdr: ValueRef::Static(&Value::Cons(ValueCons {
                        car: ValueRef::Static(&Value::Symbol(ValueSymbol {
                            name: Cow::Borrowed("s6")
                        })),
                        cdr: ValueRef::Static(&Value::Nil),
                    })),
                })),
            })
        );
        assert_eq!(
            s.read_value().unwrap(),
            Value::Cons(ValueCons {
                car: ValueRef::Static(&Value::Symbol(ValueSymbol {
                    name: Cow::Borrowed("s7")
                })),
                cdr: ValueRef::Static(&Value::Cons(ValueCons {
                    car: ValueRef::Static(&Value::Nil),
                    cdr: ValueRef::Static(&Value::Cons(ValueCons {
                        car: ValueRef::Static(&Value::Symbol(ValueSymbol {
                            name: Cow::Borrowed("s8")
                        })),
                        cdr: ValueRef::Static(&Value::Nil),
                    })),
                })),
            })
        );
        assert_eq!(
            s.read_value().unwrap(),
            Value::Cons(ValueCons {
                car: ValueRef::Static(&Value::Bool(true)),
                cdr: ValueRef::Static(&Value::Cons(ValueCons {
                    car: ValueRef::Static(&Value::Bool(false)),
                    cdr: ValueRef::Static(&Value::Nil),
                })),
            })
        );
        assert_eq!(s.read_value().unwrap_err().kind, ErrorKind::EndOfFile);
    }
}
