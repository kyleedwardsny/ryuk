use std::borrow::{Cow, ToOwned};
use std::rc::Rc;

// Workaround for a bug in rustc. See
// https://github.com/rust-lang/rust/issues/47032.
#[derive(Debug)]
pub struct SizedHolder<T>(pub T);

#[derive(Debug, PartialEq)]
pub struct ValueSymbol(pub Cow<'static, str>);

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
            Value::Symbol(ValueSymbol(name)) => Value::Symbol(ValueSymbol(name.clone())),
            Value::Cons(ValueCons { car, cdr }) => Value::Cons(ValueCons {
                car: SizedHolder(car.0.clone()),
                cdr: SizedHolder(cdr.0.clone()),
            }),
            Value::Bool(b) => Value::Bool(*b),
        })
    }
}

pub type ValueRef = Cow<'static, Value>;
