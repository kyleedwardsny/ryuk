mod lisp {
    /// Attempts to cast a dyn reference to its concrete type
    pub trait CastTo<T> {
        fn cast_to(&self) -> Option<&T> { Option::None }
    }

    /// Attempts to cast a mut dyn reference to its concrete mut type
    pub trait CastToMut<T>: CastTo<T> {
        fn cast_to_mut(&mut self) -> Option<&mut T> { Option::None }
    }

    /// Extends all of the traits needed to be a first-class Lisp value
    pub trait Value<'a>:
        CastToMut<None> +
        CastToMut<Symbol<'a>> +
        CastToMut<Cons> {
    }

    /// A unit struct for no value
    pub struct None;

    impl CastTo<None> for None {
        fn cast_to(&self) -> Option<&None> { Option::Some(self) }
    }

    impl CastToMut<None> for None {
        fn cast_to_mut(&mut self) -> Option<&mut None> { Option::Some(self) }
    }

    impl<'a> CastTo<Symbol<'a>> for None { }
    impl<'a> CastToMut<Symbol<'a>> for None { }
    impl CastTo<Cons> for None { }
    impl CastToMut<Cons> for None { }

    impl<'a> Value<'a> for None { }

    /// A Lisp symbol
    pub struct Symbol<'a> {
        pub sym: &'a str,
    }

    impl<'a> CastTo<None> for Symbol<'a> { }
    impl<'a> CastToMut<None> for Symbol<'a> { }

    impl<'a> CastTo<Symbol<'a>> for Symbol<'a> {
        fn cast_to(&self) -> Option<&Symbol<'a>> { Option::Some(self) }
    }

    impl<'a> CastToMut<Symbol<'a>> for Symbol<'a> {
        fn cast_to_mut(&mut self) -> Option<&mut Symbol<'a>> { Option::Some(self) }
    }

    impl<'a> CastTo<Cons> for Symbol<'a> { }
    impl<'a> CastToMut<Cons> for Symbol<'a> { }

    impl<'a> Value<'a> for Symbol<'a> { }

    /// A cons value that references two other values in an arena
    pub struct Cons {
        pub car: u32,
        pub cdr: u32,
    }

    impl CastTo<None> for Cons { }
    impl CastToMut<None> for Cons { }
    impl<'a> CastTo<Symbol<'a>> for Cons { }
    impl<'a> CastToMut<Symbol<'a>> for Cons { }

    impl CastTo<Cons> for Cons {
        fn cast_to(&self) -> Option<&Cons> { Option::Some(self) }
    }

    impl CastToMut<Cons> for Cons {
        fn cast_to_mut(&mut self) -> Option<&mut Cons> { Option::Some(self) }
    }

    impl<'a> Value<'a> for Cons { }
}

#[cfg(test)]
mod test {
    use super::*;

    fn assert_cast_succeeds<T, F>(val: &dyn lisp::CastTo<T>, f: F) where
        F: Fn(&T) {
        match val.cast_to() {
            Option::Some(r) => f(r),
            _ => panic!("cast_to() failed"),
        }
    }

    fn assert_cast_fails<T>(val: &dyn lisp::CastTo<T>) {
        match val.cast_to() {
            Option::None => (),
            _ => panic!("cast_to() succeeded"),
        }
    }

    fn assert_cast_mut_succeeds<T, F>(val: &mut dyn lisp::CastToMut<T>, f: F) where
        F: Fn(&mut T) {
        match val.cast_to_mut() {
            Option::Some(r) => f(r),
            _ => panic!("cast_to_mut() failed"),
        }
    }

    fn assert_cast_mut_fails<T>(val: &mut dyn lisp::CastToMut<T>) {
        match val.cast_to_mut() {
            Option::None => (),
            _ => panic!("cast_to_mut() succeeded"),
        }
    }

    #[test]
    fn test_none() {
        let mut none = lisp::None;

        assert_cast_succeeds(&none, |_: &lisp::None| ());
        assert_cast_fails::<lisp::Symbol>(&none);
        assert_cast_fails::<lisp::Cons>(&none);

        assert_cast_mut_succeeds(&mut none, |_: &mut lisp::None| ());
        assert_cast_mut_fails::<lisp::Symbol>(&mut none);
        assert_cast_mut_fails::<lisp::Cons>(&mut none);
    }

    #[test]
    fn test_symbol() {
        let mut sym = lisp::Symbol { sym: "sym" };

        assert_cast_fails::<lisp::None>(&sym);
        assert_cast_succeeds(&sym, |r: &lisp::Symbol| assert_eq!(r.sym, "sym"));
        assert_cast_fails::<lisp::Cons>(&sym);

        assert_cast_mut_fails::<lisp::None>(&mut sym);
        assert_cast_mut_succeeds(&mut sym, |r: &mut lisp::Symbol| r.sym = "sym2");
        assert_eq!(sym.sym, "sym2");
        assert_cast_mut_fails::<lisp::Cons>(&mut sym);
    }

    #[test]
    fn test_cons() {
        let mut cons = lisp::Cons { car: 1, cdr: 2 };

        assert_cast_fails::<lisp::None>(&cons);
        assert_cast_fails::<lisp::Symbol>(&cons);
        assert_cast_succeeds(&cons, |r: &lisp::Cons| assert_eq!((r.car, r.cdr), (1, 2)));

        assert_cast_mut_fails::<lisp::None>(&mut cons);
        assert_cast_mut_fails::<lisp::Symbol>(&mut cons);
        assert_cast_mut_succeeds(&mut cons, |r: &mut lisp::Cons| { r.car = 3; r.cdr = 4 });
        assert_eq!((cons.car, cons.cdr), (3, 4));
    }
}
