mod lisp {
    use std::any::Any;
    use std::collections::HashMap;
    use std::ops::Index;

    /// Optionally cast to a type
    pub trait CastTo<'t, 'f: 't, T: ?Sized + 't> {
        fn do_cast(&'f self) -> Option<&'t T> { Option::None }
    }

    /// A Lisp value
    pub trait Value<'t, 'f: 't>:
        CastTo<'t, 'f, dyn NoneValue> +
        CastTo<'t, 'f, dyn SymbolValue> +
        CastTo<'t, 'f, dyn ConsValue> {
    }

    /// Generic function to cast a value to another value
    pub fn cast_to_value<'t, 'f: 't, T>(from: &'f dyn Value<'t, 'f>) -> Option<&'t T> where
        dyn Value<'t, 'f> + 'f: CastTo<'t, 'f, T>,
        T: ?Sized + 't {
        CastTo::<'t, 'f, T>::do_cast(from)
    }

    /// No value
    pub trait NoneValue { }

    /// A Lisp symbol
    pub trait SymbolValue {
        /// Get the name of the symbol
        fn name(&self) -> &str;
    }

    /// A cons value that references two other values in an arena
    pub trait ConsValue {
        /// Get the car of the cons
        fn car(&self) -> u32;

        /// Get the cdr of the cons
        fn cdr(&self) -> u32;
    }

    /// A unit struct for no value
    pub struct None;

    impl None {
        /// Create a None
        pub fn new() -> None {
            None
        }
    }

    impl NoneValue for None { }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn NoneValue> for None {
        fn do_cast(&'f self) -> Option<&'t dyn NoneValue> { Option::Some(self) }
    }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn SymbolValue> for None { }
    impl<'t, 'f: 't> CastTo<'t, 'f, dyn ConsValue> for None { }

    impl<'t, 'f: 't> Value<'t, 'f> for None { }

    /// A Lisp symbol with static lifetime
    pub struct StaticSymbol {
        sym: &'static str,
    }

    impl StaticSymbol {
        /// Create a static symbol
        pub fn new(sym: &'static str) -> StaticSymbol {
            StaticSymbol { sym }
        }
    }

    impl SymbolValue for StaticSymbol {
        fn name(&self) -> &str {
            self.sym
        }
    }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn NoneValue> for StaticSymbol { }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn SymbolValue> for StaticSymbol {
        fn do_cast(&self) -> Option<&dyn SymbolValue> { Option::Some(self) }
    }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn ConsValue> for StaticSymbol { }

    impl<'t, 'f: 't> Value<'t, 'f> for StaticSymbol { }

    /// A Lisp symbol with ownership
    pub struct OwnedSymbol {
        sym: String,
    }

    impl OwnedSymbol {
        /// Create an owned symbol
        pub fn new(sym: String) -> OwnedSymbol {
            OwnedSymbol { sym }
        }
    }

    impl SymbolValue for OwnedSymbol {
        fn name(&self) -> &str {
            &self.sym
        }
    }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn NoneValue> for OwnedSymbol { }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn SymbolValue> for OwnedSymbol {
        fn do_cast(&self) -> Option<&dyn SymbolValue> { Option::Some(self) }
    }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn ConsValue> for OwnedSymbol { }

    impl<'t, 'f: 't> Value<'t, 'f> for OwnedSymbol { }

    /// A cons value
    pub struct Cons {
        car: u32,
        cdr: u32,
    }

    impl Cons {
        pub fn new(car: u32, cdr: u32) -> Cons {
            Cons {
                car,
                cdr,
            }
        }
    }

    impl ConsValue for Cons {
        fn car(&self) -> u32 {
            self.car
        }

        fn cdr(&self) -> u32 {
            self.cdr
        }
    }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn NoneValue> for Cons { }
    impl<'t, 'f: 't> CastTo<'t, 'f, dyn SymbolValue> for Cons { }

    impl<'t, 'f: 't> CastTo<'t, 'f, dyn ConsValue> for Cons {
        fn do_cast(&self) -> Option<&dyn ConsValue> { Option::Some(self) }
    }

    impl<'t, 'f: 't> Value<'t, 'f> for Cons { }

    /// An arena of values
    pub trait Arena: Index<u32, Output = dyn Any> { }

    /// A mutable arena of values
    pub trait ArenaMut: Arena {
        fn create(&mut self, val: Box<dyn Any>) -> u32;
    }

    /// A statically compiled arena of values
    pub struct ConstArena {
        pub values: &'static [&'static dyn Any],
    }

    impl Arena for ConstArena { }

    impl Index<u32> for ConstArena {
        type Output = dyn Any;

        fn index(&self, index: u32) -> &Self::Output {
            self.values[index as usize]
        }
    }

    /// An arena of values that uses a HashMap to store its values
    pub struct HashMapArena {
        values: HashMap<u32, Box<dyn Any>>,
        next: u32,
    }

    impl HashMapArena {
        /// Create a new HashMapArena
        pub fn new() -> HashMapArena {
            HashMapArena {
                values: HashMap::<u32, Box<dyn Any>>::new(),
                next: 0,
            }
        }
    }

    impl Arena for HashMapArena { }

    impl Index<u32> for HashMapArena {
        type Output = dyn Any;

        fn index(&self, index: u32) -> &Self::Output {
            &(**self.values.get(&index).expect("Could not find value"))
        }
    }

    impl ArenaMut for HashMapArena {
        fn create(&mut self, val: Box<dyn Any>) -> u32 {
            let index = self.next;
            self.values.insert(index, val);
            self.next += 1;
            index
        }
    }
}

#[cfg(test)]
mod test {
    use super::lisp::*;

    #[test]
    fn test_none() {
        let v = None::new();
        cast_to_value::<dyn NoneValue>(&v).expect("Cast to NoneValue failed");
        assert!(cast_to_value::<dyn SymbolValue>(&v).is_none(), "Cast to SymbolValue succeeded");
        assert!(cast_to_value::<dyn ConsValue>(&v).is_none(), "Cast to ConsValue succeeded");
    }

    #[test]
    fn test_static_symbol() {
        let v = StaticSymbol::new("sym");
        assert!(cast_to_value::<dyn NoneValue>(&v).is_none(), "Cast to NoneValue succeeded");
        assert_eq!(cast_to_value::<dyn SymbolValue>(&v).expect("Cast to SymbolValue failed").name(), "sym");
        assert!(cast_to_value::<dyn ConsValue>(&v).is_none(), "Cast to ConsValue succeeded");
    }

    #[test]
    fn test_owned_symbol() {
        let v = OwnedSymbol::new("sym".to_string());
        assert!(cast_to_value::<dyn NoneValue>(&v).is_none(), "Cast to NoneValue succeeded");
        assert_eq!(cast_to_value::<dyn SymbolValue>(&v).expect("Cast to SymbolValue failed").name(), "sym");
        assert!(cast_to_value::<dyn ConsValue>(&v).is_none(), "Cast to ConsValue succeeded");
    }

    #[test]
    fn test_cons() {
        let v = Cons::new(1, 2);
        assert!(cast_to_value::<dyn NoneValue>(&v).is_none(), "Cast to NoneValue succeeded");
        assert!(cast_to_value::<dyn SymbolValue>(&v).is_none(), "Cast to SymbolValue succeeded");
        let c = cast_to_value::<dyn ConsValue>(&v).expect("Cast to ConsValue failed");
        assert_eq!(c.car(), 1);
        assert_eq!(c.cdr(), 2);
    }

    /*fn test_arena(arena: &dyn Arena, index: u32) {
        let cons = arena[index].downcast_ref::<dyn ConsValue>().expect("Not a cons");
        assert_eq!(arena[cons.car].downcast_ref::<dyn SymbolValue>().expect("Not a symbol").sym, "sym");
        let cons = arena[cons.cdr].downcast_ref::<dyn ConsValue>().expect("Not a cons");
        arena[cons.car].downcast_ref::<dyn NoneValue>().expect("Not none");
        arena[cons.cdr].downcast_ref::<dyn NoneValue>().expect("Not none");
    }

    #[test]
    fn test_const_arena() {
        const ARENA: lisp::ConstArena = lisp::ConstArena {
            values: &[
                &lisp::None as &dyn lisp::Value,
                &lisp::Cons {
                    car: 2,
                    cdr: 3,
                } as &dyn lisp::Value,
                &lisp::Symbol {
                    sym: "sym",
                } as &dyn lisp::Value,
                &lisp::Cons {
                    car: 0,
                    cdr: 0,
                } as &dyn lisp::Value,
            ],
        };

        test_arena(&ARENA, 1);
    }

    #[test]
    fn test_hashmap_arena() {
        use lisp::ArenaMut;
        let mut arena = lisp::HashMapArena::new();

        let n = arena.create(lisp::None);
        let s = arena.create(lisp::Symbol { sym: "sym" });
        let c2 = arena.create(lisp::Cons { car: n, cdr: n });
        let c1 = arena.create(lisp::Cons { car: s, cdr: c2 });

        test_arena(&arena, c1);
    }*/
}
