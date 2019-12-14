mod lisp {
    use std::collections::HashMap;
    use std::io::{Read, Result};
    use std::ops::Index;

    /// Optionally cast to a type
    pub trait CastTo<T: ?Sized> {
        fn do_cast(&self) -> Option<&T> {
            Option::None
        }
    }

    /// A Lisp value
    pub trait Value:
        CastTo<dyn NoneValue> + CastTo<dyn SymbolValue> + CastTo<dyn ConsValue>
    {
    }

    //// Generic function to cast a value to another value
    pub fn cast_to_value<'a, T>(from: &'a (dyn Value + 'static)) -> Option<&'a T>
    where
        dyn Value: CastTo<T>,
        T: ?Sized,
    {
        CastTo::<T>::do_cast(from)
    }

    /// No value
    pub trait NoneValue {}

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
        pub const fn new() -> None {
            None
        }
    }

    impl NoneValue for None {}

    impl CastTo<dyn NoneValue> for None {
        fn do_cast(&self) -> Option<&(dyn NoneValue + 'static)> {
            Option::Some(self)
        }
    }

    impl CastTo<dyn SymbolValue> for None {}
    impl CastTo<dyn ConsValue> for None {}

    impl Value for None {}

    /// A Lisp symbol with static lifetime
    pub struct StaticSymbol {
        sym: &'static str,
    }

    impl StaticSymbol {
        /// Create a static symbol
        pub const fn new(sym: &'static str) -> StaticSymbol {
            StaticSymbol { sym }
        }
    }

    impl SymbolValue for StaticSymbol {
        fn name(&self) -> &str {
            self.sym
        }
    }

    impl CastTo<dyn NoneValue> for StaticSymbol {}

    impl CastTo<dyn SymbolValue> for StaticSymbol {
        fn do_cast(&self) -> Option<&(dyn SymbolValue + 'static)> {
            Option::Some(self)
        }
    }

    impl CastTo<dyn ConsValue> for StaticSymbol {}

    impl Value for StaticSymbol {}

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

    impl CastTo<dyn NoneValue> for OwnedSymbol {}

    impl CastTo<dyn SymbolValue> for OwnedSymbol {
        fn do_cast(&self) -> Option<&(dyn SymbolValue + 'static)> {
            Option::Some(self)
        }
    }

    impl CastTo<dyn ConsValue> for OwnedSymbol {}

    impl Value for OwnedSymbol {}

    /// A cons value
    pub struct Cons {
        car: u32,
        cdr: u32,
    }

    impl Cons {
        pub const fn new(car: u32, cdr: u32) -> Cons {
            Cons { car, cdr }
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

    impl CastTo<dyn NoneValue> for Cons {}
    impl CastTo<dyn SymbolValue> for Cons {}

    impl CastTo<dyn ConsValue> for Cons {
        fn do_cast(&self) -> Option<&(dyn ConsValue + 'static)> {
            Option::Some(self)
        }
    }

    impl Value for Cons {}

    /// An arena of values
    pub trait Arena: Index<u32, Output = dyn Value> {}

    /// A mutable arena of values
    pub trait ArenaMut: Arena {
        fn create(&mut self, val: Box<dyn Value>) -> u32;
    }

    /// A statically compiled arena of values
    pub struct ConstArena {
        pub values: &'static [&'static dyn Value],
    }

    impl Arena for ConstArena {}

    impl Index<u32> for ConstArena {
        type Output = dyn Value;

        fn index(&self, index: u32) -> &'static Self::Output {
            self.values[index as usize]
        }
    }

    /// An arena of values that uses a HashMap to store its values
    pub struct HashMapArena {
        values: HashMap<u32, Box<dyn Value>>,
        next: u32,
    }

    impl HashMapArena {
        /// Create a new HashMapArena
        pub fn new() -> HashMapArena {
            HashMapArena {
                values: HashMap::<u32, Box<dyn Value>>::new(),
                next: 0,
            }
        }
    }

    impl Arena for HashMapArena {}

    impl Index<u32> for HashMapArena {
        type Output = dyn Value;

        fn index(&self, index: u32) -> &Self::Output {
            &(**self.values.get(&index).expect("Could not find value"))
        }
    }

    impl ArenaMut for HashMapArena {
        fn create(&mut self, val: Box<dyn Value>) -> u32 {
            let index = self.next;
            self.values.insert(index, val);
            self.next += 1;
            index
        }
    }

    /// Read a single object from a stream
    pub fn read(arena: &mut impl ArenaMut, reader: &mut impl Read) -> Result<u32> {
        let mut pb = syntax::PutBack::new(reader);
        syntax::read(arena, &mut pb)
    }

    mod syntax {
        use super::*;
        use std::io::{Error, ErrorKind, Read, Result};

        pub struct PutBack<'a, R: Read> {
            reader: &'a mut R,
            last: Option<char>,
        }

        impl<'a, R: Read> PutBack<'a, R> {
            pub fn new(reader: &'a mut R) -> PutBack<R> {
                PutBack {
                    reader,
                    last: Option::None,
                }
            }

            pub fn read_char(&mut self) -> Result<char> {
                let result = match self.last {
                    Option::Some(l) => Result::Ok(l),
                    _ => {
                        let mut buf = [0 as u8];
                        match self.reader.read_exact(&mut buf) {
                            Result::Ok(()) => Result::Ok(buf[0] as char),
                            Result::Err(e) => Result::Err(e),
                        }
                    }
                };

                self.last = Option::None;
                result
            }

            pub fn put_back(&mut self, c: char) {
                assert!(self.last.is_none());
                self.last = Option::Some(c);
            }

            pub fn skip_whitespace(&mut self) -> Result<()> {
                loop {
                    let c = self.read_char()?;
                    if c != ' ' && c != '\n' {
                        self.put_back(c);
                        return Result::Ok(());
                    }
                }
            }
        }

        fn read_symbol<R: Read>(arena: &mut impl ArenaMut, pb: &mut PutBack<R>) -> Result<u32> {
            let mut name = String::new();
            loop {
                match pb.read_char() {
                    Result::Ok(c) => match c {
                        'a'..='z' => name.push(c),
                        _ => {
                            pb.put_back(c);
                            break;
                        }
                    },
                    Result::Err(e) => match e.kind() {
                        ErrorKind::UnexpectedEof => break,
                        _ => return Result::Err(e),
                    },
                }
            }

            Result::Ok(arena.create(Box::new(OwnedSymbol::new(name))))
        }

        fn read_delimited<R: Read>(
            arena: &mut impl ArenaMut,
            pb: &mut PutBack<R>,
            end: char,
        ) -> Option<Result<u32>> {
            if let Result::Err(e) = pb.skip_whitespace() {
                return Option::Some(Result::Err(e));
            }

            match pb.read_char() {
                Result::Ok(c) => {
                    if c == end {
                        return Option::None;
                    }
                    pb.put_back(c);

                    Option::Some(read(arena, pb))
                }
                Result::Err(e) => Option::Some(Result::Err(e)),
            }
        }

        fn read_list<R: Read>(arena: &mut impl ArenaMut, pb: &mut PutBack<R>) -> Result<u32> {
            match read_delimited(arena, pb, ')') {
                Option::None => Result::Ok(arena.create(Box::new(None::new()))),
                Option::Some(r) => {
                    let car = r?;
                    let cdr = read_list(arena, pb)?;
                    Result::Ok(arena.create(Box::new(Cons::new(car, cdr))))
                }
            }
        }

        pub fn read<R: Read>(arena: &mut impl ArenaMut, pb: &mut PutBack<R>) -> Result<u32> {
            pb.skip_whitespace()?;
            let c = pb.read_char()?;
            match c {
                'a'..='z' => {
                    pb.put_back(c);
                    read_symbol(arena, pb)
                }
                '(' => read_list(arena, pb),
                _ => Result::Err(Error::new(
                    ErrorKind::InvalidData,
                    format!("Invalid character: '{}'", c),
                )),
            }
        }
    }

    #[cfg(test)]
    mod test {
        use super::*;
        use std::io::ErrorKind;

        #[test]
        fn test_put_back_none() {
            let mut reader = "123".as_bytes();
            let mut pb = syntax::PutBack::new(&mut reader);
            assert_eq!(pb.read_char().expect("Failed to read"), '1');
            assert_eq!(pb.read_char().expect("Failed to read"), '2');
            assert_eq!(pb.read_char().expect("Failed to read"), '3');
            assert_eq!(
                pb.read_char().expect_err("Successfully read").kind(),
                ErrorKind::UnexpectedEof
            );
        }

        #[test]
        fn test_put_back_some() {
            let mut reader = "23".as_bytes();
            let mut pb = syntax::PutBack::new(&mut reader);
            pb.put_back('1');
            assert_eq!(pb.read_char().expect("Failed to read"), '1');
            assert_eq!(pb.read_char().expect("Failed to read"), '2');
            assert_eq!(pb.read_char().expect("Failed to read"), '3');
            assert_eq!(
                pb.read_char().expect_err("Successfully read").kind(),
                ErrorKind::UnexpectedEof
            );
        }

        #[test]
        fn test_put_back_middle() {
            let mut reader = "13".as_bytes();
            let mut pb = syntax::PutBack::new(&mut reader);
            assert_eq!(pb.read_char().expect("Failed to read"), '1');
            pb.put_back('2');
            assert_eq!(pb.read_char().expect("Failed to read"), '2');
            assert_eq!(pb.read_char().expect("Failed to read"), '3');
            assert_eq!(
                pb.read_char().expect_err("Successfully read").kind(),
                ErrorKind::UnexpectedEof
            );
        }

        #[test]
        #[should_panic]
        fn test_put_back_error() {
            let mut reader = "3".as_bytes();
            let mut pb = syntax::PutBack::new(&mut reader);
            pb.put_back('2');
            pb.put_back('1');
        }

        #[test]
        fn test_put_back_skip_whitespace() {
            let mut reader = "Hell o \nworld!\n".as_bytes();
            let mut pb = syntax::PutBack::new(&mut reader);
            pb.skip_whitespace().expect("Failed to skip whitespace");
            assert_eq!(pb.read_char().expect("Failed to read"), 'H');
            pb.skip_whitespace().expect("Failed to skip whitespace");
            assert_eq!(pb.read_char().expect("Failed to read"), 'e');
            assert_eq!(pb.read_char().expect("Failed to read"), 'l');
            assert_eq!(pb.read_char().expect("Failed to read"), 'l');
            pb.skip_whitespace().expect("Failed to skip whitespace");
            assert_eq!(pb.read_char().expect("Failed to read"), 'o');
            pb.skip_whitespace().expect("Failed to skip whitespace");
            assert_eq!(pb.read_char().expect("Failed to read"), 'w');
            assert_eq!(pb.read_char().expect("Failed to read"), 'o');
            assert_eq!(pb.read_char().expect("Failed to read"), 'r');
            assert_eq!(pb.read_char().expect("Failed to read"), 'l');
            assert_eq!(pb.read_char().expect("Failed to read"), 'd');
            assert_eq!(pb.read_char().expect("Failed to read"), '!');
            assert_eq!(
                pb.skip_whitespace().expect_err("Successfully read").kind(),
                ErrorKind::UnexpectedEof
            );
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
        assert!(
            cast_to_value::<dyn SymbolValue>(&v).is_none(),
            "Cast to SymbolValue succeeded"
        );
        assert!(
            cast_to_value::<dyn ConsValue>(&v).is_none(),
            "Cast to ConsValue succeeded"
        );
    }

    #[test]
    fn test_static_symbol() {
        let v = StaticSymbol::new("sym");
        assert!(
            cast_to_value::<dyn NoneValue>(&v).is_none(),
            "Cast to NoneValue succeeded"
        );
        assert_eq!(
            cast_to_value::<dyn SymbolValue>(&v)
                .expect("Cast to SymbolValue failed")
                .name(),
            "sym"
        );
        assert!(
            cast_to_value::<dyn ConsValue>(&v).is_none(),
            "Cast to ConsValue succeeded"
        );
    }

    #[test]
    fn test_owned_symbol() {
        let v = OwnedSymbol::new("sym".to_string());
        assert!(
            cast_to_value::<dyn NoneValue>(&v).is_none(),
            "Cast to NoneValue succeeded"
        );
        assert_eq!(
            cast_to_value::<dyn SymbolValue>(&v)
                .expect("Cast to SymbolValue failed")
                .name(),
            "sym"
        );
        assert!(
            cast_to_value::<dyn ConsValue>(&v).is_none(),
            "Cast to ConsValue succeeded"
        );
    }

    #[test]
    fn test_cons() {
        let v = Cons::new(1, 2);
        assert!(
            cast_to_value::<dyn NoneValue>(&v).is_none(),
            "Cast to NoneValue succeeded"
        );
        assert!(
            cast_to_value::<dyn SymbolValue>(&v).is_none(),
            "Cast to SymbolValue succeeded"
        );
        let c = cast_to_value::<dyn ConsValue>(&v).expect("Cast to ConsValue failed");
        assert_eq!(c.car(), 1);
        assert_eq!(c.cdr(), 2);
    }

    fn test_arena(arena: &dyn Arena, index: u32) {
        let cons = cast_to_value::<dyn ConsValue>(&arena[index]).expect("Not a cons");
        assert_eq!(
            cast_to_value::<dyn SymbolValue>(&arena[cons.car()])
                .expect("Not a symbol")
                .name(),
            "sym"
        );
        let cons = cast_to_value::<dyn ConsValue>(&arena[cons.cdr()]).expect("Not a cons");
        cast_to_value::<dyn NoneValue>(&arena[cons.car()]).expect("Not none");
        cast_to_value::<dyn NoneValue>(&arena[cons.cdr()]).expect("Not none");
    }

    #[test]
    fn test_const_arena() {
        const ARENA: ConstArena = ConstArena {
            values: &[
                &None::new() as &dyn Value,
                &Cons::new(2, 3) as &dyn Value,
                &StaticSymbol::new("sym") as &dyn Value,
                &Cons::new(0, 0) as &dyn Value,
            ],
        };

        test_arena(&ARENA, 1);
    }

    #[test]
    fn test_hashmap_arena() {
        let mut arena = HashMapArena::new();

        let n = arena.create(Box::new(None::new()));
        let s = arena.create(Box::new(OwnedSymbol::new("sym".to_string())));
        let c2 = arena.create(Box::new(Cons::new(n, n)));
        let c1 = arena.create(Box::new(Cons::new(s, c2)));

        test_arena(&arena, c1);
    }

    #[test]
    fn test_read_symbol() {
        let mut arena = HashMapArena::new();
        let mut reader = " symbol  ".as_bytes();

        let r = read(&mut arena, &mut reader).expect("Failed to read");
        let sym = cast_to_value::<SymbolValue>(&arena[r]).expect("Not a symbol");
        assert_eq!(sym.name(), "symbol");
    }

    #[test]
    fn test_read_none() {
        let mut arena = HashMapArena::new();
        let mut reader = " (  )  ".as_bytes();

        let r = read(&mut arena, &mut reader).expect("Failed to read");
        cast_to_value::<NoneValue>(&arena[r]).expect("Not None");
    }

    #[test]
    fn test_read_list() {
        let mut arena = HashMapArena::new();
        let mut reader = " ( hello ( world sym) () )   ".as_bytes();

        let r = read(&mut arena, &mut reader).expect("Failed to read");
        let cons = cast_to_value::<ConsValue>(&arena[r]).expect("Not a cons");
        let car = cast_to_value::<SymbolValue>(&arena[cons.car()]).expect("Not a symbol");
        assert_eq!(car.name(), "hello");
        let cdr = cast_to_value::<ConsValue>(&arena[cons.cdr()]).expect("Not a cons");
        {
            let car = cast_to_value::<ConsValue>(&arena[cdr.car()]).expect("Not a cons");
            {
                let car = cast_to_value::<SymbolValue>(&arena[car.car()]).expect("Not a symbol");
                assert_eq!(car.name(), "world");
            }
            let cdr = cast_to_value::<ConsValue>(&arena[car.cdr()]).expect("Not a cons");
            let car = cast_to_value::<SymbolValue>(&arena[cdr.car()]).expect("Not a symbol");
            assert_eq!(car.name(), "sym");
            cast_to_value::<NoneValue>(&arena[cdr.cdr()]).expect("Not none");
        }
        let cdr = cast_to_value::<ConsValue>(&arena[cdr.cdr()]).expect("Not a cons");
        cast_to_value::<NoneValue>(&arena[cdr.car()]).expect("Not none");
        cast_to_value::<NoneValue>(&arena[cdr.cdr()]).expect("Not none");
    }
}
