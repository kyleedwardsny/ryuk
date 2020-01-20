macro_rules! eq_match {
    ($lhs: expr, $rhs:expr, { $(($lpat:pat, $rpat:pat) => $result:expr,)* }) => {
        match $lhs {
            $($lpat => match $rhs {
                $rpat => $result,
                _ => false,
            }),*
        }
    };
}

#[macro_use]
pub mod value;
pub mod algo;
pub mod env;
pub mod error;
pub mod list;
