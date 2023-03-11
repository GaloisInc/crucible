#![cfg_attr(not(with_main), no_std)]
// Make sure that we can include negative numbers in C-style enums

pub enum Ordering {
    /// An ordering where a compared value is equal [to another].
    Equal = 0,
    /// An ordering where a compared value is greater [than another].
    Greater = 1,
    /// An ordering where a compared value is less [than another].
    Less = -23,
}

use self::Ordering::*;

impl Ordering {

    pub fn reverse(self) -> Ordering {
        match self {
            Less => Greater,
            Equal => Equal,
            Greater => Less,
        }
    }

}


pub fn f (x : i32) -> i32 {
    let y = Greater;
    let z = match y {
            Less => Greater,
            Equal => Equal,
            Greater => Less,
            };
    return (z as i32);
}


pub const ARG : i32 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> i32 { f(ARG) }
