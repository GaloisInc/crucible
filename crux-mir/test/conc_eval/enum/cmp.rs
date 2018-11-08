#![no_implicit_prelude]

pub enum Ordering {
    /// An ordering where a compared value is equal [to another].
    Equal = 0,
    /// An ordering where a compared value is greater [than another].
    Greater = 1,
    /// An ordering where a compared value is less [than another].
    Less = -1,
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
    let z = (y.reverse() as i32);
    return z
}


pub const ARG : i32 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
