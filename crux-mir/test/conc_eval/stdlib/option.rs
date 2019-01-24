
pub enum Opt<T> {
    /// No value
    N,
    /// Some value `T`
    S(T)
}

use Opt::*;

impl<T> Opt<T> {
  fn or_else<F: FnOnce() -> Opt<T>>(self:Self, f: F) -> Opt<T> {
    match self {
        S(_) => self,
        N => f(),
    }
  } 
}

fn g () -> Opt<u32> {
    S (3)
}

fn f (y : u32) -> bool { 
    let x: Opt<u32> = S(y);
    x.or_else(g);
    true
}

const ARG: u32 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
