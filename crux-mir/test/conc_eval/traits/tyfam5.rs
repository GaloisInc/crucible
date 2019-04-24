pub enum Opt<T> {
    /// No value
    N,
    /// Some value `T`
    S(T)
}

use Opt::*;
    
pub trait Ir {
    type Item;
    fn dummy();
}

impl<T: Ir> Ir for Opt<T> {
    type Item = <T as Ir>::Item;
    fn dummy() {}
}

// Stub to avoid "Could not find cfg: f"
const ARG: i32 = 1;
fn f(arg: i32) {}


#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
