extern crate crucible;
use crucible::*;

fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    x + one()
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
