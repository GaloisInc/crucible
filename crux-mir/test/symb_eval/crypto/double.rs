extern crate crucible;
use crucible::*;

// ----------------------------------------------------------------------


fn double_ref(x : u32) -> u32 {
    return x * 2;
}

fn double_imp(x : u32) -> u32 {
    return x << 1;
}


fn f (_arg : u32) -> bool {
    let a0 = crucible_u32("a0");
    crucible_assert!(double_ref(a0) == double_imp(a0));
    true
}

const ARG: u32 = 27;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
