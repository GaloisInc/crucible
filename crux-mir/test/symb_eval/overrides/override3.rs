fn f(x: u8) -> () {
    // This call should be replaced by the test override
    let foo = crucible_i8("x");
    crucible_assert(x + 1 != x);
    ()
}

fn crucible_i8(x: &'static str) -> u8 {
    // The internal test override returns 1 from this instead of 2
    2
}

fn crucible_assert(cond: bool) -> () {
    ()
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
