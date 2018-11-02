#[allow(unused_variables)]
fn crucible_i8(x: &'static str) -> u8 {
    // The internal test override returns 1 from this instead of 2
    2
}

#[allow(unused_variables)]
fn crucible_assert_impl(
    cond: bool,
    cond_str: &'static str,
    file: &'static str,
    line: u32,
    col: u32,
) -> () {
    ()
}

macro_rules! crucible_assert {
    ($e:expr) => {
        crucible_assert_impl($e, stringify!($e), file!(), line!(), column!())
    };
}

#[allow(unused_variables)]
fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    let foo = crucible_i8("x");
    crucible_assert!(foo + 1 != foo);
    0
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
