#[allow(unused_variables)]
fn crucible_i8(x: &'static str) -> i8 {
    2
}

#[allow(unused_variables)]
fn crucible_i16(x: &'static str) -> i16 {
    2
}

#[allow(unused_variables)]
fn crucible_i32(x: &'static str) -> i32 {
    2
}

#[allow(unused_variables)]
fn crucible_i64(x: &'static str) -> i64 {
    2
}

#[allow(unused_variables)]
fn crucible_u8(x: &'static str) -> u8 {
    2
}

#[allow(unused_variables)]
fn crucible_u16(x: &'static str) -> u16 {
    2
}

#[allow(unused_variables)]
fn crucible_u32(x: &'static str) -> u32 {
    2
}

#[allow(unused_variables)]
fn crucible_u64(x: &'static str) -> u64 {
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

#[allow(unused_variables)]
fn crucible_assume_impl(
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

macro_rules! crucible_assume {
    ($e:expr) => {
        crucible_assume_impl($e, stringify!($e), file!(), line!(), column!())
    };
}

fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    let foo = crucible_u64("foo");
    crucible_assume!(foo != 0);
    crucible_assert!(foo + 1 != 0);
    0
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
