// ----------------------------------------------------------------------
#[allow(unused_variables)]
fn crucible_u32(x: &'static str) -> u32 {
    2
}

#[allow(unused_variables)]
fn crucible_i32(x: &'static str) -> i32 {
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
