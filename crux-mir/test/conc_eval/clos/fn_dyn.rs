// FAIL: call_once shim (in `dyn Fn` vtable)
#![cfg_attr(not(with_main), no_std)]
fn call_with_one(some_closure: &dyn Fn(i32) -> i32) -> i32 {
    some_closure(1)
}

fn f (y:i32) -> i32 {

    call_with_one(&|x| x + y)

}

const ARG :i32 = 2;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> i32 { f(ARG) }
