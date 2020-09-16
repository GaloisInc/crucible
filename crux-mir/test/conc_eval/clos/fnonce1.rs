#![cfg_attr(not(with_main), no_std)]
/*
 where clauses are currently unsupported
*/

fn call_with_one<F>(some_closure: F) -> i32
    where F: FnOnce(i32) -> i32 {

    some_closure(1)
}

fn f (y:i32) -> i32 {

    call_with_one(|x| x + 2)

}

const ARG :i32 = 0;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> i32 { f(ARG) }
