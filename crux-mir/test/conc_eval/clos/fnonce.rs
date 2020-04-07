#![cfg_attr(not(with_main), no_std)]


fn call_with_one<F>(some_closure: &F) -> bool
    where F: Fn(i32) -> bool {

    some_closure(1)
}

fn f (y:i32) -> bool {

    call_with_one(&|x| x < y)

}

const ARG :i32 = 0;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> bool { f(ARG) }
