#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
// Tests deriving for stdlib trait

#[derive(Default)]
struct SomeOptions {
    foo: i32,
    bar: i16,
}

fn f(x : i32) -> bool {
    let options: SomeOptions = Default::default();
    return x == options.foo
}

const ARG : i32 = 0;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> bool { f(ARG) }
