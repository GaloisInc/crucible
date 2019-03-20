// FAIL: Default trait (temporarily) not included in mir-lib

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
fn main() {
    println!("{:?}", f(ARG))
}
