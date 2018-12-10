// FAIL: Doesn't know how to call default yet

#[derive(Default)]
struct SomeOptions {
    foo: i32,
    bar: f32,
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
