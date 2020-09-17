#[derive(Debug)]
struct Foo {
    x: bool,
}

#[cfg_attr(crux, crux_test)]
fn crux_test() -> Foo {
    // As of nightly-2020-03-22, this struct expression gets constant-folded down to `Scalar(1)`.
    // There is now code in mir-json to extract the fields in a form
    // crux-mir can interpret.
    Foo { x: true }
}

pub fn main() {
    println!("{:?}", crux_test());
}
