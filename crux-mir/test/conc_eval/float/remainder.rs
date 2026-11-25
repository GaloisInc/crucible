// A regression test for #1919.

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let x: f64 = 5.0;
    let y: f64 = 3.0;
    assert_eq!(x % y, 2.0);
}

fn main() {
    println!("{:?}", crux_test());
}
