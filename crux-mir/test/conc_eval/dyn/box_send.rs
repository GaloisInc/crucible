// FAIL: no drop method available to `drop_in_place` override

// This runs into `mir-json`'s lack of support for dropping trait objects with
// no principal trait. (`Send` is a marker trait, and doesn't constitute a
// principal trait on its own.) See
// https://github.com/GaloisInc/mir-json/pull/138#discussion_r2183694072.

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let x: Box<dyn Send> = Box::new(3usize);
    drop(x);
}

fn main() {
    println!("{:?}", crux_test());
}
