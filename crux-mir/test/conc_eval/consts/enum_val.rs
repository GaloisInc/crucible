#[cfg_attr(crux, crux_test)]
fn crux_test() -> Option<bool> {
    // As of nightly-2020-03-22, this struct expression gets constant-folded down to `Scalar(2)`.
    // There is now code in mir-json to extract the fields in a form
    // crux-mir can interpret.
    None
}

pub fn main() {
    println!("{:?}", crux_test());
}
