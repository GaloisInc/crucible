//! Test simple introduction (and dropping) of `Arc`, which exercises custom
//! dynamically-sized type support.

use std::sync::Arc;

trait Foo {}

impl Foo for usize {}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let x: Arc<dyn Foo> = Arc::new(3usize);
}

fn main() {
    println!("{:?}", crux_test());
}
