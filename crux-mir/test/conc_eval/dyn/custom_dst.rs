//! Test introduction and per-field elimination of custom dynamically-sized
//! struct types holding trait objects.

struct MyDST<T: ?Sized> {
    info: usize,
    data: T,
}

impl<T> MyDST<T> {
    fn new(info: usize, data: T) -> Self {
        Self { info, data }
    }
}

trait Foo {
    fn bar(&self) -> usize;
}

impl Foo for usize {
    fn bar(&self) -> usize {
        *self + 1
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> (usize, usize) {
    let sized: MyDST<usize> = MyDST::new(1, 2);

    // Test sized -> unsized casting behavior
    let dynamic: &MyDST<dyn Foo> = &sized;

    // Test sized field access
    let info: usize = dynamic.info;

    // Test unsized field access
    let data: &dyn Foo = &dynamic.data;

    (info, data.bar())
}

pub fn main() {
    println!("{:?}", crux_test());
}
