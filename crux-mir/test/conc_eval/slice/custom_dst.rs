//! Test introduction and per-field elimination of custom dynamically-sized
//! struct types holding slices.

struct MyDST<T: ?Sized> {
    info: usize,
    data: T,
}

impl<T> MyDST<T> {
    fn new(info: usize, data: T) -> Self {
        Self { info, data }
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> (usize, usize) {
    let sized: MyDST<[usize; 3]> = MyDST::new(0, [1, 2, 3]);

    // Test sized -> unsized casting behavior
    let dynamic: &MyDST<[usize]> = &sized;
    
    // Test sized field access
    let info: usize = dynamic.info;
    
    // Test unsized field access
    let data: &[usize] = &dynamic.data;
    
    (info, data.len())
}

pub fn main() {
    println!("{:?}", crux_test());
}
