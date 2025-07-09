//! Test various forms of field access for custom dynamically-sized types which
//! hold other custom dynamically-sized types

struct MyInnerDST<T: ?Sized> {
    info: usize,
    data: T,
}

impl<T> MyInnerDST<T> {
    fn new(info: usize, data: T) -> Self {
        Self { info, data }
    }
}

struct MyOuterDST<T: ?Sized> {
    info: usize,
    data: MyInnerDST<T>,
}

impl<T> MyOuterDST<T> {
    fn new(info: usize, data: MyInnerDST<T>) -> Self {
        Self { info, data }
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    let original_inner_datum: usize = 2;
    let original_inner_data: [usize; 3] = [1, original_inner_datum, 3];
    let original_inner_info: usize = 0;
    let original_outer_info: usize = 4;
    let sized_inner: MyInnerDST<[usize; 3]> =
        MyInnerDST::new(original_inner_info, original_inner_data);
    let sized_outer: MyOuterDST<[usize; 3]> = MyOuterDST::new(original_outer_info, sized_inner);

    let dynamic_outer: &MyOuterDST<[usize]> = &sized_outer;

    let mut good = true;

    // Access MyOuterDST::info
    let outer_info: usize = dynamic_outer.info;
    good &= outer_info == original_outer_info;

    // Access MyOuterDST::data
    let dynamic_inner: &MyInnerDST<[usize]> = &dynamic_outer.data;

    // Access MyInnerDST::info
    let inner_info_1: usize = dynamic_inner.info;
    let inner_info_2: usize = dynamic_outer.data.info;
    good &= inner_info_1 == original_inner_info;
    good &= inner_info_1 == inner_info_2;

    // Access MyInnerDST::data
    let inner_data_1: &[usize] = &dynamic_inner.data;
    let inner_data_2: &[usize] = &dynamic_outer.data.data;
    good &= inner_data_1 == original_inner_data;
    good &= inner_data_1 == inner_data_2;

    // Access MyInnerDST::data[1]
    let inner_datum_1: usize = inner_data_1[1];
    let inner_datum_2: usize = inner_data_2[1];
    let inner_datum_3: usize = dynamic_inner.data[1];
    let inner_datum_4: usize = dynamic_outer.data.data[1];
    good &= inner_datum_1 == original_inner_datum;
    good &= inner_datum_1 == inner_datum_2;
    good &= inner_datum_2 == inner_datum_3;
    good &= inner_datum_3 == inner_datum_4;

    assert!(good);
}

pub fn main() {
    println!("{:?}", crux_test());
}
