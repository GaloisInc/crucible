// use std::fmt::Debug;

// pub struct C<T: ?Sized> {
//     pub x: u32,
//     pub y: T,
// }

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    assert_eq!(4, align_of_val::<i32>(&0));
    assert_eq!(8, align_of_val::<i64>(&0));
    assert_eq!(4, align_of_val::<[i32]>(&[]));
    assert_eq!(4, align_of_val::<[i32]>(&[0]));
    assert_eq!(4, align_of_val::<[i32]>(&[0, 1]));
    assert_eq!(8, align_of_val::<[i64]>(&[]));
    assert_eq!(8, align_of_val::<[i64]>(&[0]));
    assert_eq!(8, align_of_val::<[i64]>(&[0, 1]));
    assert_eq!(1, align_of_val::<str>(&""));
    assert_eq!(1, align_of_val::<str>(&"r"));
    assert_eq!(1, align_of_val::<str>(&"ro"));

    // TODO(#1614): The following are not currently supported:

    // Trait objects
    // assert_eq!(1, align_of_val::<dyn Debug>(&()));

    // Custom DSTs with a slice as the last field
    // let sized: C<[u8; 8]> = C {
    //     x: 17,
    //     y: [0; 8],
    // };
    // let dynamic: &C<[u8]> = &sized;
    // assert_eq!(4, align_of_val(dynamic));

    // Custom DSTs with a trait object as the last field
    // let sized: C<()> = C {
    //     x: 17,
    //     y: (),
    // };
    // let dynamic: &C<dyn Debug> = &sized;
    // assert_eq!(4, align_of_val(dynamic));
}

pub fn main() {
    println!("{:?}", crux_test());
}
