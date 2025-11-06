// use std::fmt::Debug;

// pub struct C<T: ?Sized> {
//     pub x: u32,
//     pub y: T,
// }

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    assert_eq!(4, size_of_val::<i32>(&0));
    assert_eq!(8, size_of_val::<i64>(&0));
    assert_eq!(0, size_of_val::<[i32]>(&[]));
    assert_eq!(4, size_of_val::<[i32]>(&[0]));
    assert_eq!(8, size_of_val::<[i32]>(&[0, 1]));
    assert_eq!(0, size_of_val::<[i64]>(&[]));
    assert_eq!(8, size_of_val::<[i64]>(&[0]));
    assert_eq!(16, size_of_val::<[i64]>(&[0, 1]));
    assert_eq!(0, size_of_val::<str>(&""));
    assert_eq!(1, size_of_val::<str>(&"r"));
    assert_eq!(2, size_of_val::<str>(&"ro"));
    assert_eq!(4, size_of_val::<str>(&"roș")); // Note that ș occupies two bytes, not one!
    assert_eq!(5, size_of_val::<str>(&"roșu"));

    // TODO(#1614): The following are not currently supported:

    // Trait objects
    // crucible_assert!(0 == size_of_val::<dyn Debug>(x));

    // Custom DSTs with a slice as the last field
    // let sized: C<[u8; 8]> = C {
    //     x: 17,
    //     y: [0; 8],
    // };
    // let dynamic: &C<[u8]> = &sized;
    // crucible_assert!(12 == size_of_val(dynamic));

    // Custom DSTs with a trait object as the last field
    // let sized: C<()> = C {
    //     x: 17,
    //     y: (),
    // };
    // let dynamic: &C<dyn Debug> = &sized;
    // crucible_assert!(4 == size_of_val(dynamic));
}

pub fn main() {
    println!("{:?}", crux_test());
}
