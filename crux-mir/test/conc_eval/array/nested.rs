use std::mem::transmute;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    let xs: [[[u16; 1]; 2]; 4] = [[[1], [1]], [[2], [3]], [[5], [8]], [[13], [21]]];

    let xs2 = unsafe { transmute::<_, [[[u16; 4]; 2]; 1]>(xs) };
    assert_eq!(xs2[0][0], [1, 1, 2, 3]);
    assert_eq!(xs2[0][1], [5, 8, 13, 21]);

    let xs3 = unsafe { transmute::<_, [u16; 8]>(xs2) };
    assert_eq!(xs3, [1, 1, 2, 3, 5, 8, 13, 21]);

    let xs4 = &xs3[2..6];
    assert_eq!(xs4.len(), 4);
    assert_eq!(xs4[0], 2);
    assert_eq!(xs4[1], 3);

    let xs5 = &xs4[2] as *const u16;
    assert_eq!(unsafe { *(xs5.offset(-2)) }, 2);
    assert_eq!(unsafe { *(xs5.offset(-1)) }, 3);
    assert_eq!(unsafe { *xs5 }, 5);
    assert_eq!(unsafe { *(xs5.offset(1)) }, 8);

    // We can move past either end of the slice `xs4`, as long as we remain
    // within the bounds of the backing array `xs3`
    assert_eq!(unsafe { *(xs5.offset(2)) }, 13);
    assert_eq!(unsafe { *(xs5.offset(3)) }, 21);
    assert_eq!(unsafe { *(xs5.offset(-3)) }, 1);
}

pub fn main() {
    println!("{:?}", crux_test());
}
