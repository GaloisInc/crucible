#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let mut xs: [u32; 6] = [1, 2, 3, 4, 5, 6];
    let ys: &mut [u32] = &mut xs;

    let [_, rest @ ..] = ys else { panic!() };
    assert_eq!(*rest, [2, 3, 4, 5, 6]);

    let [_, rest @ ..] = rest else { panic!() };
    assert_eq!(*rest, [3, 4, 5, 6]);
    
    let [_, _, rest @ ..] = ys else { panic!() };
    assert_eq!(*rest, [3, 4, 5, 6]);

    let [first @ .., _] = ys else { panic!() };
    assert_eq!(*first, [1, 2, 3, 4, 5]);

    let [first @ .., _] = first else { panic!() };
    assert_eq!(*first, [1, 2, 3, 4]);
    
    let [first @ .., _, _] = ys else { panic!() };
    assert_eq!(*first, [1, 2, 3, 4]);

    let [_, middle @ .., _] = ys else { panic!() };
    assert_eq!(*middle, [2, 3, 4, 5]);

    for i in middle.iter_mut() {
        *i ^= 7;
    }
    assert_eq!(*middle, [5, 4, 3, 2]);
    assert_eq!(ys, [1, 5, 4, 3, 2, 6]);
    assert_eq!(xs, [1, 5, 4, 3, 2, 6]);
}

fn main() {
    println!("{:?}", crux_test());
}
