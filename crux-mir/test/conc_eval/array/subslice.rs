// FAIL: subslicing not yet supported on arrays

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let mut xs: [u32; 6] = [1, 2, 3, 4, 5, 6];

    let [_, rest @ ..] = xs;
    assert_eq!(rest, [2, 3, 4, 5, 6]);

    let [_, rest @ ..] = rest;
    assert_eq!(rest, [3, 4, 5, 6]);
    
    let [_, _, rest @ ..] = xs;
    assert_eq!(rest, [3, 4, 5, 6]);

    let [first @ .., _] = xs;
    assert_eq!(first, [1, 2, 3, 4, 5]);

    let [first @ .., _] = first;
    assert_eq!(first, [1, 2, 3, 4]);
    
    let [first @ .., _, _] = xs;
    assert_eq!(first, [1, 2, 3, 4]);

    let [_, middle @ .., _] = xs;
    assert_eq!(middle, [2, 3, 4, 5]);

    let [_, ref mut middle @ .., _] = xs;
    *middle = [5, 4, 3, 2];

    let [_, middle @ .., _] = xs;
    assert_eq!(middle, [5, 4, 3, 2]);
    assert_eq!(xs, [1, 5, 4, 3, 2, 6]);
}

fn main() {
    println!("{:?}", crux_test());
}
