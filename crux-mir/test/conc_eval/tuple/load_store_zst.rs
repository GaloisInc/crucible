fn my_replace<T: Clone>(r: &mut T, x: T) -> T {
    let old = (*r).clone();
    *r = x;
    old
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let mut x = ();
    my_replace(&mut x, ());
    let mut y = (1, ());
    my_replace(&mut y.1, ());
}

pub fn main() {
    println!("{:?}", crux_test());
}
