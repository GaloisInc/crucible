fn f(mut x: i32) {
    while x < 10 {
        x += 1;
    }
}

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    f(0);
    1
}

/*
fn f<I: Iterator<Item = i32>>(mut iterator: I) {
    while x < 10 {
        x += 1;
    }
}

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    f(0..10);
    1
}
*/

pub fn main() {
    println!("{:?}", crux_test());
}
