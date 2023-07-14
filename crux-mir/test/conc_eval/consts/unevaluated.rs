const FOO: usize = 5;

fn f(xs: [i32; FOO]) -> i32 {
    xs[2]
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    f([0, 1, 2, 3, 4])
}

pub fn main() {
    println!("{:?}", crux_test());
}
