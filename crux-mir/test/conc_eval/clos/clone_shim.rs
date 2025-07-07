// A regression test for #1455. Ensure that crucible-mir is able to translate
// clone shims for function pointers (f1) and closures (f2).

pub fn f1(x: fn() -> i32) -> i32 {
    let y = x.clone();
    y()
}

pub fn f2(x: i32) -> i32 {
    let y = || x;
    let z = y.clone();
    z()
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> i32 {
    f1(|| 42) + f2(42)
}

pub fn main() {
    println!("{:?}", crux_test());
}
