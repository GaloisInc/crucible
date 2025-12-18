// A regression test for #1502, which ensures that crucible-mir can handle a
// Vec containing a zero-sized type (e.g., S).

#[derive(Clone, Copy, Debug)]
struct S;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> S {
    let v: Vec<S> = vec![S];
    v[0]
}

pub fn main() {
    println!("{:?}", crux_test());
}
