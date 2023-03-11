
#[derive(Clone, PartialEq, Eq)]
struct S;

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let x = (S, S);
    let y = x.clone();
    assert!(x == y);
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
