extern crate crucible;
use crucible::Symbolic as _;

#[crux::test]
fn test() {
    let mut xs: [[u16; 2]; 2] = [[1, 2], [3, 4]];
    let i = usize::symbolic_where("i", |&i| i < xs.len());
    xs[i] = [0, 0];
}
