extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() -> (i32, i32, i32) {
    let arr = <[i32; 3]>::symbolic("arr");
    let s = arr.as_slice();
    let s_p = s.as_ptr();

    for i in 0..3 {
        crucible_assume!(0 < s[i] && s[i] <= 10);
    }
    for i in 0..2 {
        crucible_assume!(s[i + 1] > s[i]);
    }
    crucible_assume!(s[0] + s[1] + s[2] == 6);

    let s = concretize(s);
    let s_p = concretize(s_p);
    (s[0], s[1], unsafe { *s_p.add(2) })
}

pub fn main() {
    println!("{:?}", crux_test());
}
