extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() -> (i32, i32, i32) {
    let arr = <[i32; 3]>::symbolic("arr");

    for i in 0..3 {
        crucible_assume!(0 < arr[i] && arr[i] <= 10);
    }
    for i in 0..2 {
        crucible_assume!(arr[i + 1] > arr[i]);
    }
    crucible_assume!(arr[0] + arr[1] + arr[2] == 6);

    let arr = concretize(arr);
    (arr[0], arr[1], arr[2])
}

pub fn main() {
    println!("{:?}", crux_test());
}
