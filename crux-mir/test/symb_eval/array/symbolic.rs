extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() {
    let mut arr = <[i32; 3]>::symbolic("arr");
    crucible_assume!(0 <= arr[0] && arr[0] <= 5);
    crucible_assume!(0 <= arr[1] && arr[1] <= 5);
    crucible_assume!(0 <= arr[2] && arr[2] <= 5);
    let sum = arr.into_iter().sum::<i32>();
    crucible_assert!(0 <= sum && sum <= 15);
}
