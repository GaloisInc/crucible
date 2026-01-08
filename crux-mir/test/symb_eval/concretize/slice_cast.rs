extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() {
    let a = <[u32; 1]>::symbolic("a");
    crucible_assume!(a[0] == 0x01010101);

    let b: &[u32] = &a;
    let c: *const [u32] = b;
    let d: *const [u8] = c as *const [u8];
    let e: &[u8] = unsafe { &*d };

    // We expect this test to fail at this call to `concretize`, since we'll be
    // trying to concretize a `u32`-based backing allocation at `u8`.
    let f: &[u8] = concretize(e);

    // Currently unreachable, but should succeed.
    crucible_assert!(f.len() == 1);
}

pub fn main() {
    println!("{:?}", crux_test());
}
