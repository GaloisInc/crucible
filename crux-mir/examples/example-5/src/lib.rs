// Original file from:
// https://github.com/model-checking/kani/tree/main/docs/src/tutorial

fn find_midpoint(low: u32, high: u32) -> u32 {
    return (low + high) / 2;
}

#[cfg(crux)]
mod crux_test {
    use super::*;
    extern crate crucible;
    use self::crucible::*;

    #[crux::test]
    fn midpoint_overflow() {
        let a = u32::symbolic("a");
        let b = u32::symbolic("b");
        find_midpoint(a, b);
    }
}