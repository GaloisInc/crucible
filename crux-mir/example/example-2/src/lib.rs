// Original file from:
// https://github.com/model-checking/kani/tree/main/docs/src/tutorial

fn estimate_size(x: u32) -> u32 {
    if x < 256 {
        if x < 128 {
            return 1;
        } else {
            return 3;
        }
    } else if x < 1024 {
        if x > 1022 {
            // TODO: uncomment once https://github.com/GaloisInc/crucible/issues/1431
            // is fixed
            //panic!("Oh no, a failing corner case!");
            unsafe { return *(0 as *const u32) };
        } else {
            return 5;
        }
    } else {
        if x < 2048 {
            return 7;
        } else {
            return 9;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn it_works() {
        assert_eq!(estimate_size(1024), 7);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(10000))]
        #[test]
        fn doesnt_crash(x: u32) {
            estimate_size(x);
        }
    }
}

#[cfg(crux)]
mod crux_test {
    use super::*;
    extern crate crucible;
    use self::crucible::*;

    #[crux::test]
    fn check_estimate_size() {
        let x: u32 = u32::symbolic("x");
        estimate_size(x);
    }
}
