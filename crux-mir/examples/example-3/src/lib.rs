// Original file from:
// https://github.com/model-checking/kani/tree/main/docs/src/tutorial

fn estimate_size(x: u32) -> u32 {
    assert!(x < 4096);

    if x < 256 {
        if x < 128 {
            return 1;
        } else {
            return 3;
        }
    } else if x < 1024 {
        if x > 1022 {
            return 4;
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
        fn doesnt_crash(x in 0..4095u32) {
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
    fn verify_success() {
        let x: u32 = u32::symbolic("x");
        crucible_assume!(x < 4096);
        let y = estimate_size(x);
        assert!(y < 10);
    }

    #[crux::test]
    fn will_fail() {
        let x: u32 = u32::symbolic("x");
        let y = estimate_size(x);
    }
}
