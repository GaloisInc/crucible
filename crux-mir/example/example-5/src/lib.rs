// Original file from:
// https://github.com/model-checking/kani/tree/main/docs/src/tutorial

fn get_wrapped(i: usize, a: &[u32]) -> u32 {
    if a.len() == 0 {
        return 0;
    }

    let idx = i % a.len() + 1;
    return a[idx];
}

#[cfg(crux)]
mod crux_test {
    use super::*;
    extern crate crucible;
    use self::crucible::*;

    #[crux::test]
    fn bound_check() {
        const LIMIT: usize = 10;
        let size = LIMIT;
        let i = usize::symbolic("i");
        let array: Vec<u32> = vec![1; size];
        get_wrapped(i, &array);
    }
}