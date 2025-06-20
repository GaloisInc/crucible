// Original file from:
// https://github.com/model-checking/kani/tree/main/docs/src/tutorial

fn initialize_prefix(length: usize, buffer: &mut [u8]) {
    // Let's just ignore invalid calls
    if length >= buffer.len() {
        return;
    }

    for i in 0..=length {
        buffer[i] = 0;
    }
}


#[cfg(crux)]
mod crux_test {
    use super::*;
    extern crate crucible;
    use self::crucible::*;

    #[crux::test]
    fn check_initialize_prefix() {
        const LIMIT: usize = 10;
        let mut buffer: [u8; LIMIT] = [1; LIMIT];

        let length = usize::symbolic("x");
        initialize_prefix(length, &mut buffer);
    }
}
