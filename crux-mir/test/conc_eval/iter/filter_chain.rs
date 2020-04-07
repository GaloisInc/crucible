
fn f(x: u8) -> u8 {
    let opt = Some((x, x));
    // This sort of chaining used to cause exponential growth in the size of the .mir file, with
    // the translation timing out around 5 levels of chaining.
    opt.into_iter()
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .filter(|&(a, b)| a == b)
        .for_each(|(a, b)| {});
    0
}

const ARG: u8 = 42;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u8 { f(ARG) }
