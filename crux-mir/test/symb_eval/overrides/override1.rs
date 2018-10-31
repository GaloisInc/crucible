fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    x + one()
}

fn one() -> u8 {
    // The internal test override returns 1 from this instead of 2
    2
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
