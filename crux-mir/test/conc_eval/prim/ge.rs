// FAIL: 

fn f(x: u32) -> bool {
    x >= 2
}

const ARG: u32 = 2;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
