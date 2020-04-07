#![cfg_attr(not(with_main), no_std)]
fn f(x: (bool,bool)) -> bool {
    let y = 0.0;
    let s = "hello";
    // this is not actually an array literal
    let a = [0,1,2];
    // this is not actually a tuple literal
    let t = (0.1, 2);
    let (b,c) = t;
    y > 0.1 && s.len() > 3 && a.len() > 1 && c > 2
}

const ARG: (bool,bool) = (true, true);

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG))
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> bool { f(ARG) }
