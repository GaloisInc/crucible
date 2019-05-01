// FAIL: string literal

fn f(x: (bool,bool)) -> bool {
    let s = "hello";
    s.len() > 3
}

const ARG: (bool,bool) = (true, true);

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
