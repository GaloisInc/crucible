
fn g<T> (x : Option<T>) -> T {
    match x {
        Some(y) => y,
        None    => g(x),
    }
}

fn f (y : u32) -> u32 { 
    let x: Option<u32> = Some(0);
    return g(x);
}

const ARG: u32 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
