fn h<T>(x :T) -> T { x }

fn g<T>(x :T) -> T { h (x) }

fn f (x : u32) -> u32 {
    1 + g (x)
}

const ARG :u32 = 0;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
