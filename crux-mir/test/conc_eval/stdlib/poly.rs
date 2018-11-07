
fn g<T>(x :T) -> T { x }

fn f (x : u32) -> u32 {
    g (x)
}

const ARG :u32 = 0;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
