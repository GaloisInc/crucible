fn h<T>(x :T) -> T { x }

fn f (x : u32) -> u32 {
    h (|y| y + 1)  (x)
}

const ARG :u32 = 2;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
