
fn f<T>(x :T) -> T { x }

const ARG :u32 = 0;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
