#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    // `vec::from_elem` (which backs the `vec![x; N]` macro syntax) special-cases `x == 0` to use
    // `alloc_zeroed`.  It expects the allocator to initialize the vector to all zeros, and doesn't
    // initialize anything itself.
    let x: Vec<i32> = vec![0; 10];
    x[9]
}

pub fn main() {
    println!("{:?}", crux_test());
}
