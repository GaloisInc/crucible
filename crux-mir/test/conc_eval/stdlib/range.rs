
pub struct Rng<Idx> {
    /// The lower bound of the range (inclusive).
    
    pub start: Idx,
    /// The upper bound of the range (exclusive).
    
    pub end: Idx,
}


fn f (x : i32) -> i32 {
    let y = Rng { start: x, end: 10 } ;
    return y.end;
}

const ARG : i32 = 2;


#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
