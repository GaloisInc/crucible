#[cfg_attr(crux, crux::test)]
pub fn f() -> i32 {
    let b = Box::new([1, 2, 3]);
    let s: Box<[i32]> = b;
    s[1]
}


pub fn main() { println!("{:?}", f()); }
