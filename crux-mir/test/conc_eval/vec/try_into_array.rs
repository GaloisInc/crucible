use std::convert::TryInto;

#[cfg_attr(crux, crux::test)]
fn test() -> Result<[i32; 4], Vec<i32>> {
    vec![1, 2, 3, 4].try_into()
}

fn main() {
    println!("{:?}", test());
}
