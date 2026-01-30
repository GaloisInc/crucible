pub trait Trait {
    fn method(&self) -> u32;
}

impl Trait for u32 {
    fn method(&self) -> u32 { *self }
}

const X: &dyn Trait = &0u32;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> u32 {
    X.method()
}

pub fn main() {
    println!("{:?}", crux_test());
}
