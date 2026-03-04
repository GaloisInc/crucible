trait TBox {
    fn m_box(self: Box<Self>) -> u32;
}

impl TBox for u32 {
    fn m_box(self: Box<Self>) -> u32 {
        *self
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    let d_box1: Box<u32> = Box::new(27);
    let d_box2: Box<dyn TBox> = d_box1;
    d_box2.m_box()
}

fn main() {
    println!("{:?}", crux_test());
}
