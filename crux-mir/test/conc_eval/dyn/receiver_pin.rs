use std::pin::Pin;

trait TPin {
    fn m_pin(self: Pin<&Self>) -> u32;
}

impl TPin for u32 {
    fn m_pin(self: Pin<&Self>) -> u32 {
        *self
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    let d_pin1: Pin<&u32> = Pin::new(&27);
    let d_pin2: Pin<&dyn TPin> = d_pin1;
    d_pin2.m_pin()
}

fn main() {
    println!("{:?}", crux_test());
}
