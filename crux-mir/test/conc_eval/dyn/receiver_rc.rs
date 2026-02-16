use std::rc::Rc;

trait TRc {
    fn m_rc(self: Rc<Self>) -> u32;
}

impl TRc for u32 {
    fn m_rc(self: Rc<Self>) -> u32 {
        *self
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    let d_rc1: Rc<u32> = Rc::new(27);
    let d_rc2: Rc<dyn TRc> = d_rc1;
    d_rc2.m_rc()
}

fn main() {
    println!("{:?}", crux_test());
}
