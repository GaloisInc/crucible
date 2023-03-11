#![cfg_attr(not(with_main), no_std)]
struct Data(u32);

trait MyEq {
    fn myeq (&self, other : &Self) -> bool;
}

impl MyEq for Data {
    fn myeq (&self, other: &Data) -> bool {
        self.0 == other.0
    }
}

fn f(_: ()) -> bool {
    let d = Data(32);
    d.myeq(&d)
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> bool { f(ARG) }
