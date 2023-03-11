#![cfg_attr(not(with_main), no_std)]

struct Data(u32);


trait Foo {
    fn foo (&self) -> u32;
    fn bar (&self) -> u32;
}


impl Foo for Data {
    fn foo (&self) -> u32 {
        return self.bar()
    }

    fn bar (&self) -> u32 {
        return 1;
    }
}



fn fun(f: &Foo) -> u32 {
   f.foo()
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    fun(&d)
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> u32 { f(ARG) }
