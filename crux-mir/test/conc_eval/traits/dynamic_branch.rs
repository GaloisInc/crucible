#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]

struct Data(u32);

trait Foo {
    fn foo (&self) -> u32;
}

impl Foo for Data {
    fn foo (&self) -> u32 {
        return 1;
    }
}

impl Foo for () {
    fn foo (&self) -> u32 {
        return 2;
    }
}


fn fun(f: &Foo) -> u32 {
   return f.foo();
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    let u = ();
    if true {
        fun(&d)
    } else {
        fun(&u)
    }
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
