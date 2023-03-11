#![cfg_attr(not(with_main), no_std)]
struct Data(u32);

trait Foo<A> {
    fn foo (&self, x: A) -> A;
}

impl<A> Foo<A> for Data {
    fn foo (&self, x:A) -> A {
        return x;
    }
}



fn h(f: &Foo<u32>) -> u32 {
   f.foo(2)
}


fn k<F>(f : F) -> u32 where F : Foo<u32> {
    f.foo(3)
}

fn app<F,G>(x : &G, y:F) -> u32
  where G : Fn(F) -> u32 {
    x(y)
}


fn f(_: ()) -> u32 {
    let d = Data(32);
    app(&k,d)
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> u32 { f(ARG) }
