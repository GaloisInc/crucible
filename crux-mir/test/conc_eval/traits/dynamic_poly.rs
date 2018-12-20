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

fn f(_: ()) -> u32 {
    let d = Data(32);
    d.foo(3) + h(&d) 
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
