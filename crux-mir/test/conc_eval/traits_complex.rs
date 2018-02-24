use std::env;

#[cfg(with_main)]
fn main() {
   let args: Vec<String> = env::args().collect();

   let choice = &args[1];
   let d = Data(32);
   let s = String::from("hello");
   if choice == "1" { println!("{}", fun(&d));}
   else {println!("{}",fun(&s));}
}


struct Data(u32);

trait Foo {
    fn foo (&self) -> u32;
}

impl Foo for Data {
    fn foo (&self) -> u32 {
        return 1;
    }
}

impl Foo for String {
    fn foo (&self) -> u32 {
        return 2;
    }
}


fn fun(f: &Foo) -> u32 {
   return f.foo();
}
