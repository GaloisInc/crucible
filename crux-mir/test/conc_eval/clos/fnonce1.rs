

fn call_with_one<F>(some_closure: F) -> i32
    where F: FnOnce(i32) -> i32 {

    some_closure(1)
}

fn f (y:i32) -> i32 {

    call_with_one(|x| x + 2)

}

const ARG :i32 = 0;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
