

fn call_with_one<F>(some_closure: &F) -> bool
    where F: Fn(i32) -> bool {

    some_closure(1)
}

fn f (y:i32) -> bool {

    call_with_one(&|x| x < y)

}

const ARG :i32 = 0;

#[cfg(with_main)] 
fn main() {
    println!("{:?}", f(ARG))
}
