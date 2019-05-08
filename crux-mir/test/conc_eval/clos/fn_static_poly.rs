fn call_with_one<T,F:Fn(T)->T>(some_closure: &F, arg:T) -> T {

    some_closure(arg)

}

fn f (y:i32) -> i32 {

    call_with_one(&|x| x + y, 1)

}

const ARG :i32 = 2;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
