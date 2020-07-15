use std::env;
use std::process;

use crux_test_gen::{self, Continuation};

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("usage: {} <grammar.txt>", args.get(0).map_or("crux-test-gen", |s| s));
        process::exit(1);
    }

    let cx = crux_test_gen::parse_grammar_from_file(&args[1]).unwrap();

    let mut conts = vec![Continuation::new(0)];
    while let Some((exp, mut unify)) = crux_test_gen::expand_next(&cx, &mut conts) {
        println!("{}", crux_test_gen::render_expansion(&cx, &mut unify, &exp));
    }
}
