use std::env;
use std::process;

use crux_test_gen::{self, BranchingState};

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("usage: {} <grammar.txt>", args.get(0).map_or("crux-test-gen", |s| s));
        process::exit(1);
    }

    let cx = crux_test_gen::parse_grammar_from_file(&args[1]).unwrap();

    let mut bcx = BranchingState::new(0);
    while let Some((exp, mut rcx)) = crux_test_gen::expand_next(&cx, &mut bcx) {
        println!("{}", crux_test_gen::render_expansion(&mut rcx, &exp));
    }
}
