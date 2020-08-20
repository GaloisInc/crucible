use std::env;
use std::process;

use crux_test_gen;

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("usage: {} <grammar.txt>", args.get(0).map_or("crux-test-gen", |s| s));
        process::exit(1);
    }

    let cx = crux_test_gen::parse_grammar_from_file(&args[1]).unwrap();

    let mut prologue = None;
    for s in crux_test_gen::iter_rendered(&cx, "prologue") {
        assert!(
            prologue.is_none(),
            "expected at most one expansion for <<prologue>>",
        );
        prologue = Some(s);
    }
    if let Some(prologue) = prologue {
        println!("{}", prologue);
    }

    for s in crux_test_gen::iter_rendered(&cx, "start") {
        println!("{}", s);
    }
}
