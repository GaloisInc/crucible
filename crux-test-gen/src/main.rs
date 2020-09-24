use std::fmt::Display;
use std::process;
use clap::{App, Arg, ArgMatches};

use crux_test_gen;

fn parse_args() -> ArgMatches<'static> {
    App::new("crux-test-gen")
        .about("generate tests from a grammar")
        .arg(Arg::with_name("grammar")
             .takes_value(true)
             .value_name("GRAMMAR.TXT")
             .help("grammar file")
             .required(true))
        .arg(Arg::with_name("range")
             .long("range")
             .takes_value(true)
             .value_name("[START]:[END]")
             .help("only output when START <= expansion_counter < END"))
        .get_matches()
}

fn die(msg: impl Display) -> ! {
    eprintln!("{}", msg);
    process::exit(1);
}

macro_rules! die {
    ($($args:tt)*) => { die(format_args!($($args)*)) };
}

fn parse_range_endpoint(s: &str) -> Option<usize> {
    let s = s.trim();
    if s.len() == 0 {
        return None;
    }
    let x = s.parse()
        .unwrap_or_else(|e| die!("error parsing range endpoint {:?}: {}", s, e));
    Some(x)
}

fn parse_range(s: &str) -> (Option<usize>, Option<usize>) {
    let colon = s.find(':')
        .unwrap_or_else(|| die!("missing `:` in range {:?}", s));
    (
        parse_range_endpoint(&s[..colon]),
        parse_range_endpoint(&s[colon + 1 ..]),
    )
}

fn main() {
    let m = parse_args();

    let (range_start, range_end) = match m.value_of("range") {
        Some(s) => parse_range(s),
        None => (None, None),
    };

    let cx = crux_test_gen::parse_grammar_from_file(m.value_of_os("grammar").unwrap()).unwrap();

    let mut prologue = None;
    for s in crux_test_gen::iter_rendered(&cx, "prologue") {
        if prologue.is_some() {
            die!("expected at most one expansion for <<prologue>>");
        }
        prologue = Some(s);
    }
    if let Some(prologue) = prologue {
        println!("{}", prologue);
    }

    for (exp, mut rcx) in crux_test_gen::iter_expansions(&cx, "start") {
        let start_ok = range_start.map_or(true, |start| start <= rcx.counter);
        let end_ok = range_end.map_or(true, |end| rcx.counter < end);
        if start_ok && end_ok {
            println!("{}", crux_test_gen::render_expansion(&mut rcx, &exp));
        }
    }
}
