use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::{self, File};
use std::io::{self, Read, BufRead, BufReader, Seek, SeekFrom};
use std::path::Path;
use std::str::FromStr;

use crux_test_gen;

/// Evaluate each grammar in `examples/*.txt`, checking that the actual output matches the expected
/// output included in the grammar file.
#[test]
fn run_examples() {
    eprintln!("{:?}", env::current_dir());
    let ok = run_all_in_dir("example").unwrap();
    assert!(ok);
}

fn run_all_in_dir<P: AsRef<Path>>(path: P) -> io::Result<bool> {
    let mut ok = true;

    let mut entries = fs::read_dir(path)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let path = entry.path();
        let name: Option<&str> = path.file_name().and_then(|os| os.to_str());
        let name = match name {
            Some(x) => x,
            None => continue,
        };
        if name.starts_with(".") || !name.ends_with(".txt") {
            continue;
        }

        let ft = entry.file_type()?;
        if ft.is_file() {
            ok &= run_one(&path)?;
        } else if ft.is_dir() {
            ok &= run_all_in_dir(&path)?;
        } else if ft.is_symlink() {
            let meta = path.metadata()?;
            if meta.is_file() {
                ok &= run_one(&path)?;
            } else if meta.is_dir() {
                ok &= run_all_in_dir(&path)?;
            } else {
                continue;
            }
        } else {
            continue;
        }
    }

    Ok(ok)
}

fn run_one(path: &Path) -> io::Result<bool> {
    macro_rules! die {
        ($($args:tt)*) => {{
            eprintln!($($args)*);
            return Ok(false);
        }};
    }

    // Parse output lines.  

    // Collected lines for each output.
    let mut output_lines: HashMap<usize, Vec<String>> = HashMap::new();
    // Which outputs had an `output X is empty` line
    let mut empty_outputs: HashSet<usize> = HashSet::new();
    // Whether we saw a `no outputs` line
    let mut no_outputs: bool = false;
    let mut saw_indexed: bool = false;
    let mut saw_unindexed: bool = false;
    let mut skip_test: bool = false;

    let mut f = BufReader::new(File::open(&path)?);
    for line in f.by_ref().lines() {
        let line = line?;
        if let Some(tail) = take_prefix(&line, "// output") {
            if let Some(index_str) = take_suffix(tail, "is empty") {
                // `output 3 is empty`, or `output is empty` for a single-output grammar.
                match parse_index(index_str) {
                    Some((index, single)) => {
                        saw_indexed |= !single;
                        saw_unindexed |= single;
                        empty_outputs.insert(index);
                    },
                    None => die!("{}: bad output index {:?}", path.display(), index_str),
                }
            } else if let Some(delim) = tail.find(": ") {
                // `output 3: text`, or `output: text` for a single-output grammar.
                let index_str = &tail[..delim];
                let text = &tail[delim + 2..];
                match parse_index(index_str) {
                    Some((index, single)) => {
                        saw_indexed |= !single;
                        saw_unindexed |= single;
                        output_lines.entry(index).or_insert_with(Vec::new).push(text.to_owned());
                    },
                    None => die!("{}: bad output index {:?}", path.display(), index_str),
                }
            }
        } else if line == "// no outputs" {
            no_outputs = true;
        } else if line == "// skip test" {
            skip_test = true;
        }
    }

    // Process the output specifications.
    if skip_test {
        return Ok(true);
    }
    if no_outputs && (output_lines.len() > 0 || empty_outputs.len() > 0) {
        die!("{}: test declares `no outputs`, but has output lines", path.display());
    }
    if saw_indexed && saw_unindexed {
        die!("{}: test mixes indexed and unindexed output lines", path.display());
    }
    let num_outputs = output_lines.len() + empty_outputs.len();
    let mut expected_outputs = Vec::with_capacity(num_outputs);
    for i in 0 .. num_outputs {
        if empty_outputs.contains(&i) {
            if output_lines.contains_key(&i) {
                die!(
                    "{}: test declares output {} as empty, but also provides text for it",
                    path.display(),
                    i,
                );
            }
            expected_outputs.push("".to_owned());
        } else if let Some(ref lines) = output_lines.get(&i) {
            let mut s = lines.join("\n");
            s.push('\n');
            expected_outputs.push(s);
        } else {
            die!("{}: test is missing output for index {}", path.display(), i);
        }
    }

    // Run the grammar 
    f.seek(SeekFrom::Start(0))?;
    let mut src = String::new();
    f.read_to_string(&mut src)?;

    let cx = crux_test_gen::parse_grammar_from_str(&src);

    let mut actual_outputs = Vec::with_capacity(expected_outputs.len());
    for mut out in crux_test_gen::iter_rendered(&cx, "start") {
        // Always include end-of-line, to match parsing of expected outputs.
        if out.len() > 0 && !out.ends_with("\n") {
            out.push('\n');
        }
        actual_outputs.push(out);
    }

    // Try expanding <<prologue>>.  On success, prepend it to the first output.  This is a bit of a
    // hack, but it simplifies testing and works well enough for now.
    let mut prologue = None;
    for mut out in crux_test_gen::iter_rendered(&cx, "prologue") {
        if prologue.is_some() {
            eprintln!("expected at most one expansion for <<prologue>>");
        }
        if out.len() > 0 && !out.ends_with("\n") {
            out.push('\n');
        }
        prologue = Some(out);
    }
    if let Some(mut s) = prologue {
        if actual_outputs.len() > 0 {
            s.push_str(&actual_outputs[0]);
            actual_outputs[0] = s;
        } else {
            // There are no outputs.  Add an additional output containing only the prologue.
            actual_outputs.push(s);
        }
    }


    // Compare outputs
    let mut ok = true;
    for (i, (actual, expected)) in actual_outputs.iter()
            .zip(expected_outputs.iter()).enumerate() {
        if actual == expected {
            continue;
        }
        ok = false;

        eprintln!("{}: mismatch on output {}:", path.display(), i);
        eprintln!("  expected:");
        print_output(i, expected);
        eprintln!("  actual:");
        print_output(i, actual);
    }
    if actual_outputs.len() != expected_outputs.len() {
        ok = false;
    }
    for (i, actual) in actual_outputs.iter().enumerate().skip(expected_outputs.len()) {
        eprintln!("{}: unexpected output {}:", path.display(), i);
        eprintln!("  actual:");
        print_output(i, actual);
    }
    for (i, expected) in expected_outputs.iter().enumerate().skip(actual_outputs.len()) {
        eprintln!("{}: missing output {}:", path.display(), i);
        eprintln!("  expected:");
        print_output(i, expected);
    }
    Ok(ok)
}

fn print_output(i: usize, s: &str) {
    if s.len() == 0 {
        eprintln!("    // output {} is empty", i);
    } else {
        for line in s.lines() {
            eprintln!("    // output {}: {}", i, line);
        }
    }
}

fn take_prefix<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    if s.starts_with(prefix) {
        Some(&s[prefix.len()..])
    } else {
        None
    }
}

fn take_suffix<'a>(s: &'a str, suffix: &str) -> Option<&'a str> {
    if s.ends_with(suffix) {
        Some(&s[.. s.len() - suffix.len()])
    } else {
        None
    }
}

fn parse_index(s: &str) -> Option<(usize, bool)> {
    let s = s.trim();
    if s.len() == 0 {
        Some((0, true))
    } else if let Ok(i) = usize::from_str(s) {
        Some((i, false))
    } else {
        None
    }
}
