use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::fs;
#[allow(deprecated)]
use std::hash::{Hash, Hasher, SipHasher};
use std::path::Path;
use std::process;
use clap::{App, Arg, ArgMatches};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::{SimpleFiles, Files};
use serde_json::Value;
use termcolor;


fn parse_args() -> ArgMatches<'static> {
    App::new("crux-report-coverage")
        .about("produces coverage reports for crux-mir symbolic tests")
        .arg(Arg::with_name("input")
             .takes_value(true)
             .value_name("REPORT_DATA.JS")
             .help("coverage data file produced by crux-mir")
             .required(true)
             .multiple(true))
        .arg(Arg::with_name("filter")
             .short("f")
             .long("filter")
             .takes_value(true)
             .value_name("FILE[:[LINE]-[LINE]]")
             .help("only report uncovered branches in the indicated source region(s)")
             .multiple(true)
             .number_of_values(1))
        .get_matches()
}


macro_rules! die {
    ($($args:tt)*) => {
        return Err(format!($($args)*).into());
    };
}

type FnId = String;

/// The string representation of a `Lang.Crucible.CFG.Reg.BlockID`.  These appear in translation
/// metadata.  They have the same format as Core `BlockId`s, but are not interchangeable (the
/// translation from CFG to Core can renumber some blocks).
#[derive(Clone, PartialEq, Eq, Debug, Hash, Default)]
struct RegBlockId(pub String);

/// The string representation of a `Lang.Crucible.CFG.Core.BlockID`.  These appear in profiling
/// reports.
#[derive(Clone, PartialEq, Eq, Debug, Hash, Default)]
struct BlockId(pub String);

#[derive(Clone, Debug, Default)]
struct Report {
    fns: HashMap<FnId, FnReport>,
}

#[derive(Clone, Debug, Default)]
struct FnReport {
    visited_blocks: HashSet<BlockId>,
    branches: Vec<BranchReport>,
}

#[derive(Clone, Debug, Default)]
struct BranchReport {
    branch_id: u32,
    index: usize,
    dests: [BlockId; 2],
}

fn parse_report_into(json: Value, r: &mut Report) -> Result<(), String> {
    let sections = json.as_array()
        .ok_or_else(|| format!("expected array at top level"))?;
    for sec in sections {
        let sec = sec.as_object()
            .ok_or_else(|| format!("expected section to be an object"))?;
        if !sec.get("type").map_or(false, |j| j == "callgraph") {
            continue;
        }

        let events = sec.get("events")
            .ok_or_else(|| format!("callgraph section has no `events` field"))?;
        let events = events.as_array()
            .ok_or_else(|| format!("expected callgraph `events` field to be an array"))?;
        for evt in events {
            let evt = evt.as_object()
                .ok_or_else(|| format!("expected event to be an object"))?;
            if evt.get("type").map_or(false, |j| j == "BLOCK") {
                let fn_id = event_function(evt)?;
                r.fns.entry(fn_id).or_insert_with(FnReport::default)
                    .visited_blocks.extend(event_blocks(evt)?);
            } else if evt.get("type").map_or(false, |j| j == "BRANCH") {
                let fn_id = event_function(evt)?;
                let span = event_callsite(evt)?;
                if let Some((branch_id, index)) = parse_callsite(&span) {
                    let blocks = event_blocks(evt)?;
                    if blocks.len() != 2 {
                        die!("expected exactly two blocks in BRANCH event at {}", span);
                    }
                    let mut it = blocks.into_iter();
                    let dests = [it.next().unwrap(), it.next().unwrap()];
                    r.fns.entry(fn_id).or_insert_with(FnReport::default)
                        .branches.push(BranchReport { branch_id, index, dests });
                }
            }
        }
    }
    Ok(())
}

fn event_callsite(evt: &serde_json::Map<String, Value>) -> Result<String, String> {
    let callsite = match evt.get("callsite") {
        Some(x) => x,
        None => return Ok(String::new()),
    };
    Ok(callsite.as_str()
       .ok_or_else(|| format!("expected event `callsite` field to be a string"))?
       .to_owned())
}

fn parse_callsite(s: &str) -> Option<(u32, usize)> {
    for word in s.split_whitespace() {
        if !word.starts_with('#') {
            continue;
        }
        let comma = word.find(',')?;
        let branch_id = word[1..comma].parse().ok()?;
        let index = word[comma + 1 ..].parse().ok()?;
        return Some((branch_id, index));
    }
    None
}

fn event_function(evt: &serde_json::Map<String, Value>) -> Result<FnId, String> {
    Ok(evt.get("function")
       .ok_or_else(|| format!("event has no `function` field"))?
       .as_str()
       .ok_or_else(|| format!("expected event `function` field to be a string"))?
       .to_owned())
}

fn event_blocks(evt: &serde_json::Map<String, Value>) -> Result<Vec<BlockId>, String> {
    let blocks = match evt.get("blocks") {
        Some(x) => x,
        None => return Ok(Vec::new()),
    };
    let blocks = blocks.as_array()
        .ok_or_else(|| format!("expected event `blocks` field to be an array"))?;
    let names = blocks.iter().map(|blk| -> Result<_, String> {
        let blk = blk.as_str()
            .ok_or_else(|| format!("expected `blocks` entry to be a string"))?;
        Ok(BlockId(blk.to_owned()))
    }).collect::<Result<Vec<_>, _>>()?;
    Ok(names)
}


#[derive(Clone, Debug, Default)]
struct Trans {
    fns: HashMap<FnId, FnTrans>,
}

#[derive(Clone, Debug, Default)]
struct FnTrans {
    branches: Vec<BranchTrans>,
    unreachable: HashSet<RegBlockId>,
}

#[derive(Clone, Debug)]
enum BranchTrans {
    Bool([RegBlockId; 2], String),
    Int(Vec<i64>, Vec<RegBlockId>, String),
    DropFlag,
}

impl BranchTrans {
    fn dests(&self) -> &[RegBlockId] {
        match *self {
            BranchTrans::Bool(ref dests, _) => dests,
            BranchTrans::Int(_, ref dests, _) => dests,
            BranchTrans::DropFlag => &[],
        }
    }
}

fn parse_trans(json: Value) -> Result<Trans, String> {
    let mut t = Trans::default();

    let fns = json.as_object()
        .ok_or_else(|| format!("expected object at top level"))?;
    for (fn_name, fn_json) in fns {
        let ft = t.fns.entry(fn_name.to_owned()).or_insert_with(FnTrans::default);

        let fn_json = fn_json.as_object()
            .ok_or_else(|| format!("expected value for {:?} to be an object", fn_name))?;

        let branches_json = fn_json.get("_ftiBranches")
            .ok_or_else(|| format!("info for {:?} has no _ftiBranches?", fn_name))?
            .as_array()
            .ok_or_else(|| format!("expected {:?} _ftiBranches to be an array", fn_name))?;
        for branch_json in branches_json {
            ft.branches.push(parse_branch(branch_json)?);
        }

        let unreachable_json = fn_json.get("_ftiUnreachable")
            .ok_or_else(|| format!("info for {:?} has no _ftiUnreachable?", fn_name))?
            .as_array()
            .ok_or_else(|| format!("expected {:?} _ftiUnreachable to be an array", fn_name))?;
        for block_id in unreachable_json {
            let block_id = block_id.as_str()
                .ok_or_else(|| format!("expected {:?} block ID to be a string", fn_name))?;
            let block_id = RegBlockId(block_id.to_owned());
            ft.unreachable.insert(block_id);
        }
    }

    Ok(t)
}

fn parse_branch(json: &Value) -> Result<BranchTrans, String> {
    let obj = json.as_object()
        .ok_or_else(|| format!("expected branch value to be an object"))?;
    let tag = obj.get("tag")
        .ok_or_else(|| format!("branch object has no `tag`"))?
        .as_str()
        .ok_or_else(|| format!("expected `tag` to be a string"))?;
    let args = match obj.get("contents") {
        Some(x) => x.as_array()
            .ok_or_else(|| format!("expected `contents` to be an array"))? as &[Value],
        None => &[],
    };

    match tag {
        "BoolBranch" => {
            if args.len() != 3 {
                die!("expected 3 args for {}, but got {}", tag, args.len());
            }

            let true_dest = RegBlockId(args[0].as_str()
                .ok_or_else(|| format!("expected {} arg 0 to be a string", tag))?
                .to_owned());

            let false_dest = RegBlockId(args[1].as_str()
                .ok_or_else(|| format!("expected {} arg 1 to be a string", tag))?
                .to_owned());

            let span = args[2].as_str()
                .ok_or_else(|| format!("expected {} arg 2 to be a string", tag))?
                .to_owned();

            Ok(BranchTrans::Bool([true_dest, false_dest], span))
        },

        "IntBranch" => {
            if args.len() != 3 {
                die!("expected 3 args for {}, but got {}", tag, args.len());
            }

            let vals = args[0].as_array()
                .ok_or_else(|| format!("expected {} arg 0 to be an array", tag))?
                .iter().map(|v| -> Result<_, String> {
                    Ok(v.as_u64()
                        .ok_or_else(|| format!("expected {} arg 0 to contain only u64s", tag))?
                        as i64)
                }).collect::<Result<Vec<_>, _>>()?;

            let dests = args[1].as_array()
                .ok_or_else(|| format!("expected {} arg 1 to be an array", tag))?
                .iter().map(|v| -> Result<_, String> {
                    Ok(RegBlockId(v.as_str()
                        .ok_or_else(|| format!("expected {} arg 1 to contain only strings", tag))?
                        .to_owned()))
                }).collect::<Result<Vec<_>, _>>()?;

            let span = args[2].as_str()
                .ok_or_else(|| format!("expected {} arg 2 to be a string", tag))?
                .to_owned();

            if dests.len() != vals.len() + 1 {
                die!("wrong number of dests in {}: {} != {}", tag, dests.len(), vals.len() + 1);
            }

            Ok(BranchTrans::Int(vals, dests, span))
        },

        "DropFlagBranch" => {
            if args.len() != 0 {
                die!("expected 3 args for {}, but got {}", tag, args.len());
            }
            Ok(BranchTrans::DropFlag)
        },

        _ => die!("unknown tag {:?} for branch", tag),
    }
}


struct Reporter {
    files: SimpleFiles<String, String>,
    file_map: HashMap<String, usize>,
    filters: Option<Vec<Filter>>,
    seen: HashSet<String>,
}

struct SpanInfo {
    filename: String,
    line1: usize,
    col1: usize,
    line2: usize,
    col2: usize,
}

impl Reporter {
    fn new(filters: Option<Vec<Filter>>) -> Reporter {
        Reporter {
            files: SimpleFiles::new(),
            file_map: HashMap::new(),
            filters,
            seen: HashSet::new(),
        }
    }

    fn warn(&mut self, span: &str, msg: impl Display) {
        let key = format!("{}; {}", span, msg);
        if !self.seen.insert(key) {
            // Don't display the same warning twice.
            return;
        }

        let (sp, callsite) = match parse_span(span) {
            Some(x) => x,
            None => {
                eprintln!("invalid span {:?}", span);
                eprintln!("{}: {}", span, msg);
                return;
            },
        };

        // If any `--filter` option was passed, then either the span or the callsite must fall
        // within one of the filter regions.
        if let Some(ref filters) = self.filters {
            let span_ok = filters.iter().any(|f| f.contains_span(&sp));
            let callsite_ok = match callsite {
                Some(ref callsite) => filters.iter().any(|f| f.contains_span(callsite)),
                None => false,
            };

            if !span_ok && !callsite_ok {
                return;
            }
        }

        let file_id = self.load_file(&sp.filename);
        let start = self.pos_to_bytes(file_id, sp.line1, sp.col1);
        let end = self.pos_to_bytes(file_id, sp.line2, sp.col2);
        let label = Label::primary(file_id, start .. end);

        let mut labels = Vec::with_capacity(2);
        labels.push(label);

        if let Some(callsite) = callsite {
            let file_id = self.load_file(&callsite.filename);
            let start = self.pos_to_bytes(file_id, callsite.line1, callsite.col1);
            let end = self.pos_to_bytes(file_id, callsite.line2, callsite.col2);
            let label = Label::secondary(file_id, start .. end)
                .with_message("in this macro invocation");
            labels.push(label);
        }

        let diag = Diagnostic::warning()
            .with_message(msg.to_string())
            .with_labels(labels);

        codespan_reporting::term::emit(
            &mut termcolor::StandardStream::stdout(termcolor::ColorChoice::Auto),
            &codespan_reporting::term::Config::default(),
            &self.files,
            &diag,
        ).unwrap();
    }

    fn load_file(&mut self, name: &str) -> usize {
        if let Some(&id) = self.file_map.get(name) {
            return id;
        }

        let content = match fs::read_to_string(name) {
            Ok(x) => x,
            Err(_) => String::new(),
        };
        let id = self.files.add(name.to_owned(), content);
        self.file_map.insert(name.to_owned(), id);
        id
    }

    fn pos_to_bytes(&self, file_id: usize, line: usize, col: usize) -> usize {
        let line = line.saturating_sub(1);
        let col = col.saturating_sub(1);
        let range = match self.files.line_range(file_id, line) {
            Some(x) => x,
            None => return 0,
        };
        if col >= range.end - range.start {
            range.end
        } else {
            range.start + col
        }
    }
}

fn parse_span(s: &str) -> Option<(SpanInfo, Option<SpanInfo>)> {
    // Remove branch info if present
    let s = match s.rfind('#') {
        Some(idx) => &s[..idx],
        None => s,
    };

    if let Some(idx) = s.find('!') {
        // This span includes a macro callsite.  We parse the portions before and after the `!` as
        // separate spans, and return both.
        let main_span = parse_single_span(&s[..idx])?;
        // If the callsite span is invalid, then we consider the whole thing invalid.
        let callsite_span = parse_single_span(&s[idx + 1 ..])?;
        Some((main_span, Some(callsite_span)))
    } else {
        let main_span = parse_single_span(s)?;
        Some((main_span, None))
    }
}

fn parse_single_span(s: &str) -> Option<SpanInfo> {
    // Span format is something like "file.rs:1:2: 3:4", consisting of filename, start line and
    // column, and end line and column.  We also support the truncated form "file.rs:1:2", which
    // uses the start line and column for the end position as well.
    let mut it = s.split(':').map(|s| s.trim());
    let filename = it.next()?.to_owned();
    let line1 = it.next()?.parse().ok()?;
    let col1 = it.next()?.parse().ok()?;
    if let Some(x) = it.next() {
        let line2 = x.parse().ok()?;
        let col2 = it.next()?.parse().ok()?;
        if it.next().is_some() {
            // Too many pieces - should be exactly 5.
            return None;
        }
        Some(SpanInfo { filename, line1, col1, line2, col2 })
    } else {
        // Exactly 3 pieces, so there's only one line/column pair.
        Some(SpanInfo { filename, line1, col1, line2: line1, col2: col1 })
    }
}

fn process(reporter: &mut Reporter, fn_id: &FnId, report: &FnReport, trans: &FnTrans) {
    // Maps (branch ID, dest index) to the Core `BlockId` of the destination.
    let mut dest_map: HashMap<(u32, usize), BlockId> = HashMap::new();
    let mut visited_branches = HashSet::new();

    fn insert_dest(
        fn_id: &FnId,
        dm: &mut HashMap<(u32, usize), BlockId>,
        branch_id: u32,
        index: usize,
        dest: &BlockId,
    ) {
        let old = dm.insert((branch_id, index), dest.clone());
        if let Some(old) = old {
            if &old != dest {
                eprintln!(
                    "{}: multiple dests reported for branch {}, index {}: {:?} != {:?}",
                    fn_id, branch_id, index, old, dest,
                );
            }
        }
    }

    for branch in &report.branches {
        let BranchReport { branch_id, index, ref dests } = *branch;

        let bt = match trans.branches.get(branch_id as usize) {
            Some(x) => x,
            None => {
                eprintln!("{}: bad branch id {}", fn_id, branch_id);
                continue;
            },
        };

        if index >= bt.dests().len() {
            eprintln!(
                "{}: index {} out of range for branch {} ({} dests)",
                fn_id, index, branch_id, bt.dests().len(),
            );
            continue;
        }

        visited_branches.insert(branch_id);

        insert_dest(fn_id, &mut dest_map, branch_id, index, &dests[0]);

        if index + 2 == bt.dests().len() {
            // This is the last branch of the switch, meaning the `false` exit goes to the default
            // case instead of to another branch.
            insert_dest(fn_id, &mut dest_map, branch_id, index + 1, &dests[1]);
        }
    }


    let mut branch_ids = visited_branches.into_iter().collect::<Vec<_>>();
    branch_ids.sort();
    for branch_id in branch_ids {
        let bt = &trans.branches[branch_id as usize];

        let dest_visited = |index| {
            let block_id = match dest_map.get(&(branch_id, index)) {
                Some(x) => x,
                None => return false,
            };
            report.visited_blocks.contains(block_id)
        };

        let dest_unreachable = |index| {
            trans.unreachable.contains(&bt.dests()[index])
        };

        match *bt {
            BranchTrans::Bool(_, ref span) => {
                if !dest_visited(0) && !dest_unreachable(0) {
                    reporter.warn(span, "branch condition never has value true");
                }
                if !dest_visited(1) && !dest_unreachable(1) {
                    reporter.warn(span, "branch condition never has value false");
                }
            },

            BranchTrans::Int(ref vals, ref dests, ref span) => {
                let mut vals_seen = Vec::new();
                for i in 0 .. dests.len() {
                    if dest_visited(i) {
                        if i < vals.len() {
                            vals_seen.push(vals[i]);
                        }
                        continue;
                    }

                    // If this destination is `Unreachable`, don't complain that the edge wasn't
                    // taken.  Branches to unreachable blocks are generated in exhaustive `match`
                    // expressions: the switch covers every legal discriminant, then ends with an
                    // unreachable "else" case.
                    if dest_unreachable(i) {
                        continue;
                    }

                    if i < vals.len() {
                        reporter.warn(
                            span,
                            format_args!(
                                "branch condition never has value {}",
                                vals[i],
                            ),
                        );
                    } else {
                        reporter.warn(
                            span,
                            format_args!(
                                "branch condition never has a value other than {:?}",
                                vals_seen,
                            ),
                        );
                    }
                }
            },

            // Ignore drop-flag branches
            BranchTrans::DropFlag => {},
        }
    }
}

#[derive(Clone, Debug, Default)]
struct Filter {
    filename: String,
    start_line: Option<usize>,
    end_line: Option<usize>,
}

impl Filter {
    fn from_str(s: &str) -> Result<Filter, String> {
        let mut f = Filter::default();

        if let Some(colon) = s.rfind(':') {
            f.filename = s[..colon].to_owned();
            let lines = &s[colon + 1 ..];
            let dash = match lines.find('-') {
                Some(x) => x,
                None => return Err("expected `[LINE]-[LINE]` after `:`".to_owned()),
            };
            fn parse(s: &str) -> Result<Option<usize>, String> {
                if s.len() == 0 {
                    Ok(None)
                } else {
                    s.parse::<usize>().map(Some).map_err(|e| e.to_string())
                }
            }
            f.start_line = parse(&lines[..dash])?;
            f.end_line = parse(&lines[dash + 1 ..])?;
        } else {
            f.filename = s.to_owned();
        }

        Ok(f)
    }

    fn contains_span(&self, sp: &SpanInfo) -> bool {
        // This behaves a little oddly, accepting spans whose (exclusive) end position is exactly
        // at the start of a line as covering that line.  But hopefully nobody is quite that picky
        // about the placement of their filters...
        self.filename == sp.filename &&
            self.start_line.map_or(true, |line| sp.line2 >= line) &&
            self.end_line.map_or(true, |line| sp.line1 <= line)
    }
}

#[allow(deprecated)]
fn hash<H: Hash>(x: &H) -> u64 {
    let mut hasher = SipHasher::new();
    x.hash(&mut hasher);
    hasher.finish()
}

fn main() {
    let m = parse_args();

    let mut filters = Vec::new();
    if let Some(filter_strs) = m.values_of("filter") {
        for filter_str in filter_strs {
            let f = match Filter::from_str(filter_str) {
                Ok(x) => x,
                Err(e) => {
                    eprintln!("bad filter {:?}: {}", filter_str, e);
                    eprintln!("{}", m.usage());
                    process::exit(1);
                },
            };
            filters.push(f);
        }
    }
    let filters = if filters.len() > 0 { Some(filters) } else { None };

    let mut report = Report::default();
    let mut trans = None;
    let mut trans_hash = None;

    for report_path_str in m.values_of_os("input").unwrap() {
        let report_path = Path::new(report_path_str);
        let trans_path = report_path.with_file_name("translation.json");

        let report_bytes = fs::read(report_path).unwrap();
        let idx0 = report_bytes.iter().position(|&x| x == b'(').unwrap() + 1;
        let idx1 = report_bytes.iter().rposition(|&x| x == b')').unwrap();
        let report_json: Value = serde_json::from_slice(&report_bytes[idx0..idx1]).unwrap();
        drop(report_bytes);

        parse_report_into(report_json, &mut report).unwrap();

        let trans_bytes = fs::read(trans_path).unwrap();
        let cur_trans_hash = hash(&trans_bytes);
        if let Some(old_trans_hash) = trans_hash {
            assert!(
                cur_trans_hash == old_trans_hash,
                "translation hashes for {:?} and {:?} do not match",
                report_path_str, m.value_of_os("input").unwrap(),
            );
        } else {
            let trans_json: Value = serde_json::from_slice(&trans_bytes).unwrap();
            drop(trans_bytes);
            let cur_trans = parse_trans(trans_json).unwrap();
            trans = Some(cur_trans);
            trans_hash = Some(cur_trans_hash);
        }
    }

    let trans = match trans {
        Some(x) => x,
        None => {
            panic!("must provide at least one report file");
        },
    };

    let default_ft = FnTrans::default();
    let mut reporter = Reporter::new(filters);
    let mut fn_ids = report.fns.keys().collect::<Vec<_>>();
    fn_ids.sort();
    for fn_id in fn_ids {
        let fr = report.fns.get(fn_id)
            .expect("fn_id is not a key in report.fns?");
        let ft = trans.fns.get(fn_id).unwrap_or(&default_ft);
        process(&mut reporter, fn_id, fr, ft);
    }
}
