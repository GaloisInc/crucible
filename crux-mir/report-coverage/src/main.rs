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
        .arg(Arg::with_name("no-merge-monos")
             .long("no-merge-monos")
             .help("don't merge corresponding branches in different monomorphizations of the \
                    same function"))
        .arg(Arg::with_name("no-color")
             .long("no-color")
             .help("don't colorize output"))
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
    /// Only report coverage for the functions on this crates.
    /// If this is empty, report coverage for all crates.
    /// We use the first block in a profiling report to determine its crate.
    report_crates: Vec<String>,
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
        let mut first_block = true;
        for evt in events {
            let evt = evt.as_object()
                .ok_or_else(|| format!("expected event to be an object"))?;
            if evt.get("type").map_or(false, |j| j == "BLOCK") {
                let fn_id = event_function(evt)?;
                if first_block {
                    if let Some(c) = get_crate(&fn_id) {
                        r.report_crates.push(c);
                    }
                }
                first_block = false;
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

    fn is_drop_flag(&self) -> bool {
        match *self {
            BranchTrans::DropFlag => true,
            _ => false,
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

        _ => {
            die!("unknown tag {:?} for branch", tag);
        },
    }
}

/// Info about the coverage of a funcion
#[derive(Default)]
struct FnCoverage<'a> {
    /// Did we call this function at all
    fn_called: bool,

    /// Information about the branches in the function
    branch_cov: HashMap<&'a str, BranchCoverage>,
}

impl<'a> FnCoverage<'a> {

    pub fn branch(&mut self, span: &'a str) -> &mut BranchCoverage {
        self.branch_cov.entry(span).or_insert_with(||BranchCoverage::default())
    }

    pub fn iter_sorted<'b>(&'b self) -> impl Iterator<Item = (&'a str, &'b BranchCoverage)> + 'b {
        let mut keys = self.branch_cov.keys().collect::<Vec<_>>();
        keys.sort();
        keys.into_iter().map(move |k| (*k, self.branch_cov.get(*k).unwrap()))
    }
}


struct Coverage<'a> {
    /// Whether to merge multiple monomorphized instances of a function when computing coverage.
    /// If set, then an exit is considered covered if it is covered in any monomorphization of the
    /// source function; otherwise, every exit must be covered in every monomorphization.
    merge_functions: bool,

    /// Report stats only for these crates.  If this is empty, then report for
    /// all crates.
    report_crates: Vec<String>,

    // Information about the coverage a function
    fun_cov: HashMap<&'a str, FnCoverage<'a>>
}

impl<'a> Coverage<'a> {
    pub fn new(merge_functions: bool) -> Coverage<'a> {
        Coverage {
            merge_functions,
            fun_cov: HashMap::new(),
            report_crates: vec!()
        }
    }

    pub fn fun<'b>(&'b mut self, fn_id: &'a FnId) -> &'b mut FnCoverage<'a> {
        let k = if self.merge_functions { strip_instance(fn_id) } else { fn_id };
        self.fun_cov.entry(k).or_insert_with(||FnCoverage::default())
    }

    pub fn iter_sorted<'b>(&'b self) -> impl Iterator<Item = (&'a str, &'b FnCoverage<'a>)> + 'b {
        let mut keys = self.fun_cov.keys().collect::<Vec<_>>();
        keys.sort();
        keys.into_iter().map(move |k| (*k, self.fun_cov.get(*k).unwrap()))
    }
}

/// If `s` ends with something that looks like a monomorphized instance disambiguator
/// (`::_inst0123456789abcdef[0]`), then remove that suffix.  If no such suffix is present, `s` is
/// returned unchanged.
fn strip_instance<'a>(s: &'a str) -> &'a str {
    try_strip_instance(s).unwrap_or(s)
}

fn try_strip_instance<'a>(s: &'a str) -> Option<&'a str> {
    if !s.ends_with("[0]") {
        return None;
    }

    let colon_colon = s.rfind("::")?;
    let tail = &s[colon_colon + 2 ..];
    if !tail.starts_with("_inst") {
        return None;
    }
    if tail.len() != "_inst".len() + 16 + "[0]".len() {
        return None;
    }
    Some(&s[..colon_colon])
}

/// Function names are of the form `crate/disambig::name`, `disambig` is
/// a hash used to avoid clashes between different compilations of the same
/// crate.  This function tries to remove the `disambig` because we don't
/// want to show in user facing outpus.
fn strip_crate_hash(s: &str) -> Option<String>{
    let start = s.find('/')? + 1;
    let end = start + s[start ..].find(':')? + 1;
    let mut cs = s[end ..].chars();
    if cs.next()? != ':' { return None }
    Some(s.chars().take(start).chain(cs).collect())
}

fn get_crate(s: &str) -> Option<String> {
    let end = s.find('/')?;
    Some(s[..end].to_string())

}

/// Coverage information for an abstract branch, which may be formed by merging several concrete
/// branches with the same source span.  Records the values that were possible and the values that
/// were seen, unioned across all of the merged branches.  (The set of possible values is usually
/// the same at every branch, but this is not strictly required, and might vary in cases of
/// generics instantiated with `!`.)
#[derive(Clone, Debug, Default)]
struct BranchCoverage {
    /// Possible values of the branch condition.  If an exit leads to unreachable code, the value
    /// for that exit is not recorded here.
    pub possible: HashSet<i64>,
    /// Whether there's a default exit for this branch, in addition to exits for the values in
    /// `possible`.  If the default exit leads to unreachable code, it is not recorded here.
    pub default_possible: bool,
    /// Values observed.
    pub seen: HashSet<i64>,
    /// Whether a default value (not a member of `possible`) was observed.
    pub default_seen: bool,
    /// Whether this is a boolean branch.  If so, warnings will be formatted slightly differently
    /// (its values are rendered `false` and `true` instead of `0` and `1`).
    pub is_boolean: bool,
}

impl BranchCoverage {
    fn visited(&self) -> bool {
        self.default_seen || self.seen.len() > 0
    }
}

fn process<'a>(cov: &mut Coverage<'a>, fn_id: &'a FnId, report: &'a FnReport, trans: &'a FnTrans) {
    // Maps (branch ID, dest index) to the Core `BlockId` of the destination.
    let mut dest_map: HashMap<(u32, usize), BlockId> = HashMap::new();
    let mut visited_branches = HashSet::new();
    let fn_cov = cov.fun(fn_id);
    fn_cov.fn_called = !report.visited_blocks.is_empty();

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

        if bt.is_drop_flag() {
            continue;
        }

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

    // We go over all branches rather than just the visited ones, so
    // we can report full stats about the coverage of a function.
    for (branch_id_32, bt) in trans.branches.iter().enumerate() {
        let branch_id = branch_id_32 as u32;
        let visited = visited_branches.contains(&branch_id);

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
                let bcov = fn_cov.branch(span);
                bcov.is_boolean = true;
                // The entries in `possible` and `seen` are discriminant values (0/false or
                // 1/true), not indices.  In a boolean branch, the exit at index 0 is the true/1
                // case, and the exit at index 1 is the false/0 case.
                if !dest_unreachable(0) {
                    bcov.possible.insert(1);
                }
                if !dest_unreachable(1) {
                    bcov.possible.insert(0);
                }
                if visited && dest_visited(0) {
                    bcov.seen.insert(1);
                }
                if visited && dest_visited(1) {
                    bcov.seen.insert(0);
                }
            },

            BranchTrans::Int(ref vals, ref dests, ref span) => {
                let bcov = fn_cov.branch(span);
                for i in 0 .. dests.len() {
                    // If this destination is `Unreachable`, don't complain that the edge wasn't
                    // taken.  Branches to unreachable blocks are generated in exhaustive `match`
                    // expressions: the switch covers every legal discriminant, then ends with an
                    // unreachable "else" case.
                    if dest_unreachable(i) {
                        continue;
                    }

                    if i < vals.len() {
                        bcov.possible.insert(vals[i]);
                    } else {
                        bcov.default_possible = true;
                    }

                    if visited && dest_visited(i) {
                        if i < vals.len() {
                            bcov.seen.insert(vals[i]);
                        } else {
                            bcov.default_seen = true;
                        }
                    }
                }
            },

            // Ignore drop-flag branches
            BranchTrans::DropFlag => {},
        }
    }
}


struct SpanInfo {
    filename: String,
    line1: usize,
    col1: usize,
    line2: usize,
    col2: usize,
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
        let main_str = &s[..idx].trim();
        let callsite_str = &s[idx + 1 ..].trim();
        let main_span = parse_single_span(main_str)?;
        // mir-json sometimes records the same span both before and after the `!`.
        if callsite_str == main_str {
            return Some((main_span, None));
        }
        // If the callsite span is invalid, then we consider the whole thing invalid.
        let callsite_span = parse_single_span(callsite_str)?;
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


struct Reporter {
    files: SimpleFiles<String, String>,
    file_map: HashMap<String, usize>,
    filters: Option<Vec<Filter>>,
    seen: HashSet<String>,
    color_choice: termcolor::ColorChoice,
}

impl Reporter {
    fn new(
        filters: Option<Vec<Filter>>,
        color_choice: termcolor::ColorChoice,
    ) -> Reporter {
        Reporter {
            files: SimpleFiles::new(),
            file_map: HashMap::new(),
            filters,
            seen: HashSet::new(),
            color_choice,
        }
    }

    fn coverage_stats(&self, fun: &str, called: bool, branch_seen: usize, branch_tot: usize) {
        use std::io::Write;
        use termcolor::{Color, ColorSpec, StandardStream, WriteColor};


        let call_stat = if called { "✅" } else { "❌" }; 
        let mut stdout = StandardStream::stdout(self.color_choice);
        stdout.set_color(ColorSpec::new().set_fg(None)).unwrap();
        let perc = if branch_tot == 0 { if called { 100 } else { 0 } } else { 100 * branch_seen / branch_tot }; 
        let fun = strip_crate_hash(fun).unwrap_or_else(||fun.to_string());
        write!(&mut stdout, "{} {:3}% {}: ", call_stat, perc, fun).unwrap();

        let color =
          if called && branch_seen == branch_tot { Color::Green } else { Color::Yellow };

        stdout.set_color(ColorSpec::new().set_bold(true).set_fg(Some(color))).unwrap();
        writeln!(&mut stdout, "{}/{}", branch_seen, branch_tot).unwrap();
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
            &mut termcolor::StandardStream::stdout(self.color_choice),
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


fn report_all(reporter: &mut Reporter, cov: &Coverage) {

    let mut summary = vec![];

    let consider = |f| {
        if cov.report_crates.len() == 0 { return true }
        if let Some(c) = get_crate(f) {
            cov.report_crates.iter().any(|yes| c == *yes)
        } else {
            false
        }
    };

    for (fun, fn_cov) in cov.iter_sorted() {
        
        if !consider(fun) { continue }
        

        let mut seen = 0;
        let mut tot  = 0;

        for (span, bcov) in fn_cov.iter_sorted() {
            let is_boolean = bcov.is_boolean &&
                bcov.possible.iter().all(|&x| x == 0 || x == 1) &&
                !bcov.default_possible;
 
            if is_boolean {
                tot += 2;

                if !bcov.seen.contains(&0) {
                    if bcov.visited() { reporter.warn(span, "branch condition never has value false"); }
                } else {
                    seen += 1;
                }
                if !bcov.seen.contains(&1) {
                    if bcov.visited() { reporter.warn(span, "branch condition never has value true"); }
                } else {
                    seen += 1;
                }
                continue;
            }

            let mut possible = bcov.possible.iter().cloned().collect::<Vec<_>>();
            possible.sort();

            tot += possible.len();
            if bcov.default_possible { tot += 1; }

            for &val in &possible {

                if bcov.seen.contains(&val) {
                    seen += 1;
                }
                else {
                    if bcov.visited() { reporter.warn(span, format_args!("branch condition never has value {}", val)); }
                }
            }

            if bcov.default_possible {
                if bcov.default_seen {
                    seen += 1;
                } else {
                    if bcov.visited() {
                        reporter.warn(
                            span,
                            format_args!("branch condition never has a value other than {:?}", possible)
                        );
                    }
                }
            }
        }
        summary.push((fun, fn_cov.fn_called, seen, tot));
    }


    for (fun, called, seen,tot) in summary.into_iter() {
        reporter.coverage_stats(fun, called, seen, tot);
    }
    
}


#[allow(deprecated)]
fn hash<H: Hash>(x: &H) -> u64 {
    let mut hasher = SipHasher::new();
    x.hash(&mut hasher);
    hasher.finish()
}

/*
Covergae information is computed from two files:
  * `translation.json` contains static information about the program:
    for each function it tracks the Rust source code locations of branches,
    their targets, and also blocks that were marked as unreachable
  * `report_data.js` contains dynamic information about blocks visited by
    the simluator.
*/

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

    let default_fr = FnReport::default();
    let merge_monos = !m.is_present("no-merge-monos");
    let mut coverage = Coverage::new(merge_monos);
    coverage.report_crates = report.report_crates;

    for (fn_id, ft) in trans.fns.iter() {
        let fr = report.fns.get(fn_id).unwrap_or(&default_fr);
        process(&mut coverage, fn_id, fr, ft);
    }

    let color_choice = if m.is_present("no-color") {
        termcolor::ColorChoice::Never
    } else {
        termcolor::ColorChoice::Auto
    };
    let mut reporter = Reporter::new(filters, color_choice);
    report_all(&mut reporter, &coverage);
}
