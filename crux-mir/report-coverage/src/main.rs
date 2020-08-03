use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::Path;
use serde_json::Value;

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

fn parse_report(json: Value) -> Result<Report, String> {
    let mut r = Report::default();

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

    Ok(r)
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
}

impl BranchTrans {
    fn dests(&self) -> &[RegBlockId] {
        match *self {
            BranchTrans::Bool(ref dests, _) => dests,
            BranchTrans::Int(_, ref dests, _) => dests,
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
        _ => die!("unknown tag {:?} for branch", tag),
    }
}


fn process(fn_id: &FnId, report: &FnReport, trans: &FnTrans) {
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
                    eprintln!("{}: branch condition never takes on the value true", span);
                }
                if !dest_visited(1) && !dest_unreachable(1) {
                    eprintln!("{}: branch condition never takes on the value false", span);
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
                        eprintln!(
                            "{}: branch condition never takes on the value {}",
                            span, vals[i],
                        );
                    } else {
                        eprintln!(
                            "{}: branch condition never takes on a value other than {:?}",
                            span, vals_seen,
                        );
                    }
                }
            },
        }
    }
}


fn main() {
    let args = env::args().collect::<Vec<_>>();
    assert!(args.len() == 2, "usage: crux-report-coverage REPORT_DATA.JS");

    let report_path = Path::new(&args[1]);
    let trans_path = report_path.with_file_name("translation.json");

    let report_bytes = fs::read(report_path).unwrap();
    let idx0 = report_bytes.iter().position(|&x| x == b'(').unwrap() + 1;
    let idx1 = report_bytes.iter().rposition(|&x| x == b')').unwrap();
    let report_json: Value = serde_json::from_slice(&report_bytes[idx0..idx1]).unwrap();
    drop(report_bytes);

    let trans_bytes = fs::read(trans_path).unwrap();
    let trans_json: Value = serde_json::from_slice(&trans_bytes).unwrap();
    drop(trans_bytes);

    let report = parse_report(report_json).unwrap();
    let trans = parse_trans(trans_json).unwrap();

    let default_ft = FnTrans::default();
    let mut fn_ids = report.fns.keys().collect::<Vec<_>>();
    fn_ids.sort();
    for fn_id in fn_ids {
        let fr = report.fns.get(fn_id)
            .expect("fn_id is not a key in report.fns?");
        let ft = trans.fns.get(fn_id).unwrap_or(&default_ft);
        process(fn_id, fr, ft);
    }
}
