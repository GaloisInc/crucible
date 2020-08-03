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
type BlockId = String;

#[derive(Clone, Debug, Default)]
struct Report {
    fns: HashMap<FnId, FnReport>,
}

#[derive(Clone, Debug, Default)]
struct FnReport {
    visited_blocks: HashSet<BlockId>,
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
            }
        }
    }

    Ok(r)
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
        Ok(blk.to_owned())
    }).collect::<Result<Vec<_>, _>>()?;
    Ok(names)
}


#[derive(Clone, Debug, Default)]
struct Trans {
    fns: HashMap<FnId, FnTrans>,
}

#[derive(Clone, Debug, Default)]
struct FnTrans {
    branches: HashMap<BlockId, BranchTrans>,
}

#[derive(Clone, Debug)]
enum BranchTrans {
    Bool(BlockId, BlockId, String),
    Int(Vec<i64>, Vec<BlockId>, String),
    Unreachable,
}

impl BranchTrans {
    fn is_unreachable(&self) -> bool {
        match *self {
            BranchTrans::Unreachable => true,
            _ => false,
        }
    }
}

fn parse_trans(json: Value) -> Result<Trans, String> {
    let mut t = Trans::default();

    let fns = json.as_object()
        .ok_or_else(|| format!("expected object at top level"))?;
    for (fn_name, branches) in fns {
        let ft = t.fns.entry(fn_name.to_owned()).or_insert_with(FnTrans::default);

        let branches = branches.as_object()
            .ok_or_else(|| format!("expected value for {:?} to be an object", fn_name))?;
        for (block, branch) in branches {
            ft.branches.insert(
                block.to_owned(),
                parse_branch(branch)?,
            );
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

            let true_dest = args[0].as_str()
                .ok_or_else(|| format!("expected {} arg 0 to be a string", tag))?
                .to_owned();

            let false_dest = args[1].as_str()
                .ok_or_else(|| format!("expected {} arg 1 to be a string", tag))?
                .to_owned();

            let span = args[2].as_str()
                .ok_or_else(|| format!("expected {} arg 2 to be a string", tag))?
                .to_owned();

            Ok(BranchTrans::Bool(true_dest, false_dest, span))
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
                    Ok(v.as_str()
                        .ok_or_else(|| format!("expected {} arg 1 to contain only strings", tag))?
                        .to_owned())
                }).collect::<Result<Vec<_>, _>>()?;

            let span = args[2].as_str()
                .ok_or_else(|| format!("expected {} arg 2 to be a string", tag))?
                .to_owned();

            if dests.len() != vals.len() + 1 {
                die!("wrong number of dests in {}: {} != {}", tag, dests.len(), vals.len() + 1);
            }

            Ok(BranchTrans::Int(vals, dests, span))
        },
        "UnreachableTerm" => {
            if args.len() != 0 {
                die!("expected 0 args for {}, but got {}", tag, args.len());
            }
            Ok(BranchTrans::Unreachable)
        },
        _ => die!("unknown tag {:?} for branch", tag),
    }
}


fn process(fn_id: &FnId, report: &FnReport, trans: &FnTrans) {
    let mut branch_ids = trans.branches.keys().collect::<Vec<_>>();
    branch_ids.sort();

    for branch_id in branch_ids {
        // Only consider branches that were visited at least once.
        if !report.visited_blocks.contains(branch_id) {
            continue;
        }

        let branch = trans.branches.get(branch_id)
            .expect("branch_id is not a key in branches?");
        match *branch {
            BranchTrans::Bool(ref true_dest, ref false_dest, ref span) => {
                let true_ok = report.visited_blocks.contains(true_dest) ||
                   trans.branches.get(true_dest).map_or(false, |b| b.is_unreachable());
                let false_ok = report.visited_blocks.contains(false_dest) ||
                   trans.branches.get(false_dest).map_or(false, |b| b.is_unreachable());

                if !true_ok {
                    eprintln!("{}: branch condition never takes on the value true", span);
                }
                if !false_ok {
                    eprintln!("{}: branch condition never takes on the value false", span);
                }
            },

            BranchTrans::Int(ref vals, ref dests, ref span) => {
                let mut vals_seen = Vec::new();
                for (i, dest) in dests.iter().enumerate() {
                    if report.visited_blocks.contains(dest) {
                        eprintln!("branch at {}, {} has visited {}", fn_id, branch_id, dest);
                        if i < vals.len() {
                            vals_seen.push(vals[i]);
                        }
                        continue;
                    }

                    // If this destination is `Unreachable`, don't complain that the edge wasn't
                    // taken.  Branches to unreachable blocks are generated in exhaustive `match`
                    // expressions: the switch covers every legal discriminant, then ends with an
                    // unreachable "else" case.
                    match trans.branches.get(dest) {
                        Some(&BranchTrans::Unreachable) => continue,
                        _ => {},
                    }

                    if i < vals.len() {
                        eprintln!(
                            "{} ({}, {}): branch condition never takes on the value {}",
                            span, fn_id, branch_id, vals[i],
                        );
                    } else {
                        eprintln!(
                            "{}: branch condition never takes on a value other than {:?}",
                            span, vals_seen,
                        );
                    }
                }
            },

            BranchTrans::Unreachable => continue,
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
