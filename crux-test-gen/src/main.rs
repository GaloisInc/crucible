use std::collections::HashMap;
use std::env;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::process;
use std::rc::Rc;
use std::str::FromStr;

use crate::builder::{GrammarBuilder, ProductionLhs, ProductionRhs};
use crate::ty::{Ty, Subst, UnifyState, VarId};

mod builder;
mod parse;
mod ty;


type NonterminalId = usize;
type ProductionId = usize;

#[derive(Clone, Debug, Default)]
pub struct NonterminalRef {
    id: NonterminalId,
    args: Box<[Ty]>,
}

/// The implementation of a "magic" built-in production.  The callback can manipulate the
/// surrounding expansion state (for example, to adjust the current budget values) and the
/// expansion of the current production (for example, to provide a callback for use in rendering
/// `Chunk::Special`s).  The third argument is the instance index, used for families of built-in
/// productions.  (If this is a single production and not a family - in other words, if
/// `multiplicity` is not defined - then the index is always zero.)  The callback should return
/// `true` to indicate success, or `false` for failure (in which case the current expansion will be
/// aborted, and control will resume from the next alternative `Continuation`).
///
/// If the callback returns false, it must also leave the `ExpState` unchanged.  The caller may try
/// a different production if this one fails, and the callback must leave no visible side effects
/// in that case.
struct ProductionHandler(Box<dyn Fn(&mut ExpState, &mut PartialExpansion, usize) -> bool>);

/// Compute the number of instances in this builtin production family.
///
/// Most builtins define of a single nonterminal along with one or more productions (usually
/// exactly one, in fact) for expanding that nonterminal.  However, for some builtins, the number
/// of ways to expand the builtin nonterminal is not known in advance.  For example, the
/// `choose_local` builtin expands to any of the variables in scope, so the number of possible
/// expansions depends on the available variables.
struct ProductionMultiplicity(Box<dyn Fn(&ExpState) -> usize>);

impl fmt::Debug for ProductionHandler {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "ProductionHandler(..)")
    }
}

impl fmt::Debug for ProductionMultiplicity {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "ProductionMultiplicity(..)")
    }
}

#[derive(Debug, Default)]
pub struct Production {
    /// The generic type parameters of this production, declared with `for[T, U, ...]`.
    vars: Vec<Rc<str>>,
    /// The arguments to the nonterminal on the LHS of this production.  The arguments of the
    /// `NonterminalRef` must match these for the production to apply.  In `for[T] expr[Vec[T]]`,
    /// the `args` are `[Vec[T]]`.
    args: Vec<Ty>,
    chunks: Vec<Chunk>,
    nts: Vec<NonterminalRef>,
    handler: Option<ProductionHandler>,
    multiplicity: Option<ProductionMultiplicity>,
}

#[derive(Debug, Default)]
pub struct Nonterminal {
    /// All productions for this nonterminal.  This is an upper bound on possible expansion
    /// options; some productions may not be valid for the `args` of a given `NonterminalRef`.
    productions: Vec<ProductionId>
}

#[derive(Debug, Default)]
pub struct Context {
    productions: Vec<Production>,
    nonterminals: Vec<Nonterminal>,
}

#[derive(Clone, Debug)]
pub enum Chunk {
    /// A chunk of literal text.  Must not contain newlines.  The `bool`
    /// indicates whether to insert a newline after this text.
    Text(Rc<str>, bool),
    /// Increases or decreases the current indentation level.
    Indent(isize),
    /// Expand the nonterminal at the given index.
    Nt(usize),

    Special(usize),
}

#[derive(Clone)]
struct Expansion {
    production: ProductionId,
    subexpansions: Box<[Expansion]>,
    specials: Box<[Rc<dyn Fn(&mut ty::UnifyState) -> String>]>,
}

#[derive(Clone)]
struct PartialExpansion {
    production: ProductionId,
    /// Translation from local type variables of the production to global `VarId`s in the parent
    /// `ExpState`'s `unify` table.
    subst: Subst,
    num_nts: usize,
    subexpansions: Vec<Expansion>,
    specials: Vec<Rc<dyn Fn(&mut ty::UnifyState) -> String>>,
}

#[derive(Clone)]
struct ExpState {
    exp: Vec<PartialExpansion>,
    unify: ty::UnifyState,
    budget: Budget,
}

#[derive(Clone)]
/// Represents alternatives not taken during expansion of the grammar.  Can be
/// resumed into a new `ExpState` to generate the next alternative.
struct Continuation {
    state: ExpState,
    kind: ContinuationKind,
}

#[derive(Clone)]
enum ContinuationKind {
    /// Continue with the next in a sequence of alternative productions.
    Alts {
        alternatives: Vec<ProductionId>,
        next: usize,
    },
    /// Continue with the next instance of a single family of productions.
    Family {
        production: ProductionId,
        multiplicity: usize,
        next: usize,
    },
}

#[derive(Clone)]
enum ExpResult {
    Progress,
    Done(Expansion, UnifyState),
    Abort,
}


#[derive(Clone, Default, Debug)]
pub struct Budget(HashMap<String, usize>);

impl Budget {
    pub fn set(&mut self, key: &str, amount: usize) {
        self.0.insert(key.to_owned(), amount);
    }

    pub fn get(&self, key: &str) -> usize {
        self.0.get(key).cloned().unwrap_or(0)
    }

    pub fn add(&mut self, key: &str, amount: usize) {
        *self.0.entry(key.to_owned()).or_insert(0) += amount;
    }

    pub fn take(&mut self, key: &str, amount: usize) -> bool {
        match self.0.get_mut(key) {
            Some(x) => {
                if *x >= amount {
                    *x -= amount;
                    true
                } else {
                    false
                }
            },
            None => {
                // Taking 0 is always okay.  Taking any positive amount from an uninitialized
                // budget will fails.
                amount == 0
            },
        }
    }
}



impl PartialExpansion {
    pub fn new(
        cx: &Context,
        unify: &mut UnifyState,
        production: ProductionId,
    ) -> PartialExpansion {
        let subst = unify.fresh_subst(cx.productions[production].vars.len());
        let num_nts = cx.productions[production].nts.len();
        let subexpansions = Vec::with_capacity(num_nts);
        PartialExpansion {
            production,
            subst,
            num_nts,
            subexpansions,
            specials: Vec::new(),
        }
    }

    pub fn is_finished(&self) -> bool {
        self.subexpansions.len() == self.num_nts
    }

    pub fn into_expansion(self) -> Expansion {
        assert!(self.is_finished());
        Expansion {
            production: self.production,
            subexpansions: self.subexpansions.into_boxed_slice(),
            specials: self.specials.into_boxed_slice(),
        }
    }

    fn next_nonterminal<'cx>(&self, cx: &'cx Context) -> &'cx NonterminalRef {
        let idx = self.subexpansions.len();
        &cx.productions[self.production].nts[idx]
    }
}

impl ExpState {
    fn new() -> ExpState {
        ExpState {
            exp: Vec::new(),
            unify: UnifyState::new(),
            budget: Budget::default(),
        }
    }

    fn apply_production(
        &mut self,
        cx: &Context,
        production: ProductionId,
        index: Option<usize>,
    ) -> bool {
        let mut pe = PartialExpansion::new(cx, &mut self.unify, production);

        if !self.exp.is_empty() {
            let tys1 = self.cur_partial().subst.clone()
                .and(&self.cur_partial().next_nonterminal(cx).args as &[_]);
            let tys2 = pe.subst.clone().and(&cx.productions[production].args as &[_]);

            if !self.unify.unify(tys1, tys2) {
                return false;
            }
        } else {
            // When resuming the initial continuation, there is no current nonterminal we can unify
            // with the production's LHS.  However, this is okay as long as the production has no
            // arguments.
            assert!(cx.productions[production].args.len() == 0);
        }

        // Sanity check.  This will fail if a nonterminal has multiple productions and at least one
        // is a production family.
        assert!(cx.productions[production].multiplicity.is_some() == index.is_some());

        if let Some(ref handler) = cx.productions[production].handler {
            let ok = (*handler.0)(self, &mut pe, index.unwrap_or(0));
            if !ok {
                // FIXME: If the handler fails after unification has already happened, we need to
                // roll back the unification state.  Otherwise, this production could have visible
                // side effects, even if it logically was never applied.  Currently, this doesn't
                // cause us any problems, because all of the builtin productions use patterns that
                // are linear and fully general, meaning they never unify a pre-existing variable
                // with another pre-existing variable or any concrete type.
                return false;
            }
        }

        if pe.is_finished() {
            self.cur_partial_mut().subexpansions.push(pe.into_expansion());
        } else {
            self.exp.push(pe);
        }
        true
    }

    fn cur_partial(&self) -> &PartialExpansion {
        self.exp.last().unwrap()
    }

    fn cur_partial_mut(&mut self) -> &mut PartialExpansion {
        self.exp.last_mut().unwrap()
    }

    pub fn expand(self, cx: &Context) -> (ExpResult, Vec<Continuation>) {
        let mut st = self;
        let mut continuations = Vec::new();

        loop {
            // Pop any finished frames from the expansion stack.
            while st.cur_partial().is_finished() {
                let prev_partial = st.exp.pop().unwrap();
                // TODO: post-expansion actions
                let prev = prev_partial.into_expansion();
                if let Some(cur) = st.exp.last_mut() {
                    cur.subexpansions.push(prev);
                } else {
                    // We popped the last frame.  Expansion is complete.
                    return (ExpResult::Done(prev, st.unify), continuations);
                }
            }

            // The current expansion frame is guaranteed to be unfinished.  Choose a production for
            // its next nonterminal, then apply that production (pushing a new frame).
            let next_nt = st.cur_partial().next_nonterminal(cx);
            let alts = cx.nonterminals[next_nt.id].productions.clone();

            // We suspend the current state at the branching point for choosing between `alts`,
            // then immediately resume the continuation to continue with the current expansion.
            let mut cont = if alts.len() == 1 {
                let prod = alts[0];
                let multiplicity = cx.productions[prod].multiplicity.as_ref()
                    .map(|f| (f.0)(&st));

                // Shortcut: if there's exactly one option, we simply apply it.  This avoids a
                // clone inside `Continuation::resume`.
                if multiplicity.is_none() || multiplicity == Some(1) {
                    let index = multiplicity.map(|_| 0);
                    if st.apply_production(cx, prod, index) {
                        continue;
                    } else {
                        return (ExpResult::Abort, continuations);
                    }
                }

                Continuation {
                    state: st,
                    kind: ContinuationKind::Family {
                        production: prod,
                        multiplicity: multiplicity.unwrap(),
                        next: 0,
                    },
                }
            } else {
                // Note this handles the `alts.len() == 0` case.  Since `next == len == 0` from the
                // start, `resume` will bail out before cloning the state.
                Continuation {
                    state: st,
                    kind: ContinuationKind::Alts {
                        alternatives: alts,
                        next: 0,
                    },
                }
            };

            if let Some(new_st) = cont.resume(cx) {
                st = new_st;
                continuations.push(cont);
            } else {
                return (ExpResult::Abort, continuations);
            }
        }
    }
}

impl Continuation {
    pub fn new(production: ProductionId) -> Continuation {
        Continuation {
            state: ExpState::new(),
            kind: ContinuationKind::Alts {
                alternatives: vec![production],
                next: 0,
            },
        }
    }

    pub fn resume(&mut self, cx: &Context) -> Option<ExpState> {
        match self.kind {
            ContinuationKind::Alts { ref mut alternatives, ref mut next } => {
                if *next >= alternatives.len() {
                    return None;
                }

                let mut st = self.state.clone();
                for (i, &alt) in alternatives.iter().enumerate().skip(*next) {
                    if st.apply_production(cx, alt, None) {
                        *next = i + 1;
                        return Some(st);
                    }
                }
                *next = alternatives.len();
                None
            },

            ContinuationKind::Family { production, multiplicity, ref mut next } => {
                if *next >= multiplicity {
                    return None;
                }

                let mut st = self.state.clone();
                for i in *next .. multiplicity {
                    if st.apply_production(cx, production, Some(i)) {
                        *next = i + 1;
                        return Some(st);
                    }
                }
                *next = multiplicity;
                None
            },
        }
    }
}

fn expand_next(
    cx: &Context,
    continuations: &mut Vec<Continuation>,
) -> Option<(Expansion, UnifyState)> {
    while let Some(cont) = continuations.last_mut() {
        if let Some(state) = cont.resume(cx) {
            let (result, new_continuations) = state.expand(cx);
            continuations.extend(new_continuations);
            match result {
                ExpResult::Done(exp, unify) => return Some((exp, unify)),
                ExpResult::Abort => {},
                ExpResult::Progress => unimplemented!(),
            }
        } else {
            continuations.pop();
        }
    }
    None
}


fn render_expansion(cx: &Context, unify: &mut UnifyState, exp: &Expansion) -> String {
    let mut stack: Vec<(&Chunk, &Expansion)> = Vec::new();
    for chunk in cx.productions[exp.production].chunks.iter().rev() {
        stack.push((chunk, exp));
    }

    let mut output = String::new();
    let mut indent = String::new();
    let mut start_of_line = true;
    while let Some((chunk, exp)) = stack.pop() {
        match *chunk {
            Chunk::Text(ref s, newline) => {
                if start_of_line {
                    output.push_str(&indent);
                }
                start_of_line = false;
                output.push_str(s);
                if newline {
                    output.push('\n');
                    start_of_line = true;
                }
            },
            Chunk::Indent(offset) => {
                if offset > 0 {
                    for _ in 0 .. offset {
                        indent.push(' ');
                    }
                } else {
                    for _ in 0 .. -offset {
                        indent.pop();
                    }
                }
            },
            Chunk::Nt(idx) => {
                let subexp = &exp.subexpansions[idx];
                for subchunk in cx.productions[subexp.production].chunks.iter().rev() {
                    stack.push((subchunk, subexp));
                }
            },
            Chunk::Special(idx) => {
                output.push_str(&(exp.specials[idx])(unify));
            },
        }
    }

    output
}


fn add_start_production(gb: &mut GrammarBuilder) {
    // Set up the nonterminal __root__, with ID 0, which expands to `<<start>>` via production 0.
    let root_id = gb.nt_id("__root__");
    assert_eq!(root_id, 0);
    let start_id = gb.nt_id("start");
    let lhs = gb.mk_simple_lhs("__root__");
    let rhs = ProductionRhs {
        chunks: vec![Chunk::Nt(0)],
        nts: vec![gb.mk_simple_nt_ref("start")],
    };
    let start_prod_id = gb.add_prod(lhs, rhs);
    assert_eq!(start_prod_id, 0);
}

// NB: Currently, builtin production LHSs should only use a sequence of distinct variables as their
// patterns.  Variables should not repeat, and no pattern should include a concrete type
// constructor.  See the FIXME in `apply_production` for more info.

fn add_builtin_ctor_name(gb: &mut GrammarBuilder) {
    let (lhs, vars) = gb.mk_lhs_with_args("ctor_name", 1);
    let var = vars[0];
    let rhs = ProductionRhs {
        chunks: vec![Chunk::Special(0)],
        nts: vec![],
    };
    gb.add_prod_with_handler(lhs, rhs, move |_, partial, _| {
        let var = partial.subst.subst(var);
        partial.specials.push(Rc::new(move |unify| {
            if let Some(name) = unify.resolve_ctor(var) {
                name.to_string()
            } else {
                format!("[unconstrained {:?}]", var)
            }
        }));
        true
    });
}

fn parse_budget_args(
    s: &mut ExpState,
    partial: &PartialExpansion,
    v_name: VarId,
    v_amount: VarId,
) -> Result<(Rc<str>, usize), String> {
    let name = match s.unify.resolve_ctor(partial.subst.subst(v_name)) {
        Some(x) => x,
        None => {
            return Err(format!("name is unconstrained"));
        },
    };
    let amount = match s.unify.resolve_ctor(partial.subst.subst(v_amount)) {
        Some(x) => match usize::from_str(&x) {
            Ok(x) => x,
            Err(e) => {
                return Err(format!("amount is not an integer ({:?})", x));
            },
        },
        None => {
            return Err(format!("amount is unconstrained"));
        },
    };
    Ok((name, amount))
}

fn add_builtin_budget(gb: &mut GrammarBuilder) {
    // All budget nonterminals expand to the empty string.
    let rhs = ProductionRhs { chunks: vec![], nts: vec![] };

    // set_budget[K,V]: sets the current budget for `K` to `V`; expands to the empty string.
    //
    // In all budget productions, if the constructor of the key or the value type is not yet known,
    // then expansion fails.
    let (lhs, vars) = gb.mk_lhs_with_args("set_budget", 2);
    let v_name = vars[0];
    let v_amount = vars[1];
    gb.add_prod_with_handler(lhs, rhs.clone(), move |s, partial, _| {
        let (name, amount) = match parse_budget_args(s, partial, v_name, v_amount) {
            Ok(x) => x,
            Err(e) => {
                eprintln!("warning: set_budget: {}", e);
                return false;
            },
        };
        s.budget.set(&name, amount);
        true
    });

    // add_budget[K,V]: adds `V` to the current budget for `K`; expands to the empty string.
    let (lhs, vars) = gb.mk_lhs_with_args("add_budget", 2);
    let v_name = vars[0];
    let v_amount = vars[1];
    gb.add_prod_with_handler(lhs, rhs.clone(), move |s, partial, _| {
        let (name, amount) = match parse_budget_args(s, partial, v_name, v_amount) {
            Ok(x) => x,
            Err(e) => {
                eprintln!("warning: add_budget: {}", e);
                return false;
            },
        };
        s.budget.add(&name, amount);
        true
    });

    // take_budget[K,V]: subtracts `V` from the current budget for `K`, and expands to the empty
    // string.  If the current budget is less than `V`, it instead fails to expand.
    let (lhs, vars) = gb.mk_lhs_with_args("take_budget", 2);
    let v_name = vars[0];
    let v_amount = vars[1];
    gb.add_prod_with_handler(lhs, rhs.clone(), move |s, partial, _| {
        let (name, amount) = match parse_budget_args(s, partial, v_name, v_amount) {
            Ok(x) => x,
            Err(e) => {
                eprintln!("warning: take_budget: {}", e);
                return false;
            },
        };
        s.budget.take(&name, amount)
    });
}


fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("usage: {} <grammar.txt>", args.get(0).map_or("crux-test-gen", |s| s));
        process::exit(1);
    }

    let mut f = File::open(&args[1]).unwrap();
    let mut src = String::new();
    f.read_to_string(&mut src).unwrap();
    let lines = src.lines().map(|l| l.trim_end()).collect::<Vec<_>>();

    let mut gb = GrammarBuilder::default();
    add_start_production(&mut gb);
    add_builtin_ctor_name(&mut gb);
    add_builtin_budget(&mut gb);
    gb.parse_grammar(&lines);
    let cx = gb.finish();

    let mut conts = vec![Continuation::new(0)];
    while let Some((exp, mut unify)) = expand_next(&cx, &mut conts) {
        println!("{}", render_expansion(&cx, &mut unify, &exp));
    }
}
