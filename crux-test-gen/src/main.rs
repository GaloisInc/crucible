use std::env;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::process;
use std::rc::Rc;

use crate::builder::{GrammarBuilder, ProductionLhs, ProductionRhs};
use crate::ty::{Ty, Subst, UnifyState, VarId};

mod builder;
mod parse;
mod ty;


type NonterminalId = usize;
type ProductionId = usize;

#[derive(Debug, Default)]
pub struct NonterminalRef {
    id: NonterminalId,
    args: Box<[Ty]>,
}

struct ProductionHandler(Box<dyn Fn(&mut ExpState, &mut PartialExpansion) -> bool>);

impl fmt::Debug for ProductionHandler {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "ProductionHandler(..)")
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

#[derive(Debug)]
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
    // ...
}

#[derive(Clone)]
struct ExpState {
    exp: Vec<PartialExpansion>,
    unify: ty::UnifyState,
    // scope: ...,
}

#[derive(Clone)]
/// Represents alternatives not taken during expansion of the grammar.  Can be
/// resumed into a new `ExpState` to generate the next alternative.
struct Continuation {
    state: ExpState,
    alternatives: Vec<ProductionId>,
    next: usize,
}

#[derive(Clone)]
enum ExpResult {
    Progress,
    Done(Expansion, UnifyState),
    Abort,
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
        }
    }

    fn apply_production(
        &mut self,
        cx: &Context,
        production: ProductionId,
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

        if let Some(ref handler) = cx.productions[production].handler {
            let ok = (*handler.0)(self, &mut pe);
            if !ok {
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

    pub fn expand(mut self, cx: &Context) -> (ExpResult, Vec<Continuation>) {
        let mut continuations = Vec::new();

        loop {
            // Pop any finished frames from the expansion stack.
            while self.cur_partial().is_finished() {
                let prev_partial = self.exp.pop().unwrap();
                // TODO: post-expansion actions
                let prev = prev_partial.into_expansion();
                if let Some(cur) = self.exp.last_mut() {
                    cur.subexpansions.push(prev);
                } else {
                    // We popped the last frame.  Expansion is complete.
                    return (ExpResult::Done(prev, self.unify), continuations);
                }
            }

            // The current expansion frame is guaranteed to be unfinished.  Choose a production for
            // its next nonterminal, then apply that production (pushing a new frame).
            let next_nt = self.cur_partial().next_nonterminal(cx);
            let alts = cx.nonterminals[next_nt.id].productions.clone();

            let saved_state = if alts.len() > 1 { Some(self.clone()) } else { None };

            let mut found = false;
            for (i, &alt) in alts.iter().enumerate() {
                if self.apply_production(cx, alt) {
                    found = true;
                    if i < alts.len() - 1 {
                        continuations.push(Continuation {
                            state: saved_state.unwrap(),
                            alternatives: alts,
                            next: i + 1,
                        });
                    }
                    break;
                }
            }
            if !found {
                // There's no way to continue this expansion.
                return (ExpResult::Abort, continuations);
            }
        }
    }
}

impl Continuation {
    pub fn new(production: ProductionId) -> Continuation {
        Continuation {
            state: ExpState::new(),
            alternatives: vec![production],
            next: 0,
        }
    }

    pub fn resume(&mut self, cx: &Context) -> Option<ExpState> {
        if self.next >= self.alternatives.len() {
            return None;
        }

        let mut st = self.state.clone();
        for (i, &alt) in self.alternatives.iter().enumerate().skip(self.next) {
            if st.apply_production(cx, alt) {
                self.next = i + 1;
                return Some(st);
            }
        }
        self.next = self.alternatives.len();
        None
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

fn add_builtin_ctor_name(gb: &mut GrammarBuilder) {
    let (lhs, vars) = gb.mk_lhs_with_args("ctor_name", 1);
    let var = vars[0];
    let rhs = ProductionRhs {
        chunks: vec![Chunk::Special(0)],
        nts: vec![],
    };
    gb.add_prod_with_handler(lhs, rhs, move |_, partial| {
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
    gb.parse_grammar(&lines);
    let cx = gb.finish();

    eprintln!("{:#?}", cx);

    let mut conts = vec![Continuation::new(0)];
    while let Some((exp, mut unify)) = expand_next(&cx, &mut conts) {
        println!("{}", render_expansion(&cx, &mut unify, &exp));
    }
}
