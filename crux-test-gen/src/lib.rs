use std::collections::HashMap;
use std::fmt;
use std::fs::File;
use std::io::{self, Read};
use std::path::Path;
use std::rc::Rc;
use std::str::FromStr;

use crate::builder::{GrammarBuilder, ProductionRhs};
use crate::ty::{Ty, Subst, VarId};

mod builder;
mod parse;
mod ty;

pub use self::ty::UnifyState;


type NonterminalId = usize;
type ProductionId = usize;

#[derive(Clone, Debug, Default)]
struct NonterminalRef {
    id: NonterminalId,
    args: Box<[Ty]>,
}

impl NonterminalRef {
    fn nullary(id: NonterminalId) -> NonterminalRef {
        NonterminalRef {
            id,
            args: Box::new([]),
        }
    }
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
struct ProductionHandler(
    Box<dyn Fn(&Context, &mut ExpState, &mut PartialExpansion, usize) -> bool>,
);

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
struct Production {
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
struct Nonterminal {
    /// All productions for this nonterminal.  This is an upper bound on possible expansion
    /// options; some productions may not be valid for the `args` of a given `NonterminalRef`.
    productions: Vec<ProductionId>
}

#[derive(Debug, Default)]
pub struct Context {
    productions: Vec<Production>,
    nonterminals: Vec<Nonterminal>,
    nonterminals_by_name: HashMap<String, NonterminalId>,
}

#[derive(Clone, Debug)]
enum Chunk {
    /// A chunk of literal text.  Must not contain newlines.  The `bool`
    /// indicates whether to insert a newline after this text.
    Text(Rc<str>, bool),
    /// Increases or decreases the current indentation level.
    Indent(isize),
    /// Expand the nonterminal at the given index.
    Nt(usize),
    /// Add a newline, if the current line is nonempty.
    ///
    /// In a multiline production, when a nonterminal appears on a line by itself, it's followed by
    /// a `MagicNewline` instead of `Text("", true)`.  This avoids inserting a blank line when the
    /// nonterminal expands to the empty string, allowing the user to set up scopes and budgets
    /// using one command per line, without adding a bunch of unwanted blank lines to the output.
    MagicNewline,

    Special(usize),
}

#[derive(Clone)]
pub struct Expansion {
    production: ProductionId,
    subexpansions: Box<[Expansion]>,
    specials: Box<[Rc<dyn Fn(&mut RenderContext) -> String>]>,
}

#[derive(Clone)]
struct PartialExpansion {
    production: ProductionId,
    /// Translation from local type variables of the production to global `VarId`s in the parent
    /// `ExpState`'s `unify` table.
    subst: Subst,
    num_nts: usize,
    subexpansions: Vec<Expansion>,
    specials: Vec<Rc<dyn Fn(&mut RenderContext) -> String>>,
}

#[derive(Clone)]
struct ExpState {
    root_nt: Rc<NonterminalRef>,
    root_subst: Subst,
    exp: Vec<PartialExpansion>,
    unify: ty::UnifyState,
    budget: Budget,
    scopes: Vec<Scope>,
}

/// Snapshot of the use site of a nested expansion.  This contains all the fields of `ExpState`
/// except for `exp` (which starts empty in the nested expansion) and `unify` (which will be filled
/// in with the final `UnifyState` of the parent expansion).
#[derive(Clone)]
struct NestedSnapshot {
    root_nt: Rc<NonterminalRef>,
    root_subst: Subst,
    budget: Budget,
    scopes: Vec<Scope>,
}

/// Represents alternatives not taken during expansion of the grammar.  Can be
/// resumed into a new `ExpState` to generate the next alternative.
#[derive(Clone)]
pub struct BranchingState {
    continuations: Vec<Continuation>,
    expansion_counter: usize,
}

pub struct RenderContext<'a> {
    pub cx: &'a Context,
    pub unify: UnifyState,
    pub counter: usize,
}

#[derive(Clone)]
struct Continuation {
    state: ExpState,
    kind: ContinuationKind,
}

#[derive(Clone)]
enum ContinuationKind {
    /// Continue with the next in a sequence of alternative productions.
    Alts {
        /// The IDs of productions to try.  The continuation is resumed by applying
        /// `alternatives[next]` to the next unexpanded nonterminal in the `ExpState`.
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

// TODO: replace with a struct wrapped in Option
#[derive(Clone)]
enum ExpResult {
    Done(Expansion, UnifyState),
    Abort,
}


#[derive(Clone, Default, Debug)]
struct Budget(HashMap<String, usize>);

impl Budget {
    pub fn set(&mut self, key: &str, amount: usize) {
        self.0.insert(key.to_owned(), amount);
    }

    pub fn get(&mut self, key: &str) -> usize {
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
                // budget will fail.
                amount == 0
            },
        }
    }
}


/// A local variable scope.
///
/// Terminology note: we use "locals" to refer to variables in the target program, as managed by
/// `fresh_local` and related builtins.  "Var", in contrast, refers to a type variable in the
/// grammar.
#[derive(Clone)]
struct Scope {
    first_local_id: usize,
    locals: Vec<Local>,
    /// Whether it's possible to `take` variables from scopes outside this one.
    take_outside_mode: TakeMode,
}

#[derive(Clone)]
struct Local {
    /// The grammar-level type of this local.  Typically, the grammar will use types that mirror
    /// those of the target language, though this is not a strict requirement.  Since the type is
    /// taken from the argument of the `fresh_local` production, we simply store a type variable
    /// here (in the global `UnifyState` namespace, i.e., already substituted) and rely on
    /// unification to map it to a concrete type.
    ty: VarId,
    /// Whether this local has been consumed via the `take_local` production.  Consumed locals
    /// won't be returned by future `choose_local` or `take_local` productions.
    taken: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TakeMode {
    Block,
    Allow,
}

impl Scope {
    pub fn new(first_local_id: usize, take_outside_mode: TakeMode) -> Scope {
        Scope {
            first_local_id,
            locals: Vec::new(),
            take_outside_mode,
        }
    }

    pub fn fresh_local(&mut self, ty: VarId) -> usize {
        let idx = self.locals.len();
        self.locals.push(Local { ty, taken: false });
        self.first_local_id + idx
    }

    pub fn index_ok(&self, idx: usize) -> bool {
        self.first_local_id <= idx && idx < self.first_local_id + self.locals.len()
    }

    /// Get the type of the local whose index is `idx`.  Returns `None` if the local has already
    /// been consumed or if `idx` is not valid for this scope (`!self.index_ok(idx)`).
    pub fn get_ty(&self, idx: usize) -> Option<VarId> {
        let rel_idx = idx.checked_sub(self.first_local_id)?;
        let l = self.locals.get(rel_idx)?;
        if !l.taken {
            return Some(l.ty);
        }
        None

    }

    /// Mark the local at `idx` as taken.  Afterward, `get_ty` will return `None` for this local.
    /// This function panics if `idx` is not valid for this scope.
    pub fn take(&mut self, idx: usize) {
        self.locals[idx - self.first_local_id].taken = true;
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
    fn new(root_nt: NonterminalRef) -> ExpState {
        ExpState {
            root_nt: Rc::new(root_nt),
            root_subst: Subst::empty(),
            exp: Vec::new(),
            unify: UnifyState::new(),
            budget: Budget::default(),
            scopes: Vec::new(),
        }
    }

    /// Take a snapshot of this state for future nested expansion of `root_nt`.  Type variables in
    /// `root_nt` will be interpreted according to `root_subst`.
    ///
    /// In general, it does not make sense to propagate unification constraints out of a nested
    /// expansion state, since the state may be forked (cloned) multiple times, with different
    /// constraints in each fork.  However, we do support propagating constaints inward, including
    /// constraints that are added to the parent state after the snapshot is taken.  This works
    /// through a two-step process: first, `nested_snapshot` captures information about the use
    /// site of the nested expansion; later, `activate` adds the final `UnifyState` of the parent
    /// expansion (which may contain constraints from after the use site) to produce a complete
    /// `ExpState` for the nested expansion.
    fn nested_snapshot(&self, root_nt: NonterminalRef, root_subst: Subst) -> NestedSnapshot {
        NestedSnapshot {
            root_nt: Rc::new(root_nt),
            root_subst,
            budget: self.budget.clone(),
            scopes: self.scopes.clone(),
        }
    }

    /// Build a new `ExpState` for immediate nested expansion.
    fn nested(&self, root_nt: NonterminalRef, root_subst: Subst) -> ExpState {
        self.nested_snapshot(root_nt, root_subst)
            .activate(self.unify.clone())
    }

    fn apply_production(
        &mut self,
        cx: &Context,
        production: ProductionId,
        index: Option<usize>,
    ) -> bool {
        let mut pe = PartialExpansion::new(cx, &mut self.unify, production);

        // Get the type arguments of the nonterminal being substituted.
        let tys1 = if !self.exp.is_empty() {
            // Type variables in the nonterminal are bound by the enclosing production.
            // `cur_partial.subst` assigns a global unification variable to each local variable in
            // the current instance of that production.
            self.cur_partial().subst.clone()
                .and(&self.cur_partial().next_nonterminal(cx).args as &[_])
        } else {
            // The root nonterminal can refer to variables defined in the root subst.
            self.root_subst.clone().and(&self.root_nt.args as &[_])
        };

        // Unify nonterminal's type arguments with the type arguments of the production.
        let tys2 = pe.subst.clone().and(&cx.productions[production].args as &[_]);
        if !self.unify.unify(tys1, tys2) {
            return false;
        }

        // Sanity check.  This will fail if a nonterminal has multiple productions and at least one
        // is a production family.
        assert!(cx.productions[production].multiplicity.is_some() == index.is_some());

        if let Some(ref handler) = cx.productions[production].handler {
            let ok = (*handler.0)(cx, self, &mut pe, index.unwrap_or(0));
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

        if pe.is_finished() && !self.exp.is_empty() {
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

    fn expand(self, cx: &Context) -> (ExpResult, Vec<Continuation>) {
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

    fn cur_scope(&self) -> Option<&Scope> {
        self.scopes.last()
    }

    fn cur_scope_mut(&mut self) -> Option<&mut Scope> {
        self.scopes.last_mut()
    }

    fn count_locals(&self) -> usize {
        self.cur_scope().map_or(0, |s| s.first_local_id + s.locals.len())
    }

    fn get_local(&self, idx: usize) -> Option<VarId> {
        for s in self.scopes.iter() {
            if s.index_ok(idx) {
                return s.get_ty(idx);
            }
        }
        None
    }

    /// Try to take / consume local `idx`.  Returns `true` on success, or `false` on failure, which
    /// happens when `idx` is in an outer scope, but an inner scope forbids taking variables from
    /// the outer scope.
    fn take_local(&mut self, idx: usize) -> bool {
        for s in self.scopes.iter_mut().rev() {
            if s.index_ok(idx) {
                s.take(idx);
                return true;
            }
            if s.take_outside_mode == TakeMode::Block {
                break;
            }
        }
        false
    }

    fn push_scope(&mut self, take_outside_mode: TakeMode) {
        let next_id = self.count_locals();
        self.scopes.push(Scope::new(next_id, take_outside_mode));
    }

    /// Pop a scope from the stack.  Returns `true` on success, or `false` if there were no scopes
    /// to pop.
    fn pop_scope(&mut self) -> bool {
        self.scopes.pop().is_some()
    }
}

impl NestedSnapshot {
    /// Activate a snapshot for nested expansion by providing the final `UnifyState` of its parent
    /// expansion.
    fn activate(self, unify: UnifyState) -> ExpState {
        let NestedSnapshot { root_nt, root_subst, budget, scopes } = self;
        let exp = Vec::new();
        ExpState { root_nt, root_subst, exp, unify, budget, scopes }
    }
}

impl Continuation {
    fn new(cx: &Context, root_nt: NonterminalRef) -> Continuation {
        Continuation::from_state(cx, ExpState::new(root_nt))
    }

    /// Build a `Continuation` that tries every production for the root nonterminal of `state`.
    fn from_state(cx: &Context, state: ExpState) -> Continuation {
        let prods = cx.nonterminals[state.root_nt.id].productions.clone();
        Continuation {
            state,
            kind: ContinuationKind::Alts {
                alternatives: prods,
                next: 0,
            },
        }
    }

    fn resume(&mut self, cx: &Context) -> Option<ExpState> {
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

impl BranchingState {
    fn new(cont: Continuation) -> BranchingState {
        BranchingState {
            continuations: vec![cont],
            expansion_counter: 0,
        }
    }

    pub fn empty() -> BranchingState {
        BranchingState {
            continuations: vec![],
            expansion_counter: 0,
        }
    }

    fn next_counter(&mut self) -> usize {
        let x = self.expansion_counter;
        self.expansion_counter += 1;
        x
    }
}


pub fn expand_next<'a>(
    cx: &'a Context,
    branching: &mut BranchingState,
) -> Option<(Expansion, RenderContext<'a>)> {
    while let Some(cont) = branching.continuations.last_mut() {
        if let Some(state) = cont.resume(cx) {
            let (result, new_continuations) = state.expand(cx);
            branching.continuations.extend(new_continuations);
            match result {
                ExpResult::Done(exp, unify) => {
                    let counter = branching.next_counter();
                    let rcx = RenderContext { cx, unify, counter };
                    return Some((exp, rcx));
                },
                ExpResult::Abort => {},
            }
        } else {
            branching.continuations.pop();
        }
    }
    None
}


pub fn render_expansion(rcx: &mut RenderContext, exp: &Expansion) -> String {
    let mut stack: Vec<(&Chunk, &Expansion)> = Vec::new();
    for chunk in rcx.cx.productions[exp.production].chunks.iter().rev() {
        stack.push((chunk, exp));
    }

    let mut output = String::new();
    let mut indent = String::new();
    let mut start_of_line = true;
    while let Some((chunk, exp)) = stack.pop() {
        match *chunk {
            Chunk::Text(ref s, newline) => {
                // Avoid indenting if `s` is empty.
                if s.len() > 0 {
                    if start_of_line {
                        output.push_str(&indent);
                    }
                    start_of_line = false;
                    output.push_str(s);
                }
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
                for subchunk in rcx.cx.productions[subexp.production].chunks.iter().rev() {
                    stack.push((subchunk, subexp));
                }
            },
            Chunk::MagicNewline => {
                if !start_of_line {
                    output.push('\n');
                    start_of_line = true;
                }
            },
            Chunk::Special(idx) => {
                output.push_str(&(exp.specials[idx])(rcx));
            },
        }
    }

    output
}


pub struct IterRendered<'a> {
    cx: &'a Context,
    bcx: BranchingState,
}

impl<'a> Iterator for IterRendered<'a> {
    type Item = String;
    fn next(&mut self) -> Option<String> {
        let (exp, mut rcx) = expand_next(self.cx, &mut self.bcx)?;
        Some(render_expansion(&mut rcx, &exp))
    }
}

/// Return an iterator over all expansions of the named nonterminal.
pub fn iter_rendered<'a>(cx: &'a Context, nonterminal: &str) -> IterRendered<'a> {
    let bcx = match cx.nonterminals_by_name.get(nonterminal) {
        Some(&nt_id) => {
            let cont = Continuation::new(cx, NonterminalRef::nullary(nt_id));
            BranchingState::new(cont)
        },
        None => BranchingState::empty(),
    };
    IterRendered { cx, bcx }
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
    gb.add_prod_with_handler(lhs, rhs, move |_, _, partial, _| {
        let var = partial.subst.subst(var);
        partial.specials.push(Rc::new(move |rcx| {
            if let Some(name) = rcx.unify.resolve_ctor(var) {
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
                return Err(format!("error parsing amount {:?}: {}", x, e));
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
    gb.add_prod_with_handler(lhs, rhs.clone(), move |_, s, partial, _| {
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
    gb.add_prod_with_handler(lhs, rhs.clone(), move |_, s, partial, _| {
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
    gb.add_prod_with_handler(lhs, rhs.clone(), move |_, s, partial, _| {
        let (name, amount) = match parse_budget_args(s, partial, v_name, v_amount) {
            Ok(x) => x,
            Err(e) => {
                eprintln!("warning: take_budget: {}", e);
                return false;
            },
        };
        s.budget.take(&name, amount)
    });

    // check_budget[K,V]: if the current budget for `K` is exactly `V`, expands to the empty
    // string.  Otherwise, it fails to expand.  `check_budget[foo, 0]` is useful for asserting that
    // all provided budget for `foo` must be consumed by the end of expansion.
    let (lhs, vars) = gb.mk_lhs_with_args("check_budget", 2);
    let v_name = vars[0];
    let v_amount = vars[1];
    gb.add_prod_with_handler(lhs, rhs.clone(), move |_, s, partial, _| {
        let (name, amount) = match parse_budget_args(s, partial, v_name, v_amount) {
            Ok(x) => x,
            Err(e) => {
                eprintln!("warning: check_budget: {}", e);
                return false;
            },
        };
        s.budget.get(&name) == amount
    });
}

fn add_builtin_locals(gb: &mut GrammarBuilder) {
    let empty_rhs = ProductionRhs { chunks: vec![], nts: vec![] };
    let special_rhs = ProductionRhs { chunks: vec![Chunk::Special(0)], nts: vec![] };

    // fresh_local[T]: declares a fresh local of type `T`, and expands to the name of the new
    // local.  The local is added to the innermost open scope; if no scopes are open, expansion
    // fails.  Currently, the name of the local is not customizable: it always consists of `x`
    // followed by a number.
    let (lhs, vars) = gb.mk_lhs_with_args("fresh_local", 1);
    let v_ty = vars[0];
    gb.add_prod_with_handler(lhs, special_rhs.clone(), move |_, s, partial, _| {
        let scope = match s.cur_scope_mut() {
            Some(x) => x,
            None => return false,
        };
        let local_id = scope.fresh_local(partial.subst.subst(v_ty));
        partial.specials.push(Rc::new(move |_| format!("x{}", local_id)));
        true
    });

    // choose_local[T]: expands to the name of a local of type `T`.  Specifically, this looks for a
    // local whose type unifies with `T`, so it works even if `T` or the local's type is
    // underconstrained.  
    let (lhs, vars) = gb.mk_lhs_with_args("choose_local", 1);
    let v_ty = vars[0];
    gb.add_prod_family(
        lhs,
        special_rhs.clone(),
        move |s| s.count_locals(),
        move |_, s, partial, index| {
            let local_ty_var = match s.get_local(index) {
                Some(x) => x,
                // Might return `None` if the variable at `index` was consumed by `take_local`.
                None => return false,
            };
            let arg_ty_var = partial.subst.subst(v_ty);
            if !s.unify.unify_vars(local_ty_var, arg_ty_var) {
                return false;
            }
            // Success - the var at `index` has the requested type.  Expand to its name.
            partial.specials.push(Rc::new(move |_| format!("x{}", index)));
            true
        },
    );

    // take_local[T]: expands to the name of a local of type `T`, and removes that local from its
    // containing scope.
    let (lhs, vars) = gb.mk_lhs_with_args("take_local", 1);
    let v_ty = vars[0];
    gb.add_prod_family(
        lhs,
        special_rhs.clone(),
        move |s| s.count_locals(),
        move |_, s, partial, index| {
            let local_ty_var = match s.get_local(index) {
                Some(x) => x,
                None => return false,
            };
            let arg_ty_var = partial.subst.subst(v_ty);
            if !s.unify.unify_vars(local_ty_var, arg_ty_var) {
                return false;
            }
            // Consume the local at `index`, if that's allowed.
            if !s.take_local(index) {
                return false;
            }
            // Success - the local at `index` has the requested type, and is consumable.  Expand to
            // its name.
            partial.specials.push(Rc::new(move |_| format!("x{}", index)));
            true
        },
    );

    // push_scope: pushes a new scope for tracking locals, and expands to the empty string.  Any
    // locals declared in the new scope will be discarded at the matching `pop_scope`.
    let lhs = gb.mk_simple_lhs("push_scope");
    gb.add_prod_with_handler(lhs, empty_rhs.clone(), move |_, s, _, _| {
        s.push_scope(TakeMode::Allow);
        true
    });

    // push_borrowed_scope: like `push_scope`, but forbids `take_local` from consuming locals that
    // were introduced outside the new scope.  This is useful for the bodies of Rust `Fn`/`FnMut`
    // closures, which can read and write variables from outer scopes, but cannot move them.
    let lhs = gb.mk_simple_lhs("push_borrowed_scope");
    gb.add_prod_with_handler(lhs, empty_rhs.clone(), move |_, s, _, _| {
        s.push_scope(TakeMode::Block);
        true
    });

    // pop_scope: pops the innermost scope, erasing any locals it contains, and expands to the
    // empty string.  If there is no open scope, expansion fails.
    let lhs = gb.mk_simple_lhs("pop_scope");
    gb.add_prod_with_handler(lhs, empty_rhs.clone(), move |_, s, _, _| {
        s.pop_scope()
    });
}

fn add_builtin_counter(gb: &mut GrammarBuilder) {
    let special_rhs = ProductionRhs { chunks: vec![Chunk::Special(0)], nts: vec![] };

    // expansion_counter: Expands to an integer indicating the index of the current expansion.
    let lhs = gb.mk_simple_lhs("expansion_counter");
    gb.add_prod_with_handler(lhs, special_rhs, move |_, _, partial, _| {
        partial.specials.push(Rc::new(move |rcx| format!("{}", rcx.counter)));
        true
    });
}

fn parse_expand_args(
    cx: &Context,
    s: &mut ExpState,
    partial: &PartialExpansion,
    v_nt: VarId,
) -> Option<(Option<NonterminalRef>, Subst)> {
    let res = s.unify.resolve(partial.subst.subst(v_nt))?;
    let ctor_ty = res.val;
    let nt_ref = match cx.nonterminals_by_name.get(&ctor_ty.ctor as &str) {
        Some(&id) => {
            let args = (&ctor_ty.args as &[_]).to_owned().into_boxed_slice();
            Some(NonterminalRef { id, args })
        },
        None => None,
    };
    Some((nt_ref, res.subst))
}

fn add_builtin_expand(gb: &mut GrammarBuilder) {
    let special_rhs = ProductionRhs { chunks: vec![Chunk::Special(0)], nts: vec![] };

    // expand_all[nt]: Expands to all possible expansions of `nt` in the current context,
    // concatenated together.
    //
    // Type variable unification propagates "into" `expand_all`, but not "out" of it.  The
    // `expand_all` builtin expands its argument multiple times, potentially making different
    // unification decisions each time, so there is no single set of constraints that could be
    // propagated out.  However, all constraints from the enclosing context apply when expanding
    // the argument of the `expand_all`.  The expansion of the `expand_all`'s argument is delayed
    // until after the parent expansion is complete, so this even includes constraints added after
    // the expansion of the `expand_all` itself.
    let (lhs, vars) = gb.mk_lhs_with_args("expand_all", 1);
    let var = vars[0];
    gb.add_prod_with_handler(lhs, special_rhs.clone(), move |cx, s, partial, _| {
        let (nt_ref, subst) = match parse_expand_args(cx, s, partial, var) {
            Some((Some(nt_ref), subst)) => (nt_ref, subst),
            Some((None, _)) => {
                // `expand_all[bad_nt]` succeeds even when `bad_nt` doesn't exist in the grammar,
                // expanding to the empty string, as there are no productions for `bad_nt`.  We
                // handle this as a special case.
                partial.specials.push(Rc::new(move |_| String::new()));
                return true;
            },
            None => {
                eprintln!("warning: expand_all: argument is unconstrained");
                return false;
            },
        };

        // Snapshot the current state (budgets, scopes, etc) for future use during rendering.
        let snapshot = s.nested_snapshot(nt_ref, subst);

        partial.specials.push(Rc::new(move |rcx| {
            // Now that we have the final `UnifyState` for the parent expansion, we can run the
            // nested expansions.
            let state = snapshot.clone().activate(rcx.unify.clone());
            let bcx = BranchingState::new(Continuation::from_state(rcx.cx, state));
            let mut s = String::new();
            for exp in (IterRendered { cx: rcx.cx, bcx }) {
                s.push_str(&exp);
            }
            s
        }));
        true
    });

    // expand_first[nt]: Expands to the first expansion of `nt` that is legal in the current
    // context.  Fails to expand if no expansions of `nt` are legal.
    //
    // Unlike `expand_all`, `expand_first` propagates type variable unification in both directions.
    // The nested expansion of `nt` happens immediately, and any new constraints are propagated
    // back to the parent expansion's `UnifyState`.
    //
    // `expand_first` never backtracks into alternate expansions of `nt` beyond the first one that
    // succeeds.  If the first expansion of `nt` adds constraints that are inconsistent with some
    // later constraints, then the entire parent expansion will fail, instead of trying a different
    // expansion of `nt`.
    let (lhs, vars) = gb.mk_lhs_with_args("expand_first", 1);
    let var = vars[0];
    gb.add_prod_with_handler(lhs, special_rhs.clone(), move |cx, s, partial, _| {
        let (nt_ref, subst) = match parse_expand_args(cx, s, partial, var) {
            Some((Some(nt_ref), subst)) => (nt_ref, subst),
            Some((None, _)) => {
                // `expand_first[bad_nt]` fails, as there are no productions for `bad_nt`.
                return false;
            },
            None => {
                eprintln!("warning: expand_first: argument is unconstrained");
                return false;
            },
        };

        // Snapshot the current state (budgets, scopes, etc) for future use during rendering.
        let state = s.nested(nt_ref, subst);
        let mut bcx = BranchingState::new(Continuation::from_state(cx, state));
        let exp = match expand_next(cx, &mut bcx) {
            Some((exp, rcx)) => {
                // Copy the nested expansion's unification state back into the enclosing state `s`.
                s.unify = rcx.unify;
                exp
            },
            None => return false,
        };

        // Wait until we have the final `RenderContext` to actually render `exp`.
        partial.specials.push(Rc::new(move |rcx| {
            render_expansion(rcx, &exp)
        }));
        true
    });
}


pub fn parse_grammar_from_str(src: &str) -> Context {
    let lines = src.lines().map(|l| l.trim_end()).collect::<Vec<_>>();

    let mut gb = GrammarBuilder::default();
    add_builtin_ctor_name(&mut gb);
    add_builtin_budget(&mut gb);
    add_builtin_locals(&mut gb);
    add_builtin_counter(&mut gb);
    add_builtin_expand(&mut gb);
    gb.parse_grammar(&lines);

    gb.finish()
}

pub fn parse_grammar_from_file<P: AsRef<Path>>(path: P) -> io::Result<Context> {
    let mut f = File::open(path)?;
    let mut src = String::new();
    f.read_to_string(&mut src)?;
    Ok(parse_grammar_from_str(&src))
}
