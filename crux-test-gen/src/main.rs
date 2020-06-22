use std::rc::Rc;

type NonterminalId = usize;
type ProductionId = usize;

struct Production {
    chunks: Vec<Chunk>,
    nts: Vec<NonterminalId>,
}

struct Nonterminal {
    productions: Vec<ProductionId>
}

struct Context {
    productions: Vec<Production>,
    nonterminals: Vec<Nonterminal>,
}

enum Chunk {
    /// A chunk of literal text.  Must not contain newlines.  The `bool`
    /// indicates whether to insert a newline after this text.
    Text(Rc<str>, bool),
    /// Increases or decreases the current indentation level.
    Indent(isize),
    /// Expand the nonterminal at the given index.
    Nt(usize),
}

#[derive(Clone)]
struct Expansion {
    production: ProductionId,
    subexpansions: Box<[Expansion]>,
}

#[derive(Clone)]
struct PartialExpansion {
    production: ProductionId,
    num_nts: usize,
    subexpansions: Vec<Expansion>,
    // ...
}

#[derive(Clone)]
struct ExpState {
    exp: Vec<PartialExpansion>,
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
    Done(Expansion),
    Abort,
}



impl PartialExpansion {
    pub fn new(cx: &Context, production: ProductionId) -> PartialExpansion {
        let num_nts = cx.productions[production].nts.len();
        let subexpansions = Vec::with_capacity(num_nts);
        PartialExpansion {
            production,
            num_nts,
            subexpansions,
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
        }
    }

    fn next_nonterminal(&self, cx: &Context) -> NonterminalId {
        let idx = self.subexpansions.len();
        cx.productions[self.production].nts[idx]
    }
}

impl ExpState {
    fn new() -> ExpState {
        ExpState {
            exp: Vec::new(),
        }
    }

    fn apply_production(&mut self, cx: &Context, production: ProductionId) {
        let mut pe = PartialExpansion::new(cx, production);
        // TODO: pre-expansion actions
        if pe.is_finished() {
            // TODO: post-expansion actions
            self.cur_partial_mut().subexpansions.push(pe.into_expansion());
        } else {
            self.exp.push(pe);
        }
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
                    return (ExpResult::Done(prev), continuations);
                }
            }

            // The current expansion frame is guaranteed to be unfinished.  Choose a production for
            // its next nonterminal, then apply that production (pushing a new frame).
            let next_nt = self.cur_partial().next_nonterminal(cx);
            let alts = cx.nonterminals[next_nt].productions.clone();

            let next_prod = if alts.len() == 0 {
                // There's no way to continue this expansion.
                return (ExpResult::Abort, continuations);
            } else if alts.len() == 1 {
                alts[0]
            } else {
                let prod = alts[0];
                continuations.push(Continuation {
                    state: self.clone(),
                    alternatives: alts,
                    next: 1,
                });
                prod
            };
            self.apply_production(cx, next_prod);
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
        st.apply_production(cx, self.alternatives[self.next]);
        self.next += 1;
        Some(st)
    }
}

fn expand_next(cx: &Context, continuations: &mut Vec<Continuation>) -> Option<Expansion> {
    while let Some(cont) = continuations.last_mut() {
        if let Some(state) = cont.resume(cx) {
            let (result, new_continuations) = state.expand(cx);
            continuations.extend(new_continuations);
            match result {
                ExpResult::Done(exp) => return Some(exp),
                ExpResult::Abort => {},
                ExpResult::Progress => unimplemented!(),
            }
        } else {
            continuations.pop();
        }
    }
    None
}


fn render_expansion(cx: &Context, exp: &Expansion) -> String {
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
        }
    }

    output
}


fn main() {
    let cx = Context {
        productions: vec![
            // S -> XX
            Production {
                chunks: vec![Chunk::Nt(0), Chunk::Nt(1)],
                nts: vec![1, 1],
            },
            // X -> "a"
            Production {
                chunks: vec![Chunk::Text("a".to_owned().into(), false)],
                nts: vec![],
            },
            // X -> "b"
            Production {
                chunks: vec![Chunk::Text("b".to_owned().into(), false)],
                nts: vec![],
            },
        ],
        nonterminals: vec![
            // S
            Nonterminal {
                productions: vec![0],
            },
            // X
            Nonterminal {
                productions: vec![1, 2],
            },
        ],
    };

    let mut conts = vec![Continuation::new(0)];
    while let Some(exp) = expand_next(&cx, &mut conts) {
        println!("{}", render_expansion(&cx, &exp));
    }
}
