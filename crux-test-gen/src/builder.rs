use std::cmp;
use std::collections::{HashMap, HashSet};
use std::io::{self, Read};
use std::rc::Rc;
use regex::Regex;
use crate::{Context, Production, Nonterminal, ProductionId, NonterminalId, NonterminalRef, Chunk};
use crate::ty::{Ty, CtorTy, VarId};


#[derive(Default)]
pub struct GrammarBuilder {
    prods: Vec<Production>,
    nts: Vec<Nonterminal>,

    nts_by_name: HashMap<String, NonterminalId>,
    text_interner: HashSet<Rc<str>>,
}

pub struct ProductionLhs {
    pub vars: Vec<Rc<str>>,
    pub nt: NonterminalRef,
}

#[derive(Default)]
pub struct ProductionRhs {
    pub chunks: Vec<Chunk>,
    pub nts: Vec<NonterminalRef>,
}

impl GrammarBuilder {
    pub fn nt_id(&mut self, name: &str) -> NonterminalId {
        if let Some(&id) = self.nts_by_name.get(name) {
            id
        } else {
            let id = self.nts.len();
            self.nts.push(Nonterminal::default());
            self.nts_by_name.insert(name.to_owned(), id);
            id
        }
    }

    pub fn add_prod(&mut self, lhs: ProductionLhs, rhs: ProductionRhs) -> usize {
        let ProductionLhs { vars, nt } = lhs;
        let ProductionRhs { chunks, nts } = rhs;

        let id = self.prods.len();
        self.prods.push(Production {
            vars,
            args: nt.args.into(),
            chunks,
            nts,
        });
        self.nts[nt.id].productions.push(id);
        id
    }

    pub fn intern_text(&mut self, s: &str) -> Rc<str> {
        if let Some(x) = self.text_interner.get(s) {
            return x.clone();
        } else {
            let x: Rc<str> = s.into();
            self.text_interner.insert(x.clone());
            x
        }
    }

    pub fn mk_simple_nt_ref(&mut self, name: &str) -> NonterminalRef {
        NonterminalRef {
            id: self.nt_id(name),
            args: Box::new([]),
        }
    }

    pub fn mk_simple_lhs(&mut self, name: &str) -> ProductionLhs {
        ProductionLhs {
            vars: Vec::new(),
            nt: self.mk_simple_nt_ref(name),
        }
    }

    pub fn finish(self) -> Context {
        Context {
            productions: self.prods,
            nonterminals: self.nts,
        }
    }
}


