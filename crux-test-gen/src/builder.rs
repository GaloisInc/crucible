use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use crate::{
    Context, Production, ProductionHandler, Nonterminal, NonterminalId,
    NonterminalRef, Chunk, ExpState, PartialExpansion,
};
use crate::ty::{Ty, VarId};


#[derive(Default)]
pub struct GrammarBuilder {
    prods: Vec<Production>,
    nts: Vec<Nonterminal>,

    nts_by_name: HashMap<String, NonterminalId>,
    text_interner: HashSet<Rc<str>>,
}

#[derive(Clone)]
pub struct ProductionLhs {
    pub vars: Vec<Rc<str>>,
    pub nt: NonterminalRef,
}

#[derive(Clone, Default)]
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
        self.add_prod_with_opt_handler(lhs, rhs, None)
    }

    pub fn add_prod_with_handler(
        &mut self,
        lhs: ProductionLhs,
        rhs: ProductionRhs,
        handler: impl Fn(&mut ExpState, &mut PartialExpansion, usize) -> bool + 'static,
    ) -> usize {
        self.add_prod_with_opt_handler(lhs, rhs, Some(ProductionHandler(Box::new(handler))))
    }

    pub fn add_prod_with_opt_handler(
        &mut self,
        lhs: ProductionLhs,
        rhs: ProductionRhs,
        handler: Option<ProductionHandler>,
    ) -> usize {
        let ProductionLhs { vars, nt } = lhs;
        let ProductionRhs { chunks, nts } = rhs;

        let id = self.prods.len();
        self.prods.push(Production {
            vars,
            args: nt.args.into(),
            chunks,
            nts,
            handler,
            multiplicity: None,
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

    pub fn mk_lhs_with_args(&mut self, name: &str, n: usize) -> (ProductionLhs, Vec<VarId>) {
        let lhs = ProductionLhs {
            vars: (0..n).map(|i| format!("T{}", i).into()).collect(),
            nt: NonterminalRef {
                id: self.nt_id(name),
                args: (0..n).map(|i| Ty::Var(VarId(i as u32))).collect(),
            },
        };
        let vars = (0..n).map(|i| VarId(i as u32)).collect();
        (lhs, vars)
    }

    pub fn finish(self) -> Context {
        Context {
            productions: self.prods,
            nonterminals: self.nts,
        }
    }
}


