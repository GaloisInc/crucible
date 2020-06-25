use std::ops::Deref;
use std::rc::Rc;
use ena::unify::{InPlaceUnificationTable, UnifyKey, UnifyValue};


#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct VarId(u32);

impl UnifyKey for VarId {
    type Value = Option<Term>;
    fn index(&self) -> u32 { self.0 }
    fn from_index(x: u32) -> Self { Self(x) }
    fn tag() -> &'static str { "var" }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Ctor(Rc<CtorTy>),
    Var(VarId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CtorTy {
    ctor: Rc<str>,
    args: Rc<[Ty]>,
}

impl Ty {
    fn maybe_subst(&self, vars: &[VarId]) -> Option<Ty> {
        match *self {
            Ty::Ctor(ref c) => Some(Ty::Ctor(Rc::new(c.maybe_subst(vars)?))),
            Ty::Var(v) => {
                let new_var = vars[v.0 as usize];
                if v != new_var {
                    Some(Ty::Var(new_var))
                } else {
                    None
                }
            },
        }
    }

    pub fn subst(self, vars: &[VarId]) -> Ty {
        self.maybe_subst(vars).unwrap_or(self)
    }
}

impl CtorTy {
    fn maybe_subst(&self, vars: &[VarId]) -> Option<CtorTy> {
        let mut changed = false;
        let new_args = self.args.iter().map(|ty| {
            if let Some(new_ty) = ty.maybe_subst(vars) {
                changed = true;
                new_ty
            } else {
                ty.clone()
            }
        }).collect::<Rc<[_]>>();

        if changed {
            Some(CtorTy {
                ctor: self.ctor.clone(),
                args: new_args,
            })
        } else {
            None
        }
    }

    pub fn subst(self, vars: &[VarId]) -> CtorTy {
        self.maybe_subst(vars).unwrap_or(self)
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Term(SubstAnd<Rc<CtorTy>>);

impl UnifyValue for Term {
    type Error = ();
    fn unify_values(a: &Self, b: &Self) -> Result<Self, ()> {
        let ac = &a.0.val;
        let bc = &b.0.val;
        // Unification of `a.args` with `b.args` happens separately, since we can't perform it
        // here (no access to the unification table).
        if ac.ctor == bc.ctor && ac.args.len() == bc.args.len() {
            Ok(a.clone())
        } else {
            Err(())
        }
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Subst(Rc<Box<[VarId]>>);

impl Subst {
    pub fn subst(&self, v: VarId) -> VarId {
        self.0[v.0 as usize]
    }

    pub fn and<T>(&self, x: T) -> SubstAnd<T> {
        SubstAnd::new(self.clone(), x)
    }
}

impl<'a> From<&'a [VarId]> for Subst {
    fn from(x: &[VarId]) -> Subst {
        Subst(Rc::new(<Box<[_]>>::from(x)))
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SubstAnd<T> {
    pub subst: Subst,
    pub val: T,
}

impl<T> SubstAnd<T> {
    pub fn new(subst: Subst, val: T) -> SubstAnd<T> {
        SubstAnd { subst, val }
    }

    pub fn with<U>(&self, new_val: U) -> SubstAnd<U> {
        SubstAnd::new(self.subst.clone(), new_val)
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> SubstAnd<U> {
        SubstAnd::new(self.subst, f(self.val))
    }

    pub fn subst(&self, v: VarId) -> VarId {
        self.subst.subst(v)
    }
}


pub struct UnifyState {
    t: InPlaceUnificationTable<VarId>,
}

impl UnifyState {
    pub fn new() -> UnifyState {
        UnifyState {
            t: InPlaceUnificationTable::new(),
        }
    }

    pub fn fresh(&mut self) -> VarId {
        self.t.new_key(None)
    }

    /// Unify the corresponding elements of `a` and `b`.  Returns `true` (and updates internal
    /// state of `self`) if unification succeeds; returns `false` (and leaves `self` unmodified)
    /// otherwise.
    ///
    /// We put off substitution until the last possible moment so the caller can try many
    /// combinations of `Subst`s and `Ty`s without having to allocate a new substituted `Ty` for
    /// each one.
    pub fn unify(&mut self, a: SubstAnd<&[Ty]>, b: SubstAnd<&[Ty]>) -> bool {
        let snap = self.t.snapshot();
        let ok = self.do_unify_list(a, b).is_ok();
        if ok {
            self.t.commit(snap);
        } else {
            self.t.rollback_to(snap);
        }
        ok
    }

    pub fn unify_one(&mut self, a: SubstAnd<&Ty>, b: SubstAnd<&Ty>) -> bool {
        let snap = self.t.snapshot();
        let ok = self.do_unify(a, b).is_ok();
        if ok {
            self.t.commit(snap);
        } else {
            self.t.rollback_to(snap);
        }
        ok
    }

    fn do_unify_list(&mut self, a: SubstAnd<&[Ty]>, b: SubstAnd<&[Ty]>) -> Result<(), ()> {
        if a.val.len() != b.val.len() {
            return Err(());
        }
        for (aa, bb) in a.val.iter().zip(b.val.iter()) {
            self.do_unify(a.with(aa), b.with(bb))?;
        }
        Ok(())
    }

    fn do_unify(&mut self, a: SubstAnd<&Ty>, b: SubstAnd<&Ty>) -> Result<(), ()> {
        match (a.val, b.val) {
            (&Ty::Ctor(ref ac), &Ty::Ctor(ref bc)) => {
                self.do_unify_ctor_ctor(a.with(ac), b.with(bc))
            },
            (&Ty::Ctor(ref ac), &Ty::Var(bv)) => {
                self.do_unify_ctor_var(a.with(ac), b.subst(bv))
            },
            (&Ty::Var(av), &Ty::Ctor(ref bc)) => {
                self.do_unify_ctor_var(b.with(bc), a.subst(av))
            },
            (&Ty::Var(av), &Ty::Var(bv)) => {
                self.do_unify_var_var(a.subst(av), b.subst(bv))
            },
        }
    }

    fn do_unify_ctor_ctor(
        &mut self,
        a: SubstAnd<&Rc<CtorTy>>,
        b: SubstAnd<&Rc<CtorTy>>,
    ) -> Result<(), ()> {
        if a.val.ctor != b.val.ctor || a.val.args.len() != b.val.args.len() {
            return Err(());
        }
        self.do_unify_list(a.with(&a.val.args), b.with(&b.val.args))
    }

    fn do_unify_ctor_var(
        &mut self,
        a: SubstAnd<&Rc<CtorTy>>,
        v: VarId,
    ) -> Result<(), ()> {
        match self.t.probe_value(v) {
            Some(Term(x)) => {
                self.do_unify_ctor_ctor(x.with(&x.val), a.clone())?;
            }
            None => {},
        }
        self.t.unify_var_value(v, Some(Term(a.map(|x| x.clone()))))
    }

    fn do_unify_var_var(
        &mut self,
        v1: VarId,
        v2: VarId,
    ) -> Result<(), ()> {
        if self.t.unioned(v1, v2) {
            return Ok(());
        }

        // If v1 and v2 have both been resolved to concrete `Term`s, unify those `Term`s.  If one
        // or both has no `Term`, then everything will be handled by merging `Option`s.
        let x1 = self.t.probe_value(v1);
        let x2 = self.t.probe_value(v2);
        match (x1, x2) {
            (Some(Term(x1)), Some(Term(x2))) => {
                self.do_unify_ctor_ctor(x1.with(&x1.val), x2.with(&x2.val))?;
            },
            (_, _) => {},
        }

        self.t.unify_var_var(v1, v2)
    }
}


#[cfg(test)]
mod test {
    use super::*;

    macro_rules! ty {
        ($name:ident) => {
            Ty::Ctor(Rc::new(CtorTy {
                ctor: stringify!($name).into(),
                args: Rc::new([]),
            }))
        };
        ($name:ident [ $($args:expr),* ]) => {
            Ty::Ctor(Rc::new(CtorTy {
                ctor: stringify!($name).into(),
                args: Rc::new([$($args),*]),
            }))
        };
        ($var:expr) => { Ty::Var(VarId($var)) };
    }

    macro_rules! unify_one {
        ($u:expr, ($s1:expr, $s2:expr), $a:expr, $b:expr) => {
            $u.unify_one($s1.and(&$a), $s2.and(&$b))
        };
        ($u:expr, $s:expr, $a:expr, $b:expr) => {
            $u.unify_one($s.and(&$a), $s.and(&$b))
        };
    }

    macro_rules! unify {
        ($u:expr, ($s1:expr, $s2:expr), $a:expr, $b:expr) => {
            $u.unify($s1.and(&$a), $s2.and(&$b))
        };
        ($u:expr, $s:expr, $a:expr, $b:expr) => {
            $u.unify($s.and(&$a), $s.and(&$b))
        };
    }

    #[test]
    fn basic() {
        let mut u = UnifyState::new();
        let s = Subst::from(&[] as &[_]);

        assert!(unify_one!(u, s, ty!(A), ty!(A)));
        assert!(!unify_one!(u, s, ty!(A), ty!(B)));
        assert!(!unify_one!(u, s, ty!(A), ty!(A[ty!(B)])));
    }

    #[test]
    fn var_basic() {
        let mut u = UnifyState::new();
        let s = Subst::from(&[u.fresh()] as &[_]);

        assert!(unify_one!(u, s, ty!(A), ty!(0)));
        assert!(unify_one!(u, s, ty!(A), ty!(0)));
        assert!(!unify_one!(u, s, ty!(B), ty!(0)));
    }

    /// Check that substitutions are applied properly.
    #[test]
    fn var_subst() {
        let mut u = UnifyState::new();
        let s0 = Subst::from(&[] as &[_]);
        let s1 = Subst::from(&[u.fresh()] as &[_]);
        let s2 = Subst::from(&[u.fresh()] as &[_]);

        assert!(unify_one!(u, (s0, s1), ty!(A), ty!(0)));
        assert!(unify_one!(u, (s1, s0), ty!(0), ty!(A)));
        assert!(unify_one!(u, (s0, s2), ty!(B), ty!(0)));
        assert!(unify_one!(u, (s2, s0), ty!(0), ty!(B)));
    }

    #[test]
    fn var_under_ctor() {
        let mut u = UnifyState::new();
        let s0 = Subst::from(&[] as &[_]);
        let s1 = Subst::from(&[u.fresh()] as &[_]);

        assert!(unify_one!(u, (s0, s1), ty!(Vec[ty!(u8)]), ty!(Vec[ty!(0)])));
        assert!(!unify_one!(u, (s1, s0), ty!(0), ty!(u16)));
        assert!(unify_one!(u, (s1, s0), ty!(0), ty!(u8)));
    }

    #[test]
    fn grammar_vec_push() {
        // Consider this grammar:
        //
        // for[T] push ::= <<expr[Vec[T]]>>.push(<<expr[T]>>)
        // for[T] expr[T] ::= <<choose-var[T]>>
        //
        // This grammar does three expansions: `push`, `expr[Vec[T]]`, and `expr[T]`.  In this
        // test, we do the substs and unification steps just as they would happen during actual
        // expansion.

        let mut u = UnifyState::new();

        let s0 = Subst::from(&[] as &[_]);
        let s_push = Subst::from(&[u.fresh()] as &[_]);

        // Expansion of `expr[Vec[T]]`
        let s_expr_vec = Subst::from(&[u.fresh()] as &[_]);
        assert!(unify_one!(u, (s_push, s_expr_vec), ty!(Vec[ty!(0)]), ty!(0)));
        assert!(unify_one!(u, (s_expr_vec, s0), ty!(0), ty!(Vec[ty!(u8)])));

        // Expansion of `expr[T]`
        let s_expr = Subst::from(&[u.fresh()] as &[_]);
        assert!(unify_one!(u, (s_push, s_expr), ty!(0), ty!(0)));
        assert!(unify_one!(u, (s_expr, s0), ty!(0), ty!(u8)));

        // The `T` in `push` should be `u8`, not anything else.
        assert!(!unify_one!(u, (s_push, s0), ty!(0), ty!(u16)));
        assert!(unify_one!(u, (s_push, s0), ty!(0), ty!(u8)));
    }
}
