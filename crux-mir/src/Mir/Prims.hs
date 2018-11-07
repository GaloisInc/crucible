{-# LANGUAGE OverloadedStrings #-}


{-# OPTIONS_GHC -Wall -fwarn-incomplete-patterns #-}

{- This module creates a Rust standard library by reading it . -}

module Mir.Prims where

import Mir.Mir
import Mir.Generate

--import Data.Text (Text)
import qualified Data.Text as T



-- | The module name for the rust core library used by mir-json.
-- If mir-json changes, we will need to update this name.
stdlib :: String
stdlib = "core/ae3efe0"

-- | Location of the rust file with the standard library
libLoc :: String
libLoc = "mir_verif/src/"

-- | The actual file containing these definitions
libFile :: String
libFile = "lib"


-- | load the rs file containing the standard library
loadPrims :: IO Collection
loadPrims = do
  col <- generateMIR libLoc libFile
  return (relocate col)


-------------------------------
-- * Relocation

-- | Crawl over the AST and rename the module that defIds live in.
-- We need this because we are loading our own variant of the standard
-- library, but all of the definitions there will have the wrong
-- name.


-- | 
relocateDefId :: DefId -> DefId
relocateDefId defId = if ':' `elem` name then T.pack (stdlib ++ rest) else defId where
  name = T.unpack defId 
  (_mod,rest) = span (/= ':') name


class Relocate a where
  relocate :: a -> a

instance Relocate a => Relocate [a] where
  relocate = fmap relocate
instance Relocate a => Relocate (Maybe a) where
  relocate = fmap relocate
instance (Relocate a, Relocate b) => Relocate (a,b) where
  relocate (x,y) = (relocate x, relocate y)

instance Relocate Collection where
  relocate (Collection as bs cs) = Collection (relocate as) (relocate bs) (relocate cs)

instance Relocate Fn where
  relocate (Fn name args ty body) = Fn (relocateDefId name) (relocate args) (relocate ty) (relocate body)

instance Relocate Var where
  relocate (Var name mut ty scope pos) = Var name mut (relocate ty) scope pos

instance Relocate Ty where
  relocate (TyTuple tys)         = TyTuple (relocate tys)
  relocate (TySlice ty)          = TySlice (relocate ty)
  relocate (TyArray ty i)        = TyArray (relocate ty) i
  relocate (TyRef ty mut)        = TyRef (relocate ty) mut
  relocate (TyAdt name tys)      = TyAdt (relocateDefId name) (relocate tys)
  relocate (TyCustom cust)       = TyCustom (relocate cust)
  relocate (TyFnDef defId tys)   = TyFnDef (relocateDefId defId) (relocate tys)
  relocate (TyClosure defId tys) = TyClosure (relocateDefId defId) (relocate tys)
  relocate (TyFnPtr fnSig)       = TyFnPtr (relocate fnSig)
  relocate (TyDynamic defId)     = TyDynamic (relocateDefId defId)
  relocate (TyRawPtr ty mut)     = TyRawPtr (relocate ty) mut
  relocate (TyDowncast ty i)     = TyDowncast (relocate ty) i
  relocate x = x

instance Relocate CustomTy where
  relocate (BoxTy ty)  = BoxTy (relocate ty)
  relocate (VecTy ty)  = VecTy (relocate ty)
  relocate (IterTy ty) = IterTy (relocate ty)

instance Relocate FnSig where
  relocate (FnSig tys ty) = FnSig (relocate tys) (relocate ty)

instance Relocate Adt where
  relocate (Adt name vars) = Adt (relocateDefId name) (relocate vars)

instance Relocate Variant where
  relocate (Variant name discr fields kind) = Variant (relocateDefId name) (relocate discr) (relocate fields) kind

instance Relocate VariantDiscr where
  relocate (Explicit defId) = Explicit (relocateDefId defId)
  relocate (Relative i)     = Relative i

instance Relocate Field where
  relocate (Field name ty substs) = Field (relocateDefId name) (relocate ty) (relocate substs)

instance Relocate MirBody where
  relocate (MirBody vars bbs) = MirBody (relocate vars) (relocate bbs)

instance Relocate BasicBlock where
  relocate (BasicBlock info dat) = BasicBlock info (relocate dat)

instance Relocate BasicBlockData where
  relocate (BasicBlockData stmts term) = BasicBlockData (relocate stmts) (relocate term)

instance Relocate Statement where
  relocate (Assign lhs rhs pos) = Assign (relocate lhs) (relocate rhs) pos
  relocate (SetDiscriminant dlv dvi) = SetDiscriminant (relocate dlv) (dvi)
  relocate (StorageLive lv) = StorageLive (relocate lv)
  relocate (StorageDead lv) = StorageDead (relocate lv)
  relocate Nop = Nop

instance Relocate Lvalue where
  relocate (LProjection lvp) = LProjection (relocate lvp)
  relocate (Local v) = Local (relocate v)
  relocate x = x

instance Relocate LvalueProjection where
  relocate (LvalueProjection base kind) = LvalueProjection (relocate base) (relocate kind)

instance Relocate Lvpelem where
  relocate (PField i ty) = PField i (relocate ty)
  relocate (Index op)    = Index (relocate op)
  relocate x = x

instance Relocate Terminator where
  relocate (SwitchInt discr ty values bbs)  = SwitchInt (relocate discr) (relocate ty) values bbs
  relocate (DropAndReplace loc val tar unw) = DropAndReplace (relocate loc) (relocate val) tar unw
  relocate (Call func args dest cl)         = Call (relocate func) (relocate args) dest cl
  relocate (Assert op ex msg tar cl)        = Assert (relocate op) ex msg tar cl
  relocate x = x

instance Relocate Operand where
  relocate (Consume lv)   = Consume (relocate lv)
  relocate (OpConstant c) = OpConstant (relocate c)

instance Relocate Constant where
  relocate (Constant ty lit) = Constant (relocate ty) (relocate lit)

instance Relocate Literal where
  relocate (Item defId tys) = Item (relocateDefId defId) (relocate tys)
  relocate (Value constVal) = Value (relocate constVal)
  relocate (LPromoted prom) = LPromoted prom


instance Relocate ConstVal where
  relocate (ConstVariant defId) = ConstVariant (relocateDefId defId)
  relocate (ConstFunction defId tys) = ConstFunction (relocateDefId defId) (relocate tys)
  relocate (ConstTuple vals) = ConstTuple (relocate vals)
  relocate (ConstArray vals) = ConstArray (relocate vals)
  relocate (ConstRepeat val i) = ConstRepeat (relocate val) i
  relocate x = x

instance Relocate Rvalue where
  relocate (Use op) = Use (relocate op)
  relocate (Repeat op len) = Repeat (relocate op) len
  relocate (Ref bk var reg) = Ref bk (relocate var) reg
  relocate (Len lv) = Len (relocate lv)
  relocate (Cast ck op ty) = Cast ck (relocate op) (relocate ty)
  relocate (BinaryOp bop op1 op2) = BinaryOp bop (relocate op1) (relocate op2)
  relocate (CheckedBinaryOp bop op1 op2) = CheckedBinaryOp bop (relocate op1) (relocate op2)
  relocate (NullaryOp np ty) = NullaryOp np (relocate ty)
  relocate (UnaryOp up op)   = UnaryOp up (relocate op)
  relocate (Discriminant dv) = Discriminant (relocate dv)
  relocate (Aggregate ak ops) = Aggregate ak (relocate ops)
  relocate (RAdtAg adtag) = RAdtAg (relocate adtag)
  relocate (RCustom _) = error "Urk"

instance Relocate AdtAg where
  relocate (AdtAg adt i ops) = AdtAg (relocate adt) i (relocate ops)

instance Relocate Trait where
  relocate (Trait name items) = Trait (relocateDefId name) (relocate items)

instance Relocate TraitItem where
  relocate (TraitMethod name sig) = TraitMethod (relocateDefId name) (relocate sig)
  relocate _ = error "TODO"
  
  
  
  
    


{-

-- Alternative approach: Hard code the standard library using MIR data types.
-- This is pretty labor intensive. Much better to get it via mir-json/relocation.
-- However, leaving this example here so that we can see what the Mir ADT looks like.

-- Option ADT

none = Variant "core/ae3efe0::option[0]::None[0]" (Relative 0)
       [] ConstKind
some = Variant "core/ae3efe0::option[0]::Some[0]" (Relative 1)
       [ Field "core/ae3efe0::Option[0]::Some[0]::0[0]"
               (TyParam 0) [] ] FnKind
option = Adt "core/ae3efe0::option[0]::Option[0]" [none, some]


is_none = let 
  var0 = Var {_varname = "_0", _varmut = Mut, _varty = TyBool, _varscope = "scope0", _varpos = "test/conc_eval/stdlib/option.rs:20:5: 22:6"}
  var1 = Var {_varname = "_1", _varmut = Immut, _varty = TyRef (TyAdt "core/ae3efe0::Option[0]" [Just (TyParam 0)]) Immut, _varscope = "scope0", _varpos = "test/conc_eval/stdlib/option.rs:20:20: 20:25"}
  var2 = Var {_varname = "_2", _varmut = Immut, _varty = TyRef (TyAdt "core/ae3efe0::Option[0]" [Just (TyParam 0)]) Immut, _varscope = "scope1", _varpos = "test/conc_eval/stdlib/option.rs:20:20: 20:25"}
  var3 = Var {_varname = "_3", _varmut = Mut, _varty = TyBool, _varscope = "scope0", _varpos = "test/conc_eval/stdlib/option.rs:21:10: 21:24"}
  var4 = Var {_varname = "_4", _varmut = Mut, _varty = TyRef (TyAdt "core/ae3efe0::Option[0]" [Just (TyParam 0)]) Immut, _varscope = "scope0", _varpos = "test/conc_eval/stdlib/option.rs:21:10: 21:14"}
  in Fn {_fname = "::option[0]::{{impl}}[0]::is_none[0]",
              _fargs = [var1],
              _freturn_ty = TyBool,
              _fbody = MirBody {
                 _mvars = [var0,
                           var2,
                           var3,
                           var4],
                                
                 _mblocks = [BasicBlock {_bbinfo = "bb0",
                                         _bbdata = BasicBlockData {
                                         _bbstmts = [StorageLive {_sllv = Local {_lvar = var2}},
                                                     Assign {_alhs = Local {_lvar = var2},
                                                             _arhs = Use {_uop = Consume (Local {_lvar = var1})},
                                                             _apos = "test/conc_eval/stdlib/option.rs:21:10: 21:14"},
                                                     StorageLive {_sllv = Local {_lvar = var3}},
                                                     StorageLive {_sllv = Local {_lvar = var4}},
                                                     Assign {_alhs = Local {_lvar = var4},
                                                             _arhs = Use {_uop = Consume (Local {_lvar = var2})},
                                                             _apos = "test/conc_eval/stdlib/option.rs:21:10: 21:14"}],
                                         _bbterminator = Call {_cfunc = OpConstant (Constant {_conty = TyFnDef "::option[0]::{{impl}}[0]::is_some[0]" [Just (TyParam 0)],
                                                                                              _conliteral = Value (ConstFunction "::option[0]::{{impl}}[0]::is_some[0]" [Just (TyParam 0)])}),
                                                                _cargs = [Consume (Local {_lvar = var4})],
                                                                _cdest = Just (Local {_lvar = var3},"bb1"), _cleanup = Nothing}}},
                              BasicBlock {_bbinfo = "bb1",
                                          _bbdata = BasicBlockData {
                                             _bbstmts = [StorageDead {_sdlv = Local {_lvar = var4}},
                                                         Nop,
                                                         Assign {_alhs = Local {_lvar = var0},
                                                                 _arhs = UnaryOp {_unop = Not, _unoperand = Consume (Local {_lvar = var3})},
                                                                 _apos = "test/conc_eval/stdlib/option.rs:21:9: 21:24"},
                                                          StorageDead {_sdlv = Local {_lvar = var3}},
                                                          StorageDead {_sdlv = Local {_lvar = var2}}], _bbterminator = Return}}] } }



is_some =  let var1 = Var {_varname = "_1", _varmut = Immut, _varty = TyRef (TyAdt "core/ae3efe0::Option[0]" [Just (TyParam 0)]) Immut,
                           _varscope = "scope0", _varpos = "test/conc_eval/stdlib/option.rs:13:20: 13:25"}
               var2 = Var {_varname = "_2", _varmut = Immut, _varty = TyRef (TyAdt "core/ae3efe0::Option[0]" [Just (TyParam 0)]) Immut,
                           _varscope = "scope1", _varpos = "test/conc_eval/stdlib/option.rs:13:20: 13:25"}
               var0 = Var {_varname = "_0", _varmut = Mut, _varty = TyBool, _varscope = "scope0", _varpos = "test/conc_eval/stdlib/option.rs:13:5: 18:6"}
               var3 = Var {_varname = "_3", _varmut = Mut, _varty = TyInt USize, _varscope = "scope0", _varpos = "test/conc_eval/stdlib/option.rs:15:13: 15:21"}
  in Fn {_fname = "::option[0]::{{impl}}[0]::is_some[0]", _fargs = [var1], _freturn_ty = TyBool,
         _fbody = MirBody {_mvars = [var0,var2,var3],
                           _mblocks = [BasicBlock {_bbinfo = "bb0",
                                                   _bbdata = BasicBlockData {
                                                      _bbstmts = [StorageLive {_sllv = Local {_lvar = var2}},
                                                                  Assign {_alhs = Local {_lvar = var2},
                                                                          _arhs = Use {_uop = Consume (Local {_lvar = var1})},
                                                                          _apos = "test/conc_eval/stdlib/option.rs:13:20: 13:25"},
                                                                   Assign {_alhs = Local {_lvar = var3}, 
                                                                            _arhs = Discriminant {_dvar = LProjection (LvalueProjection {_lvpbase = Local {_lvar = var2}, _lvpkind = Deref})},
                                                                            _apos = "test/conc_eval/stdlib/option.rs:15:13: 15:21"}],
                                                        _bbterminator = SwitchInt {_sdiscr = Consume (Local {_lvar = var3}), _switch_ty = TyInt USize, _svalues = [Just 0], _stargets = ["bb2","bb1"]}}},
                                        BasicBlock {_bbinfo = "bb1", _bbdata = BasicBlockData {
                                                    _bbstmts = [Assign {_alhs = Local {_lvar = var0},
                                                                           _arhs = Use {_uop = OpConstant (Constant {_conty = TyBool, _conliteral = Value (ConstBool True)})},
                                                                           _apos = "test/conc_eval/stdlib/option.rs:15:25: 15:29"}],
                                                    _bbterminator = Goto {_gbb = "bb3"}}},
                                        BasicBlock {_bbinfo = "bb2", _bbdata = BasicBlockData {
                                                    _bbstmts = [Assign {_alhs = Local {_lvar = var0},
                                                                           _arhs = Use {_uop = OpConstant (Constant {_conty = TyBool, _conliteral = Value (ConstBool False)})},
                                                                           _apos = "test/conc_eval/stdlib/option.rs:16:22: 16:27"}],
                                                    _bbterminator = Goto {_gbb = "bb3"}}},
                                        BasicBlock {_bbinfo = "bb3", _bbdata = BasicBlockData {_bbstmts = [StorageDead {_sdlv = Local {_lvar = var2}}], _bbterminator = Return}}]}}

prim_fns = [is_none, is_some]

prim_adts = [option]

prim_traits = []

primitives :: Collection
primitives = Collection prim_fns prim_adts prim_traits


-}


