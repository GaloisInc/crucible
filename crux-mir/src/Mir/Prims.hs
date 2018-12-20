{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}

{-# OPTIONS_GHC -Wall -fwarn-incomplete-patterns #-}

-----------------------------------------------------------------------
-- |
-- Module           : Mir.Prims
-- Description      : Define the standard library
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Stability        : provisional
--
-- This module creates a collection of standard library traits, functions
-- and ADT definitions. Most of this library is defined by the "mir-lib"
-- package.
-----------------------------------------------------------------------

module Mir.Prims where

import Mir.DefId
import Mir.Mir
import Mir.Generate
import Mir.PP()
import Data.Foldable(fold)

import Text.PrettyPrint.ANSI.Leijen (pretty)
import qualified Debug.Trace as Debug
import Control.Monad(when)


-- | Location of the rust file with the standard library
libLoc :: String
libLoc = "mir-lib/src/"

-- | load the rs file containing the standard library
loadPrims :: Int -> IO Collection
loadPrims debugLevel = do
  -- Only print debugging info in the standard library at high debugging levels
  cols <- mapM (generateMIR (debugLevel-3) libLoc) 
    [ "default"
    , "option"    -- some FnOnce bounds commented out
    , "result"    -- some FnOnce bounds commented out
    , "ops/range"
    , "default"
    , "cmp"
--    , "slice"
    ]   
    
  let total = (fold (hardCoded : cols))
  when (debugLevel > 6) $ do
    Debug.traceM "--------------------------------------------------------------"
    Debug.traceM $ "Complete Collection: "
    Debug.traceM $ show (pretty total)
    Debug.traceM "--------------------------------------------------------------"  

  return total

hardCoded :: Collection
hardCoded = Collection [] [] [fnOnce, fn, index, indexMut]


-- FnOnce trait

fnOnce :: Trait
fnOnce = Trait fnOnce_defId [call_once, output] where

           fnOnce_defId :: DefId
           fnOnce_defId = textId $ ("::ops[0]::function[0]::FnOnce[0]")

           fnOnce_Output_defId :: DefId
           fnOnce_Output_defId = textId ("::ops[0]::function[0]::FnOnce[0]::Output[0]")

           fnOnce_call_once_defId :: DefId
           fnOnce_call_once_defId = textId ("::ops[0]::function[0]::FnOnce[0]::call_once[0]")

           call_once :: TraitItem
           call_once = TraitMethod fnOnce_call_once_defId
               (FnSig [TyParam 0, TyParam 1] (TyProjection fnOnce_Output_defId []))
    
           output :: TraitItem
           output = TraitType fnOnce_Output_defId        

fn :: Trait
fn = Trait fn_defId [call_once, output] where

           fn_defId :: DefId
           fn_defId = textId $ ( "::ops[0]::function[0]::Fn[0]")

           fn_Output_defId :: DefId
           fn_Output_defId = textId  ("::ops[0]::function[0]::Fn[0]::Output[0]")

           fn_call_defId :: DefId
           fn_call_defId = textId  ("::ops[0]::function[0]::Fn[0]::call[0]")

           call_once :: TraitItem
           call_once = TraitMethod fn_call_defId
               (FnSig [TyRef (TyParam 0) Immut, TyParam 1] (TyProjection fn_Output_defId []))
    
           output :: TraitItem
           output = TraitType fn_Output_defId        

index :: Trait
index = Trait index_defId [index_index, output] where

           index_defId :: DefId
           index_defId = textId $ (stdlib <> "::ops[0]::index[0]::Index[0]")

           index_Output_defId :: DefId
           index_Output_defId = textId (stdlib <> "::ops[0]::index[0]::Index[0]::Output[0]")

           index_index_defId :: DefId
           index_index_defId = textId (stdlib <> "::ops[0]::index[0]::Index[0]::index[0]")

           index_index :: TraitItem
           index_index = TraitMethod index_index_defId
               (FnSig [TyDynamic index_defId, TyParam 0] (TyProjection index_Output_defId []))
    
           output :: TraitItem
           output = TraitType index_Output_defId        

indexMut :: Trait
indexMut = Trait index_defId [index_index, index_index_mut, output] where

           index_defId :: DefId
           index_defId = textId $ (stdlib <> "::ops[0]::index[0]::IndexMut[0]")

           index_Output_defId :: DefId
           index_Output_defId = textId (stdlib <> "::ops[0]::index[0]::Index[0]::Output[0]")

           index_index_defId :: DefId
           index_index_defId = textId (stdlib <> "::ops[0]::index[0]::Index[0]::index[0]")

           index_index_mut_defId :: DefId
           index_index_mut_defId = textId (stdlib <> "::ops[0]::index[0]::Index[0]::index_mut[0]")

           index_index :: TraitItem
           index_index = TraitMethod index_index_defId
               (FnSig [TyDynamic index_defId, TyParam 0] (TyProjection index_Output_defId []))

           index_index_mut :: TraitItem
           index_index_mut = TraitMethod index_index_mut_defId
               (FnSig [TyDynamic index_defId, TyParam 0] (TyProjection index_Output_defId []))
    
           output :: TraitItem
           output = TraitType index_Output_defId        



{-

-- Alternative approach: Hard code the standard library using MIR data types.
-- This is pretty labor intensive. Much better to get it via mir-json/relocation.
-- However, leaving this example here so that we can see what the Mir ADT looks like.

-- Option ADT

none = Variant "core/ae3efe0::Option[0]::None[0]" (Relative 0)
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


