{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Extension
-- Description      : LLVM interface for Crucible
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
--
-- Syntax extension definitions for LLVM
------------------------------------------------------------------------
module Lang.Crucible.LLVM.Extension
( LLVM
) where

import           GHC.TypeLits
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.MemModel.Pointer
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import           Lang.Crucible.LLVM.Types

data LLVM (wptr :: Nat)

type instance ExprExtension (LLVM wptr) = EmptyExprExtension
type instance StmtExtension (LLVM wptr) = LLVMStmt wptr

data LLVMStmt (wptr :: Nat) (f :: CrucibleType -> *) :: CrucibleType -> * where
  LLVM_PushFrame :: !(f Mem) -> LLVMStmt wptr f Mem
  LLVM_PopFrame  :: !(f Mem) -> LLVMStmt wptr f Mem
  LLVM_Load ::
     !(f Mem) -> 
     !(f (LLVMPointerType wptr)) ->
     !G.Type ->
     !Alignment ->
     LLVMStmt wptr f AnyType
  LLVM_Store ::
     !(f Mem) -> 
     !(f (LLVMPointerType wptr)) ->
     !G.Type ->
     !Alignment ->
     !(f AnyType) ->
     LLVMStmt wptr f Mem
  LLVM_LoadHandle ::
     !(f Mem) ->
     !(f (LLVMPointerType wptr)) ->
     LLVMStmt wptr f AnyType
  LLVM_ResolveGlobal ::
     !(NatRepr wptr) ->
     !(f Mem) ->
     GlobalSymbol ->
     LLVMStmt wptr f (LLVMPointerType wptr)
  LLVM_PtrEq ::
     !(f Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !(f (LLVMPointerType wptr)) ->
     LLVMStmt wptr f BoolType     
  LLVM_PtrLe ::
     !(f Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !(f (LLVMPointerType wptr)) ->
     LLVMStmt wptr f BoolType     
  LLVM_PtrAddOffset ::
     !(NatRepr wptr) ->
     !(f Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !(f (BVType wptr)) ->
     LLVMStmt wptr f (LLVMPointerType wptr)
  LLVM_PtrSubtract ::
     !(NatRepr wptr) ->
     !(f Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !(f (LLVMPointerType wptr)) ->
     LLVMStmt wptr f (BVType wptr)

$(return [])

instance (1 <= wptr) => TypeApp (LLVMStmt wptr) where
  appType = \case
    LLVM_PushFrame{} -> knownRepr
    LLVM_PopFrame{} -> knownRepr
    LLVM_Load{} -> knownRepr
    LLVM_Store{} -> knownRepr
    LLVM_LoadHandle{} -> knownRepr
    LLVM_ResolveGlobal w _ _ -> LLVMPointerRepr w
    LLVM_PtrEq{} -> knownRepr
    LLVM_PtrLe{} -> knownRepr
    LLVM_PtrAddOffset w _ _ _ -> LLVMPointerRepr w
    LLVM_PtrSubtract w _ _ _ -> BVRepr w

instance PrettyApp (LLVMStmt wptr) where
  ppApp pp = \case
    LLVM_PushFrame m ->
       text "pushFrame" <+> pp m
    LLVM_PopFrame m  ->
       text "popFrame" <+> pp m
    LLVM_Load m ptr tp a ->
       text "load" <+> pp m <+> pp ptr <+> text (show tp) <+> text (show a)
    LLVM_Store m ptr tp a v ->
       text "store" <+> pp m <+> pp ptr <+> text (show tp) <+> text (show a) <+> pp v
    LLVM_LoadHandle m ptr ->
       text "loadFunctionHandle" <+> pp m <+> pp ptr
    LLVM_ResolveGlobal _ m s ->
       text "resolveGlobal" <+> pp m <+> text (show s)
    LLVM_PtrEq m x y ->
       text "ptrEq" <+> pp m <+> pp x <+> pp y
    LLVM_PtrLe m x y ->
       text "ptrEq" <+> pp m <+> pp x <+> pp y
    LLVM_PtrAddOffset _ m x y ->
       text "ptrAddOffset" <+> pp m <+> pp x <+> pp y
    LLVM_PtrSubtract _ m x y ->
       text "ptrSubtract" <+> pp m <+> pp x <+> pp y

instance TestEqualityFC (LLVMStmt wptr) where
  testEqualityFC testSubterm =
    $(U.structuralTypeEquality [t|LLVMStmt|]
       [(U.DataArg 1 `U.TypeApp` U.AnyType, [|testSubterm|])
       ,(U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       ])

instance OrdFC (LLVMStmt wptr) where
  compareFC compareSubterm =
    $(U.structuralTypeOrd [t|LLVMStmt|]
       [(U.DataArg 1 `U.TypeApp` U.AnyType, [|compareSubterm|])
       ,(U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       ])

instance FunctorFC (LLVMStmt wptr) where
  fmapFC = fmapFCDefault

instance FoldableFC (LLVMStmt wptr) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (LLVMStmt wptr) where
  traverseFC =
    $(U.structuralTraversal [t|LLVMStmt|] [])


instance (1 <= wptr) => IsSyntaxExtension (LLVM wptr)
