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
, ArchWidth
, type LLVMArch
, type X86
, LLVMStmt(..)
) where

import           GHC.TypeLits
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.CFG.Common
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.MemModel.Pointer
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import           Lang.Crucible.LLVM.Types

data LLVMArch = X86 Nat
type X86 = 'X86

type family ArchWidth (arch :: LLVMArch) :: Nat where
  ArchWidth (X86 wptr) = wptr

data LLVM (arch :: LLVMArch)

type instance ExprExtension (LLVM arch) = EmptyExprExtension
type instance StmtExtension (LLVM arch) = LLVMStmt (ArchWidth arch)

data LLVMStmt (wptr :: Nat) (f :: CrucibleType -> *) :: CrucibleType -> * where
  LLVM_PushFrame :: !(GlobalVar Mem) -> LLVMStmt wptr f UnitType
  LLVM_PopFrame  :: !(GlobalVar Mem) -> LLVMStmt wptr f UnitType
  LLVM_Alloca ::
     !(NatRepr wptr) ->
     !(GlobalVar Mem) ->
     !(f (BVType wptr)) ->
     !String ->
     LLVMStmt wptr f (LLVMPointerType wptr)
  LLVM_Load ::
     !(GlobalVar Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !G.Type ->
     !Alignment ->
     LLVMStmt wptr f AnyType
  LLVM_Store ::
     !(GlobalVar Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !G.Type ->
     !Alignment ->
     !(f AnyType) ->
     LLVMStmt wptr f UnitType
  LLVM_LoadHandle ::
     !(GlobalVar Mem) ->
     !(f (LLVMPointerType wptr)) ->
     LLVMStmt wptr f AnyType
  LLVM_ResolveGlobal ::
     !(NatRepr wptr) ->
     !(GlobalVar Mem) ->
     GlobalSymbol ->
     LLVMStmt wptr f (LLVMPointerType wptr)
  LLVM_PtrEq ::
     !(GlobalVar Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !(f (LLVMPointerType wptr)) ->
     LLVMStmt wptr f BoolType
  LLVM_PtrLe ::
     !(GlobalVar Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !(f (LLVMPointerType wptr)) ->
     LLVMStmt wptr f BoolType
  LLVM_PtrAddOffset ::
     !(NatRepr wptr) ->
     !(GlobalVar Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !(f (BVType wptr)) ->
     LLVMStmt wptr f (LLVMPointerType wptr)
  LLVM_PtrSubtract ::
     !(NatRepr wptr) ->
     !(GlobalVar Mem) ->
     !(f (LLVMPointerType wptr)) ->
     !(f (LLVMPointerType wptr)) ->
     LLVMStmt wptr f (BVType wptr)

$(return [])

instance (1 <= wptr) => TypeApp (LLVMStmt wptr) where
  appType = \case
    LLVM_PushFrame{} -> knownRepr
    LLVM_PopFrame{} -> knownRepr
    LLVM_Alloca w _ _ _ -> LLVMPointerRepr w
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
    LLVM_PushFrame mvar ->
       text "pushFrame" <+> text (show mvar)
    LLVM_PopFrame mvar  ->
       text "popFrame" <+> text (show mvar)
    LLVM_Alloca _ mvar sz loc ->
       text "alloca" <+> text (show mvar) <+> pp sz <+> text loc
    LLVM_Load mvar ptr tp a ->
       text "load" <+> text (show mvar) <+> pp ptr <+> text (show tp) <+> text (show a)
    LLVM_Store mvar ptr tp a v ->
       text "store" <+> text (show mvar) <+> pp ptr <+> text (show tp) <+> text (show a) <+> pp v
    LLVM_LoadHandle mvar ptr ->
       text "loadFunctionHandle" <+> text (show mvar) <+> pp ptr
    LLVM_ResolveGlobal _ mvar s ->
       text "resolveGlobal" <+> text (show mvar) <+> text (show s)
    LLVM_PtrEq mvar x y ->
       text "ptrEq" <+> text (show mvar) <+> pp x <+> pp y
    LLVM_PtrLe mvar x y ->
       text "ptrEq" <+> text (show mvar) <+> pp x <+> pp y
    LLVM_PtrAddOffset _ mvar x y ->
       text "ptrAddOffset" <+> text (show mvar) <+> pp x <+> pp y
    LLVM_PtrSubtract _ mvar x y ->
       text "ptrSubtract" <+> text (show mvar) <+> pp x <+> pp y

instance TestEqualityFC (LLVMStmt wptr) where
  testEqualityFC testSubterm =
    $(U.structuralTypeEquality [t|LLVMStmt|]
       [(U.DataArg 1 `U.TypeApp` U.AnyType, [|testSubterm|])
       ,(U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       ,(U.ConType [t|GlobalVar|] `U.TypeApp` U.AnyType, [|testEquality|])
       ])

instance OrdFC (LLVMStmt wptr) where
  compareFC compareSubterm =
    $(U.structuralTypeOrd [t|LLVMStmt|]
       [(U.DataArg 1 `U.TypeApp` U.AnyType, [|compareSubterm|])
       ,(U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       ,(U.ConType [t|GlobalVar|] `U.TypeApp` U.AnyType, [|compareF|])
       ])

instance FunctorFC (LLVMStmt wptr) where
  fmapFC = fmapFCDefault

instance FoldableFC (LLVMStmt wptr) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (LLVMStmt wptr) where
  traverseFC =
    $(U.structuralTraversal [t|LLVMStmt|] [])


instance (1 <= ArchWidth arch) => IsSyntaxExtension (LLVM arch)
