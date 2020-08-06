-- |
-- Module           : Lang.Crucible.LLVM.Errors.Poison
-- Description      : All about LLVM poison values
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Langston Barrett <lbarrett@galois.com>
-- Stability        : provisional
--
-- This module is intended to be imported qualified.
--
-- Undefined values follow control flow, wereas the poison values follow data
-- flow. See the module-level comment in "Lang.Crucible.LLVM.Translation".
--
-- This email provides an explanation and motivation for poison and @undef@
-- values: https://lists.llvm.org/pipermail/llvm-dev/2016-October/106182.html
--------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.Errors.Poison
  ( Poison(..)
  , cite
  , explain
  , standard
  , details
  , pp
  , ppReg
  , concPoison
  ) where

import           Data.Kind (Type)
import           Data.Text (unpack)
import           Data.Maybe (isJust)
import           Data.Typeable (Typeable)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.Parameterized.TraversableF as TF
import           Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..), TraversableF(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.ClassesC (TestEqualityC(..), OrdC(..))
import           Data.Parameterized.Classes (OrderingF(..), toOrdering)

import           Lang.Crucible.LLVM.Errors.Standards
import           Lang.Crucible.LLVM.MemModel.Pointer (concBV)
import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import           Lang.Crucible.Types
import qualified What4.Interface as W4I
import           What4.Expr (GroundValue)

data Poison (e :: CrucibleType -> Type) where
  -- | Arguments: @op1@, @op2@
  AddNoUnsignedWrap   :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  AddNoSignedWrap     :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  SubNoUnsignedWrap   :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  SubNoSignedWrap     :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  MulNoUnsignedWrap   :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  MulNoSignedWrap     :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  UDivExact           :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  SDivExact           :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  ShlOp2Big           :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  ShlNoUnsignedWrap   :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  ShlNoSignedWrap     :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  LshrExact           :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  LshrOp2Big          :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  AshrExact           :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  AshrOp2Big          :: (1 <= w) => e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | TODO(langston): store the 'Vector'
  ExtractElementIndex :: (1 <= w) => e (BVType w)
                      -> Poison e
  -- | TODO(langston): store the 'Vector'
  InsertElementIndex  :: (1 <= w) => e (BVType w)
                      -> Poison e
  -- | TODO(langston): store the 'LLVMPointerType'
  GEPOutOfBounds      :: (1 <= w) => e (BVType w)
                      -> Poison e
  deriving (Typeable)

standard :: Poison e -> Standard
standard =
  \case
    AddNoUnsignedWrap _ _   -> LLVMRef LLVM8
    AddNoSignedWrap _ _     -> LLVMRef LLVM8
    SubNoUnsignedWrap _ _   -> LLVMRef LLVM8
    SubNoSignedWrap _ _     -> LLVMRef LLVM8
    MulNoUnsignedWrap _ _   -> LLVMRef LLVM8
    MulNoSignedWrap _ _     -> LLVMRef LLVM8
    UDivExact _ _           -> LLVMRef LLVM8
    SDivExact _ _           -> LLVMRef LLVM8
    ShlOp2Big _ _           -> LLVMRef LLVM8
    ShlNoUnsignedWrap _ _   -> LLVMRef LLVM8
    ShlNoSignedWrap _ _     -> LLVMRef LLVM8
    LshrExact _ _           -> LLVMRef LLVM8
    LshrOp2Big _ _          -> LLVMRef LLVM8
    AshrExact _ _           -> LLVMRef LLVM8
    AshrOp2Big _ _          -> LLVMRef LLVM8
    ExtractElementIndex _   -> LLVMRef LLVM8
    InsertElementIndex _    -> LLVMRef LLVM8
    GEPOutOfBounds _        -> LLVMRef LLVM8

-- | Which section(s) of the document state that this is poison?
cite :: Poison e -> Doc
cite = text .
  \case
    AddNoUnsignedWrap _ _   -> "‘add’ Instruction (Semantics)"
    AddNoSignedWrap _ _     -> "‘add’ Instruction (Semantics)"
    SubNoUnsignedWrap _ _   -> "‘sub’ Instruction (Semantics)"
    SubNoSignedWrap _ _     -> "‘sub’ Instruction (Semantics)"
    MulNoUnsignedWrap _ _   -> "‘mul’ Instruction (Semantics)"
    MulNoSignedWrap _ _     -> "‘mul’ Instruction (Semantics)"
    UDivExact _ _           -> "‘udiv’ Instruction (Semantics)"
    SDivExact _ _           -> "‘sdiv’ Instruction (Semantics)"
    ShlOp2Big _ _           -> "‘shl’ Instruction (Semantics)"
    ShlNoUnsignedWrap _ _   -> "‘shl’ Instruction (Semantics)"
    ShlNoSignedWrap _ _     -> "‘shl’ Instruction (Semantics)"
    LshrExact _ _           -> "‘lshr’ Instruction (Semantics)"
    LshrOp2Big _ _          -> "‘lshr’ Instruction (Semantics)"
    AshrExact _ _           -> "‘ashr’ Instruction (Semantics)"
    AshrOp2Big _ _          -> "‘ashr’ Instruction (Semantics)"
    ExtractElementIndex _   -> "‘extractelement’ Instruction (Semantics)"
    InsertElementIndex _    -> "‘insertelement’ Instruction (Semantics)"
    GEPOutOfBounds _        -> "‘getelementptr’ Instruction (Semantics)"

explain :: Poison e -> Doc
explain =
  \case
    AddNoUnsignedWrap _ _ ->
      "Unsigned addition caused wrapping even though the `nuw` flag was set"
    AddNoSignedWrap _ _ ->
      "Signed addition caused wrapping even though the `nsw` flag was set"
    SubNoUnsignedWrap _ _ ->
      "Unsigned subtraction caused wrapping even though the `nuw` flag was set"
    SubNoSignedWrap _ _  ->
      "Signed subtraction caused wrapping even though the `nsw` flag was set"
    MulNoUnsignedWrap _ _ ->
      "Unsigned multiplication caused wrapping even though the `nuw` flag was set"
    MulNoSignedWrap _ _ ->
      "Signed multiplication caused wrapping even though the `nsw` flag was set"
    SDivExact _ _ ->
      "Inexact signed division even though the `exact` flag was set"
    UDivExact _ _ ->
      "Inexact unsigned division even though the `exact` flag was set"
    ShlOp2Big _ _ ->
      "The second operand of `shl` was equal to or greater than the number of bits in the first operand"
    ShlNoUnsignedWrap _ _ ->
      "Left shift shifted out non-zero bits even though the `nuw` flag was set"
    ShlNoSignedWrap _ _ ->
      "Left shift shifted out some bits that disagreed with the sign bit even though the `nsw` flag was set"
    LshrExact _ _ ->
      "Inexact `lshr` (logical right shift) result even though the `exact` flag was set"
    LshrOp2Big _ _ ->
      "The second operand of `lshr` was equal to or greater than the number of bits in the first operand"
    AshrExact _ _ ->
      "Inexact `ashr` (arithmetic right shift) result even though the `exact` flag was set"
    AshrOp2Big _ _   ->
      "The second operand of `ashr` was equal to or greater than the number of bits in the first operand"
    ExtractElementIndex _   -> cat $
      [ "Attempted to extract an element from a vector at an index that was"
      , "greater than the length of the vector"
      ]
    InsertElementIndex _   -> cat $
      [ "Attempted to insert an element into a vector at an index that was"
      , "greater than the length of the vector"
      ]

    -- The following explanation is a bit unsatisfactory, because it is specific
    -- to how we treat this instruction in Crucible.
    GEPOutOfBounds _   -> cat $
      [ "Calling `getelementptr` resulted in an index that was out of bounds for the"
      , "given allocation (likely due to arithmetic overflow), but Crucible currently"
      , "treats all GEP instructions as if they had the `inbounds` flag set."
      ]

details :: forall sym.
  W4I.IsExpr (W4I.SymExpr sym) => Poison (RegValue' sym) -> [Doc]
details =
  \case
    AddNoUnsignedWrap v1 v2 -> args [v1, v2]
    AddNoSignedWrap   v1 v2 -> args [v1, v2]
    SubNoUnsignedWrap v1 v2 -> args [v1, v2]
    SubNoSignedWrap   v1 v2 -> args [v1, v2]
    MulNoUnsignedWrap v1 v2 -> args [v1, v2]
    MulNoSignedWrap   v1 v2 -> args [v1, v2]
    SDivExact         v1 v2 -> args [v1, v2]
    UDivExact         v1 v2 -> args [v1, v2]
    ShlOp2Big         v1 v2 -> args [v1, v2]
    ShlNoUnsignedWrap v1 v2 -> args [v1, v2]
    ShlNoSignedWrap   v1 v2 -> args [v1, v2]
    LshrExact         v1 v2 -> args [v1, v2]
    LshrOp2Big        v1 v2 -> args [v1, v2]
    AshrExact         v1 v2 -> args [v1, v2]
    AshrOp2Big        v1 v2 -> args [v1, v2]
    ExtractElementIndex v   -> args [v]
    InsertElementIndex v    -> args [v]
    GEPOutOfBounds v        -> args [v]

 where
 args :: forall w. [RegValue' sym (BVType w)] -> [Doc]
 args []     = [ text "No arguments" ]
 args [RV v] = [ text "Argument:" <+> W4I.printSymExpr v ]
 args vs     = [ hsep (text "Arguments:" : map (W4I.printSymExpr . unRV) vs) ]


-- | Pretty print an error message relating to LLVM poison values,
--   when given a printer to produce a detailed message.
pp :: (Poison e -> [Doc]) -> Poison e -> Doc
pp extra poison = vcat $
  [ "Poison value encountered: "
  , explain poison
  , vcat (extra poison)
  , cat [ "Reference: "
        , text (unpack (ppStd (standard poison)))
        , cite poison
        ]
  ] ++ case stdURL (standard poison) of
         Just url -> ["Document URL:" <+> text (unpack url)]
         Nothing  -> []

-- | Pretty print an error message relating to LLVM poison values
ppReg ::W4I.IsExpr (W4I.SymExpr sym) => Poison (RegValue' sym) -> Doc
ppReg = pp details

-- | Concretize a poison error message.
concPoison :: forall sym.
  W4I.IsExprBuilder sym =>
  sym ->
  (forall tp. W4I.SymExpr sym tp -> IO (GroundValue tp)) ->
  Poison (RegValue' sym) -> IO (Poison (RegValue' sym))
concPoison sym conc poison =
  let bv :: forall w. (1 <= w) => RegValue' sym (BVType w) -> IO (RegValue' sym (BVType w))
      bv (RV x) = RV <$> concBV sym conc x in
  case poison of
    AddNoUnsignedWrap v1 v2 ->
      AddNoUnsignedWrap <$> bv v1 <*> bv v2
    AddNoSignedWrap v1 v2 ->
      AddNoSignedWrap <$> bv v1 <*> bv v2
    SubNoUnsignedWrap v1 v2 ->
      SubNoUnsignedWrap <$> bv v1 <*> bv v2
    SubNoSignedWrap v1 v2 ->
      SubNoSignedWrap <$> bv v1 <*> bv v2
    MulNoUnsignedWrap v1 v2 ->
      MulNoUnsignedWrap<$> bv v1 <*> bv v2
    MulNoSignedWrap v1 v2 ->
      MulNoSignedWrap <$> bv v1 <*> bv v2
    UDivExact v1 v2 ->
      UDivExact <$> bv v1 <*> bv v2
    SDivExact v1 v2 ->
      SDivExact <$> bv v1 <*> bv v2
    ShlOp2Big v1 v2 ->
      ShlOp2Big <$> bv v1 <*> bv v2
    ShlNoUnsignedWrap v1 v2 ->
      ShlNoUnsignedWrap <$> bv v1 <*> bv v2
    ShlNoSignedWrap v1 v2 ->
      ShlNoSignedWrap <$> bv v1 <*> bv v2
    LshrExact v1 v2 ->
      LshrExact <$> bv v1 <*> bv v2
    LshrOp2Big v1 v2 ->
      LshrOp2Big <$> bv v1 <*> bv v2
    AshrExact v1 v2 ->
      AshrExact <$> bv v1 <*> bv v2
    AshrOp2Big v1 v2 ->
      AshrOp2Big <$> bv v1 <*> bv v2
    ExtractElementIndex v ->
      ExtractElementIndex <$> bv v
    InsertElementIndex v ->
      InsertElementIndex <$> bv v
    GEPOutOfBounds v ->
      GEPOutOfBounds <$> bv v


-- -----------------------------------------------------------------------
-- ** Instances

-- The weirdness in these instances is due to existential quantification over
-- the width. We have to make sure the type variable doesn't escape its scope.

$(return [])

eqcPoison :: forall e.
  (forall t1 t2. e t1 -> e t2 -> Maybe (t1 :~: t2)) ->
  Poison e -> Poison e -> Maybe (() :~: ())
eqcPoison subterms =
  let subterms' :: forall p q. e p -> e q -> Maybe (() :~: ())
      subterms' a b =
         case subterms a b of
           Just Refl -> Just Refl
           Nothing   -> Nothing
   in $(U.structuralTypeEquality [t|Poison|]
       [ ( U.DataArg 0 `U.TypeApp` U.AnyType, [| subterms' |])
       ])

ordcPoison :: forall e f.
  (forall t1 t2. e t1 -> f t2 -> OrderingF t1 t2) ->
  Poison e -> Poison f -> OrderingF () ()
ordcPoison subterms =
  let subterms' :: forall p q. e p -> f q -> OrderingF () ()
      subterms' a b =
         case subterms a b of
           EQF -> (EQF :: OrderingF () ())
           GTF -> (GTF :: OrderingF () ())
           LTF -> (LTF :: OrderingF () ())

   in $(U.structuralTypeOrd [t|Poison|]
       [ ( U.DataArg 0 `U.TypeApp` U.AnyType, [| subterms' |])
       ])

instance TestEqualityC Poison where
  testEqualityC subterms x y = isJust $ eqcPoison subterms x y

instance OrdC Poison where
  compareC subterms x y = toOrdering $ ordcPoison subterms x y

instance FunctorF Poison where
  fmapF = TF.fmapFDefault

instance FoldableF Poison where
  foldMapF = TF.foldMapFDefault

instance TraversableF Poison where
  traverseF :: forall m e f. Applicative m
            => (forall s. e s -> m (f s))
            -> Poison e
            -> m (Poison f)
  traverseF =
    $(U.structuralTraversal [t|Poison|]
       [ ( U.DataArg 0 `U.TypeApp` U.AnyType
         , [| ($) |] -- \f x -> f x
         )
       ]
     )
