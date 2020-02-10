-- |
-- Module           : Lang.Crucible.LLVM.Safety.Poison
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
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module Lang.Crucible.LLVM.Extension.Safety.Poison
  ( Poison(..)
  , cite
  , explain
  , standard
  , detailsReg
  , pp
  , ppReg
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

import           Lang.Crucible.LLVM.Extension.Safety.Standards
import           Lang.Crucible.Types
--import qualified What4.Interface as W4I

data Poison (e :: CrucibleType -> Type) where
  -- | Arguments: @op1@, @op2@
  AddNoUnsignedWrap   :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  AddNoSignedWrap     :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  SubNoUnsignedWrap   :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  SubNoSignedWrap     :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  MulNoUnsignedWrap   :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  MulNoSignedWrap     :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  UDivExact           :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  SDivExact           :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  ShlOp2Big           :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  ShlNoUnsignedWrap   :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  ShlNoSignedWrap     :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  LshrExact           :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  LshrOp2Big          :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  AshrExact           :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | Arguments: @op1@, @op2@
  AshrOp2Big          :: e (BVType w)
                      -> e (BVType w)
                      -> Poison e
  -- | TODO(langston): store the 'Vector'
  ExtractElementIndex :: e (BVType w)
                      -> Poison e
  -- | TODO(langston): store the 'Vector'
  InsertElementIndex  :: e (BVType w)
                      -> Poison e
  -- | TODO(langston): store the 'LLVMPointerType'
  GEPOutOfBounds      :: e (BVType w)
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
    ShlOp2Big _ _ -> cat $
      [ "The second operand of `shl` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    ShlNoUnsignedWrap _ _ ->
      "Left shift shifted out non-zero bits even though the `nuw` flag was set"
    ShlNoSignedWrap _ _ -> cat $
      [ "Left shift shifted out some bits that disagreed with the sign bit"
      , "even though the `nsw` flag was set"
      ]
    LshrExact _ _ -> cat $
      [ "Inexact `lshr` (logical right shift) result even though the `exact`"
      , "flag was set"
      ]
    LshrOp2Big _ _ -> cat $
      [ "The second operand of `lshr` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    AshrExact _ _ -> cat $
      [ "Inexact `ashr` (arithmetic right shift) result even though the `exact`"
      , "flag was set"
      ]
    AshrOp2Big _ _   -> cat $
      [ "The second operand of `ashr` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
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
      [ "Calling `getelementptr` resulted in an index that was out of bounds for"
      , "the given allocation (likely due to arithmetic overflow), but Crucible"
      , "currently treats all GEP instructions as if they had the `inbounds`"
      , "flag set."
      ]

detailsReg ::
  Poison e -> [Doc]
detailsReg = const [] -- TODO: details
  -- \case
  --   AddNoUnsignedWrap _ _ -> _
  --   AddNoSignedWrap _ _ -> _
  --   SubNoUnsignedWrap _ _ -> _
  --   SubNoSignedWrap _ _  -> _
  --   MulNoUnsignedWrap _ _ -> _
  --   MulNoSignedWrap _ _ -> _
  --   SDivExact _ _ -> _
  --   UDivExact _ _ -> _
  --   ShlOp2Big _ _ -> _
  --   ShlNoUnsignedWrap _ _ -> _
  --   ShlNoSignedWrap _ _ -> _
  --   LshrExact _ _ -> _
  --   LshrOp2Big _ _ -> _
  --   AshrExact _ _ -> _
  --   AshrOp2Big _ _   -> _
  --   ExtractElementIndex _   -> _
  --   InsertElementIndex _   -> _
  --   GEPOutOfBounds _   -> _

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

ppReg :: Poison e -> Doc
ppReg = pp detailsReg

-- -----------------------------------------------------------------------
-- ** Instances

-- The weirdness in these instances is due to existential quantification over
-- the width. We have to make sure the type variable doesn't escape its scope.

$(return [])

instance TestEqualityC Poison where
  testEqualityC subterms x y = isJust $
    $(U.structuralTypeEquality [t|Poison|]
       [ ( U.DataArg 0 `U.TypeApp` U.AnyType
         , [| \z w -> subterms z w >> Just Refl |]
         )
       ]
     ) x y

instance OrdC Poison where
  compareC subterms p1 p2 = toOrdering $
    $(U.structuralTypeOrd [t|Poison|]
       [ ( U.DataArg 0 `U.TypeApp` U.AnyType
         , [| \z w -> case subterms z w of
                        EQF -> (EQF :: OrderingF () ())
                        GTF -> (GTF :: OrderingF () ())
                        LTF -> (LTF :: OrderingF () ())

            |]
         )
       ]
     ) p1 p2

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
