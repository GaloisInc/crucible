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
  , pp
  ) where

import           Data.Kind (Type)
import           Data.Text (unpack)
import           Data.Maybe (isJust)
import           Data.Typeable (Typeable)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.Parameterized.TraversableF as TF
import           Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..), TraversableF(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.ClassesC (TestEqualityC(..))

import           Lang.Crucible.Types
import           Lang.Crucible.LLVM.Extension.Safety.Standards
import qualified What4.Interface as W4I

-- | TODO(langston): Record type information for error messages
data Poison (e :: CrucibleType -> Type) where

  AddNoUnsignedWrap   :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  AddNoSignedWrap     :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  SubNoUnsignedWrap   :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  SubNoSignedWrap     :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  MulNoUnsignedWrap   :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  MulNoSignedWrap     :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  UDivExact           :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  SDivExact           :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  ShlOp2Big           :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  ShlNoUnsignedWrap   :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  ShlNoSignedWrap     :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  LshrExact           :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  LshrOp2Big          :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  AshrExact           :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  AshrOp2Big          :: e (BVType w) -- ^ @op1@
                      -> e (BVType w) -- ^ @op2@
                      -> Poison e
  -- | TODO(langston): Figure out how to store the 'Vector'
  ExtractElementIndex :: e (BVType w)       -- ^ @idx@
                      -> Poison e
  -- | TODO(langston): Figure out how to store the 'Vector'
  InsertElementIndex  :: e (BVType w)       -- ^ @idx@
                      -> Poison e
  -- | TODO(langston): Figure out how to store the 'LLVMPointerType'
  GEPOutOfBounds      :: e (BVType w) -- ^ @idx@
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

-- TODO: print values
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
      , "the given allocation (likely due to arithmetic overflo(BVType w), but Crucible"
      , "currently treats all GEP instructions as if they had the `inbounds`"
      , "flag set."
      ]

pp :: Poison e -> Doc
pp poison = vcat $
  [ "Poison value encountered: "
  , explain poison
  , cat [ "Reference: "
         , text (unpack (ppStd (standard poison)))
         , cite poison
         ]
  ] ++ case stdURL (standard poison) of
         Just url -> ["Document URL:" <+> text (unpack url)]
         Nothing  -> []

$(return [])

instance TestEqualityC Poison where
  testEqualityC testSubterm t1 t2 =
    case (t1, t2) of
      ( AddNoUnsignedWrap s1 s2, AddNoUnsignedWrap r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (AddNoSignedWrap s1 s2, AddNoSignedWrap r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (SubNoUnsignedWrap s1 s2, SubNoUnsignedWrap r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (SubNoSignedWrap s1 s2, SubNoSignedWrap r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (MulNoUnsignedWrap s1 s2, MulNoUnsignedWrap r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (MulNoSignedWrap s1 s2, MulNoSignedWrap r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (UDivExact s1 s2, UDivExact r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (SDivExact s1 s2, SDivExact r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (ShlOp2Big s1 s2, ShlOp2Big r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (ShlNoUnsignedWrap s1 s2, ShlNoUnsignedWrap r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (ShlNoSignedWrap s1 s2, ShlNoSignedWrap r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (LshrExact s1 s2, LshrExact r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (LshrOp2Big s1 s2, LshrOp2Big r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (AshrExact s1 s2, AshrExact r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (AshrOp2Big s1 s2, AshrOp2Big r1 r2) ->
        isJust (testSubterm s1 s2) && isJust (testSubterm r1 r2)
      (ExtractElementIndex s, ExtractElementIndex r) ->
        isJust (testSubterm s r)
      (InsertElementIndex s, InsertElementIndex r) ->
        isJust (testSubterm s r)
      (GEPOutOfBounds s, GEPOutOfBounds r) ->
        isJust (testSubterm s r)
      (_, _) -> False

-- instance OrdF Poison where
--   compareF = _

instance FunctorF Poison where
  fmapF = TF.fmapFDefault

instance FoldableF Poison where
  foldMapF = TF.foldMapFDefault

instance TraversableF Poison where
  traverseF = $(U.structuralTraversal [t|Poison|] [])
