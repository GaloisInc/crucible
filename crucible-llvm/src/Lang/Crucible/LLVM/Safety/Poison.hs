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
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.Safety.Poison
  ( Poison(..)
  , cite
  , pp
  ) where

import           Data.Kind (Type)
import           Data.Text (Text, unwords, unlines)
import           Data.Typeable (Typeable)
import           Prelude hiding (unwords, unlines)

import qualified What4.Interface as W4I

import           Lang.Crucible.CFG.Generator (Expr)
import           Lang.Crucible.LLVM.Extension (LLVM)
import           Lang.Crucible.LLVM.Safety.Standards
import           Lang.Crucible.LLVM.Translation.Types (LLVMPointerType)
import           Data.Parameterized.TraversableFC

import           Data.Functor.Compose
import           Lang.Crucible.Types
import           What4.BaseTypes

-- | TODO(langston): Record type information for error messages
data Poison (e :: W4I.BaseType -> Type) where

  AddNoUnsignedWrap   :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  AddNoSignedWrap     :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  SubNoUnsignedWrap   :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  SubNoSignedWrap     :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  MulNoUnsignedWrap   :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  MulNoSignedWrap     :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  UDivExact           :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  SDivExact           :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  ShlOp2Big           :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  ShlNoUnsignedWrap   :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  ShlNoSignedWrap     :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  LshrExact           :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  LshrOp2Big          :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  AshrExact           :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  AshrOp2Big          :: e (W4I.BaseBVType w) -- ^ @op1@
                      -> e (W4I.BaseBVType w) -- ^ @op2@
                      -> Poison e
  -- | TODO(langston): Figure out how to store the 'Vector'
  ExtractElementIndex :: e (W4I.BaseBVType w)       -- ^ @idx@
                      -> Poison e
  -- | TODO(langston): Figure out how to store the 'Vector'
  InsertElementIndex  :: e (W4I.BaseBVType w)       -- ^ @idx@
                      -> Poison e
  -- | TODO(langston): Figure out how to store the 'LLVMPointerType'
  GEPOutOfBounds      :: e (W4I.BaseBVType w) -- ^ @idx@
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
    -- ExtractElementIndex _ _ -> LLVMRef LLVM8
    -- InsertElementIndex _ _  -> LLVMRef LLVM8
    -- GEPOutOfBounds _ _      -> LLVMRef LLVM8

-- | Which section(s) of the document state that this is poison?
cite :: Poison e -> Text
cite =
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
    -- ExtractElementIndex _ _ -> "‘extractelement’ Instruction (Semantics)"
    -- InsertElementIndex _ _  -> "‘insertelement’ Instruction (Semantics)"
    -- GEPOutOfBounds _ _      -> "‘getelementptr’ Instruction (Semantics)"

explain :: Poison e -> Text
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
    ShlOp2Big _ _ -> unwords $
      [ "The second operand of `shl` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    ShlNoUnsignedWrap _ _ ->
      "Left shift shifted out non-zero bits even though the `nuw` flag was set"
    ShlNoSignedWrap _ _ -> unwords $
      [ "Left shift shifted out some bits that disagreed with the sign bit"
      , "even though the `nsw` flag was set"
      ]
    LshrExact _ _ -> unwords $
      [ "Inexact `lshr` (logical right shift) result even though the `exact`"
      , "flag was set"
      ]
    LshrOp2Big _ _ -> unwords $
      [ "The second operand of `lshr` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    AshrExact _ _ -> unwords $
      [ "Inexact `ashr` (arithmetic right shift) result even though the `exact`"
      , "flag was set"
      ]
    AshrOp2Big _ _   -> unwords $
      [ "The second operand of `ashr` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    -- ExtractElementIndex _ _ -> unwords $
    --   [ "Attempted to extract an element from a vector at an index that was"
    --   , "greater than the length of the vector"
    --   ]
    -- InsertElementIndex _ _ -> unwords $
    --   [ "Attempted to insert an element into a vector at an index that was"
    --   , "greater than the length of the vector"
    --   ]
    -- The following explanation is a bit unsatisfactory, because it is specific
    -- to how we treat this instruction in Crucible.
    -- GEPOutOfBounds _ _ -> unwords $
    --   [ "Calling `getelementptr` resulted in an index that was out of bounds for"
    --   , "the given allocation (likely due to arithmetic overflow), but Crucible"
    --   , "currently treats all GEP instructions as if they had the `inbounds`"
    --   , "flag set."
    --   ]

pp :: Poison (Compose (Expr ext s) BaseToType) -> Text
pp poison = unlines $
  [ "Poison value encountered: "
  , explain poison
  , unwords ["Reference: ", ppStd (standard poison), cite poison]
  ] ++ case stdURL (standard poison) of
         Just url -> ["Document URL: " <> url]
         Nothing  -> []

-- pp :: W4I.IsExpr e => Poison e -> Text
-- pp poison = unlines $
--   [ "Poison value encountered: "
--   , explain poison
--   , unwords ["Reference: ", ppStd (standard poison), cite poison]
--   ] ++ case stdURL (standard poison) of
--          Just url -> ["Document URL: " <> url]
--          Nothing  -> []
