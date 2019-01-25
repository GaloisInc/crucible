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
--------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.Safety.Poison
  ( Poison(..)
  , cite
  , pp
  ) where

import           Data.Text (Text, unwords, unlines)
import           Data.Typeable (Typeable)
import           Prelude hiding (unwords, unlines)

import qualified What4.Interface as W4I

import           Lang.Crucible.LLVM.Safety.Standards


-- | TODO: Check which are poison vs. undefined
data Poison sym where
  AddNoUnsignedWrap   :: W4I.SymBV sym w -> Poison sym
  AddNoSignedWrap     :: Poison sym
  SubNoUnsignedWrap   :: Poison sym
  SubNoSignedWrap     :: Poison sym
  MulNoUnsignedWrap   :: Poison sym
  MulNoSignedWrap     :: Poison sym
  UDivByZero          :: Poison sym
  SDivByZero          :: Poison sym
  URemByZero          :: Poison sym
  SRemByZero          :: Poison sym
  UDivExact           :: Poison sym
  SDivExact           :: Poison sym
  SDivOverflow        :: Poison sym
  SRemOverflow        :: Poison sym
  ShlOp2Big           :: Poison sym
  ShlNoUnsignedWrap   :: Poison sym
  ShlNoSignedWrap     :: Poison sym
  LshrExact           :: Poison sym
  LshrOp2Big          :: Poison sym
  AshrExact           :: Poison sym
  AshrOp2Big          :: Poison sym
  ExtractElementIndex :: Poison sym
  InsertElementIndex  :: Poison sym
  GEPOutOfBounds      :: Poison sym
  deriving (Typeable)

standard :: Poison sym -> Standard
standard =
  \case
    AddNoUnsignedWrap _ -> LLVMRef LLVM8
    AddNoSignedWrap     -> LLVMRef LLVM8
    SubNoUnsignedWrap   -> LLVMRef LLVM8
    SubNoSignedWrap     -> LLVMRef LLVM8
    MulNoUnsignedWrap   -> LLVMRef LLVM8
    MulNoSignedWrap     -> LLVMRef LLVM8
    UDivByZero          -> LLVMRef LLVM8
    SDivByZero          -> LLVMRef LLVM8
    URemByZero          -> LLVMRef LLVM8
    SRemByZero          -> LLVMRef LLVM8
    UDivExact           -> LLVMRef LLVM8
    SDivExact           -> LLVMRef LLVM8
    SDivOverflow        -> LLVMRef LLVM8
    SRemOverflow        -> LLVMRef LLVM8
    ShlOp2Big           -> LLVMRef LLVM8
    ShlNoUnsignedWrap   -> LLVMRef LLVM8
    ShlNoSignedWrap     -> LLVMRef LLVM8
    LshrExact           -> LLVMRef LLVM8
    LshrOp2Big          -> LLVMRef LLVM8
    AshrExact           -> LLVMRef LLVM8
    AshrOp2Big          -> LLVMRef LLVM8
    ExtractElementIndex -> LLVMRef LLVM8
    InsertElementIndex  -> LLVMRef LLVM8
    GEPOutOfBounds      -> LLVMRef LLVM8

-- | Which section(s) of the document state that this is poison?
cite :: Poison sym -> Text
cite =
  \case
    AddNoUnsignedWrap _     -> "‘add’ Instruction (Semantics)"
    AddNoSignedWrap         -> "‘add’ Instruction (Semantics)"
    SubNoUnsignedWrap       -> "‘sub’ Instruction (Semantics)"
    SubNoSignedWrap         -> "‘sub’ Instruction (Semantics)"
    MulNoUnsignedWrap       -> "‘mul’ Instruction (Semantics)"
    MulNoSignedWrap         -> "‘mul’ Instruction (Semantics)"
    UDivByZero              -> "‘udiv’ Instruction (Semantics)"
    SDivByZero              -> "‘sdiv’ Instruction (Semantics)"
    URemByZero              -> "‘urem’ Instruction (Semantics)"
    SRemByZero              -> "‘srem’ Instruction (Semantics)"
    UDivExact               -> "‘udiv’ Instruction (Semantics)"
    SDivExact               -> "‘sdiv’ Instruction (Semantics)"
    SDivOverflow            -> "‘sdiv’ Instruction (Semantics)"
    SRemOverflow            -> "‘srem’ Instruction (Semantics)"
    ShlOp2Big               -> "‘shl’ Instruction (Semantics)"
    ShlNoUnsignedWrap       -> "‘shl’ Instruction (Semantics)"
    ShlNoSignedWrap         -> "‘shl’ Instruction (Semantics)"
    LshrExact               -> "‘lshr’ Instruction (Semantics)"
    LshrOp2Big              -> "‘lshr’ Instruction (Semantics)"
    AshrExact               -> "‘ashr’ Instruction (Semantics)"
    AshrOp2Big              -> "‘ashr’ Instruction (Semantics)"
    ExtractElementIndex     -> "‘extractelement’ Instruction (Semantics)"
    InsertElementIndex      -> "‘insertelement’ Instruction (Semantics)"
    GEPOutOfBounds          -> "‘getelementptr’ Instruction (Semantics)"

explain :: Poison sym -> Text
explain =
  \case
    AddNoUnsignedWrap _ ->
      "Unsigned addition caused wrapping even though the `nuw` flag was set"
    AddNoSignedWrap   ->
      "Signed addition caused wrapping even though the `nsw` flag was set"
    SubNoUnsignedWrap ->
      "Unsigned subtraction caused wrapping even though the `nuw` flag was set"
    SubNoSignedWrap   ->
      "Signed subtraction caused wrapping even though the `nsw` flag was set"
    MulNoUnsignedWrap ->
      "Unsigned multiplication caused wrapping even though the `nuw` flag was set"
    MulNoSignedWrap   ->
      "Signed multiplication caused wrapping even though the `nsw` flag was set"
    UDivByZero        -> "Unsigned division by zero"
    SDivByZero        -> "Signed division by zero"
    URemByZero        -> "Unsigned division by zero via remainder"
    SRemByZero        -> "Signed division by zero via remainder"
    SDivExact         ->
      "Inexact signed division even though the `exact` flag was set"
    UDivExact         ->
      "Inexact unsigned division even though the `exact` flag was set"
    SDivOverflow      -> "Overflow during signed division"
    SRemOverflow      -> "Overflow during signed division (via signed remainder)"
    ShlOp2Big         -> unwords $
      [ "The second operand of `shl` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    ShlNoUnsignedWrap ->
      "Left shift shifted out non-zero bits even though the `nuw` flag was set"
    ShlNoSignedWrap   -> unwords $
      [ "Left shift shifted out some bits that disagreed with the sign bit"
      , "even though the `nsw` flag was set"
      ]
    LshrExact         -> unwords $
      [ "Inexact `lshr` (logical right shift) result even though the `exact`"
      , "flag was set"
      ]
    LshrOp2Big        -> unwords $
      [ "The second operand of `lshr` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    AshrExact         -> unwords $
      [ "Inexact `ashr` (arithmetic right shift) result even though the `exact`"
      , "flag was set"
      ]
    AshrOp2Big        -> unwords $
      [ "The second operand of `ashr` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    ExtractElementIndex -> unwords $
      [ "Attempted to extract an element from a vector at an index that was"
      , "greater than the length of the vector"
      ]
    InsertElementIndex  -> unwords $
      [ "Attempted to insert an element into a vector at an index that was"
      , "greater than the length of the vector"
      ]
    -- The following explanation is a bit unsatisfactory, because it is specific
    -- to how we treat this instruction in Crucible.
    GEPOutOfBounds -> unwords $
      [ "Calling `getelementptr` resulted in an index that was out of bounds for"
      , "the given allocation (likely due to arithmetic overflow), but Crucible"
      , "currently treats all GEP instructions as if they had the `inbounds`"
      , "flag set."
      ]

pp :: Poison sym -> Text
pp poison = unlines $
  [ "Poison value encountered: "
  , explain poison
  , unwords ["Reference: ", ppStd (standard poison), cite poison]
  ] ++ case stdURL (standard poison) of
         Just url -> ["Document URL: " <> url]
         Nothing  -> []
