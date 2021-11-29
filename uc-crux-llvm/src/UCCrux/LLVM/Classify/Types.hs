{-
Module       : UCCrux.LLVM.Classify.Types
Description  : Types and utility functions on them used in classification
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}

module UCCrux.LLVM.Classify.Types
  ( Explanation (..),
    Located (..),
    ppLocated,
    partitionExplanations,
    TruePositive (..),
    TruePositiveTag (..),
    truePositiveTag,
    Diagnosis (..),
    DiagnosisTag (..),
    diagnose,
    diagnoseTag,
    prescribe,
    ppTruePositive,
    ppTruePositiveTag,
    Unclassified (..),
    doc,
    Uncertainty (..),
    partitionUncertainty,
    ppUncertainty,
    Unfixable (..),
    ppUnfixable,
    Unfixed (..),
    ppUnfixed,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void (Void)
import           GHC.Generics (Generic)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)

import qualified What4.ProgramLoc as What4

import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB

import           Prelude hiding (log)

import           Control.Exception (displayException)
import           Control.Lens (Lens', lens, to, (^.))
import           Panic (Panic)

import           Data.Parameterized.Some (Some)

import qualified Lang.Crucible.Simulator as Crucible

import           UCCrux.LLVM.Constraints (NewConstraint)
import           UCCrux.LLVM.Cursor (Where, ppWhere)
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented)
import           UCCrux.LLVM.FullType.Type (FullType)
import           UCCrux.LLVM.PP (ppProgramLoc)
{- ORMOLU_ENABLE -}

data Located a = Located
  { location :: !What4.ProgramLoc,
    locatedValue :: a
  }
  deriving (Eq, Ord, Functor, Generic, Show)

ppLocated :: (a -> Text) -> Located a -> Text
ppLocated ppVal (Located loc val) =
  Text.unwords [ppVal val, Text.pack "at", ppProgramLoc loc]

data TruePositiveTag
  = TagConcretelyFailingAssert
  | TagDoubleFree
  | TagUDivByConcreteZero
  | TagSDivByConcreteZero
  | TagURemByConcreteZero
  | TagSRemByConcreteZero
  | TagReadNonPointer
  | TagWriteNonPointer
  | TagFreeNonPointer
  | TagReadUninitializedStack
  | TagReadUninitializedHeap
  | TagCallNonFunctionPointer
  | TagFloatToPointer
  | TagDerefFunctionPointer
  deriving (Eq, Ord)

data TruePositive
  = ConcretelyFailingAssert
  | DoubleFree
  | UDivByConcreteZero
  | SDivByConcreteZero
  | URemByConcreteZero
  | SRemByConcreteZero
  | ReadNonPointer
  | WriteNonPointer
  | FreeNonPointer
  | ReadUninitializedStack !String -- program location of allocation
  | ReadUninitializedHeap !String -- program location of allocation
  | CallNonFunctionPointer !String -- program location of allocation
  | FloatToPointer
  | DerefFunctionPointer !L.Symbol -- Name of function
  deriving (Eq, Ord)

truePositiveTag :: TruePositive -> TruePositiveTag
truePositiveTag =
  \case
    ConcretelyFailingAssert {} -> TagConcretelyFailingAssert
    DoubleFree {} -> TagDoubleFree
    UDivByConcreteZero {} -> TagUDivByConcreteZero
    SDivByConcreteZero {} -> TagSDivByConcreteZero
    URemByConcreteZero {} -> TagURemByConcreteZero
    SRemByConcreteZero {} -> TagSRemByConcreteZero
    ReadNonPointer {} -> TagReadNonPointer
    WriteNonPointer {} -> TagWriteNonPointer
    FreeNonPointer {} -> TagFreeNonPointer
    ReadUninitializedStack {} -> TagReadUninitializedStack
    ReadUninitializedHeap {} -> TagReadUninitializedHeap
    CallNonFunctionPointer {} -> TagCallNonFunctionPointer
    FloatToPointer {} -> TagFloatToPointer
    DerefFunctionPointer {} -> TagDerefFunctionPointer

ppTruePositiveTag :: TruePositiveTag -> Text
ppTruePositiveTag =
  \case
    TagConcretelyFailingAssert -> "Concretely failing user assertion"
    TagDoubleFree -> "Double free"
    TagUDivByConcreteZero -> "Unsigned division with a concretely zero divisor"
    TagSDivByConcreteZero -> "Signed division with a concretely zero divisor"
    TagURemByConcreteZero -> "Unsigned remainder with a concretely zero divisor"
    TagSRemByConcreteZero -> "Signed remainder with a concretely zero divisor"
    TagReadNonPointer -> "Read from data that concretely wasn't a pointer"
    TagWriteNonPointer -> "Write to data that concretely wasn't a pointer"
    TagFreeNonPointer -> "`free` called on data that concretely wasn't a pointer"
    TagReadUninitializedStack -> "Read from uninitialized stack allocation"
    TagReadUninitializedHeap -> "Read from uninitialized heap allocation"
    TagCallNonFunctionPointer -> "Called a pointer that wasn't a function pointer"
    TagFloatToPointer -> "Treated float as pointer"
    TagDerefFunctionPointer -> "Dereferenced function pointer"

ppTruePositive :: TruePositive -> Text
ppTruePositive =
  \case
    pos@(ReadUninitializedStack loc) -> withLoc pos loc
    pos@(ReadUninitializedHeap loc) -> withLoc pos loc
    pos@(CallNonFunctionPointer loc) -> withLoc pos loc
    tp -> ppTruePositiveTag (truePositiveTag tp)
  where
    withLoc pos loc =
      ppTruePositiveTag (truePositiveTag pos) <> " allocated at " <> Text.pack loc

-- | All of the preconditions that we can deduce. We know how to detect and fix
-- these issues.
data DiagnosisTag
  = DiagnoseWriteBadAlignment
  | DiagnoseReadBadAlignment
  | DiagnoseFreeUnallocated
  | DiagnoseFreeBadOffset
  | DiagnoseWriteUnmapped
  | DiagnoseReadUninitialized
  | DiagnoseReadUninitializedOffset
  | DiagnosePointerConstOffset
  | DiagnoseMemsetTooSmall
  | DiagnoseAddSignedWrap
  | DiagnoseSubSignedWrap
  | DiagnoseNonZero
  deriving (Eq, Ord)

data Diagnosis = Diagnosis
  { diagnosisTag :: DiagnosisTag,
    diagnosisWhere :: Where
  }

diagnoseTag :: DiagnosisTag -> Text
diagnoseTag =
  \case
    DiagnoseWriteBadAlignment -> "Write to a pointer with insufficient alignment"
    DiagnoseReadBadAlignment -> "Read from a pointer with insufficient alignment"
    DiagnoseFreeUnallocated -> "`free` called on an unallocated pointer"
    DiagnoseFreeBadOffset -> "`free` called on pointer with nonzero offset"
    DiagnoseWriteUnmapped -> "Write to an unmapped pointer"
    DiagnoseReadUninitialized -> "Read from an uninitialized pointer"
    DiagnoseReadUninitializedOffset -> "Read from an uninitialized pointer calculated from a pointer"
    DiagnosePointerConstOffset -> "Addition of a constant offset to a pointer"
    DiagnoseMemsetTooSmall -> "`memset` called on pointer to too-small allocation"
    DiagnoseAddSignedWrap -> "Addition of a constant caused signed wrap of an int"
    DiagnoseSubSignedWrap -> "Subtraction of a constant caused signed wrap of an int"
    DiagnoseNonZero -> "Division or remainder by zero"

diagnose :: Diagnosis -> PP.Doc ann
diagnose (Diagnosis tag which) = PP.pretty (diagnoseTag tag) PP.<+> ppWhere which

prescribe :: DiagnosisTag -> Text
prescribe =
  ("Prescription: Add a precondition that " <>)
    . \case
      DiagnoseWriteBadAlignment -> "the pointer is sufficiently aligned."
      DiagnoseReadBadAlignment -> "the pointer is sufficiently aligned."
      DiagnoseFreeUnallocated -> "the pointer points to initialized memory."
      DiagnoseFreeBadOffset -> "the pointer points to initialized memory."
      DiagnoseWriteUnmapped -> "the pointer points to allocated memory."
      DiagnoseReadUninitialized -> "the pointer points to initialized memory."
      DiagnoseReadUninitializedOffset -> "the pointer points to initialized memory."
      DiagnosePointerConstOffset -> "the allocation is at least that size."
      DiagnoseMemsetTooSmall -> "the allocation is at least that size."
      DiagnoseAddSignedWrap -> "the integer is small enough"
      DiagnoseSubSignedWrap -> "the integer is large enough"
      DiagnoseNonZero -> "the integer is not zero"

-- | There was an error and we know roughly what sort it was, but we still can't
-- do anything about it, i.e., it\'s not clear what kind of precondition could
-- avoid the error.
data Unfixable
  = -- | The addition of an offset of a pointer such that the result points
    -- beyond (one past) the end of the allocation is undefined behavior -
    -- see the @PtrAddOffsetOutOfBounds@ constructor of @UndefinedBehavior@.
    -- If the offset that was added is symbolic and not part of an argument or
    -- global variable, it\'s not clear what kind of precondition could
    -- mitigate/avoid the error.
    AddSymbolicOffsetToInputPointer
  deriving (Eq, Ord, Show)

ppUnfixable :: Unfixable -> Text
ppUnfixable =
  \case
    AddSymbolicOffsetToInputPointer ->
      "Addition of a symbolic offset to pointer in argument, global variable, or return value of skipped function"

-- | We know how we *could* fix this in theory, but haven't implemented it yet.
data Unfixed
  = UnfixedArgPtrOffsetArg
  | UnfixedFunctionPtrInInput
  deriving (Eq, Ord, Show)

ppUnfixed :: Unfixed -> Text
ppUnfixed =
  \case
    UnfixedArgPtrOffsetArg -> "Addition of an offset from argument to a pointer in argument"
    UnfixedFunctionPtrInInput ->
      "Called function pointer in argument, global, or return value of skipped function"

-- | We don't (yet) know what to do about this error, so we can't continue
-- executing this function.
data Unclassified
  = UnclassifiedUndefinedBehavior !What4.ProgramLoc (Doc Void) (Some UB.UndefinedBehavior)
  | UnclassifiedMemoryError !What4.ProgramLoc (Doc Void)

loc :: Lens' Unclassified What4.ProgramLoc
loc =
  lens
    ( \case
        UnclassifiedUndefinedBehavior loc' _ _ -> loc'
        UnclassifiedMemoryError loc' _ -> loc'
    )
    ( \s loc' ->
        case s of
          UnclassifiedUndefinedBehavior _ doc' val ->
            UnclassifiedUndefinedBehavior loc' doc' val
          UnclassifiedMemoryError _ doc' ->
            UnclassifiedMemoryError loc' doc'
    )

doc :: Lens' Unclassified (Doc Void)
doc =
  lens
    ( \case
        UnclassifiedUndefinedBehavior _ doc' _ -> doc'
        UnclassifiedMemoryError _ doc' -> doc'
    )
    ( \s doc' ->
        case s of
          UnclassifiedUndefinedBehavior loc' _ val ->
            UnclassifiedUndefinedBehavior loc' doc' val
          UnclassifiedMemoryError loc' _ ->
            UnclassifiedMemoryError loc' doc'
    )

-- | Only used in tests, not a valid 'Show' instance.
instance Show Unclassified where
  show =
    \case
      UnclassifiedUndefinedBehavior {} -> "Undefined behavior"
      UnclassifiedMemoryError {} -> "Memory error"

-- | Possible sources of uncertainty, these might be true or false positives
data Uncertainty
  = UUnclassified Unclassified
  | UUnfixable Unfixable
  | UUnfixed Unfixed
  | -- | Simulation, input generation, or classification encountered
    -- unimplemented functionality
    UUnimplemented (Panic Unimplemented)
  | -- | This @Pred@ was not annotated
    UMissingAnnotation Crucible.SimError
  | -- | A user assertion failed, but symbolically
    UFailedAssert
  | -- | Simulation timed out
    UTimeout !Text
  deriving (Show)

partitionUncertainty ::
  [Located Uncertainty] -> ([Located Crucible.SimError], [Located ()], [Located (Panic Unimplemented)], [Located Unclassified], [Located Unfixed], [Located Unfixable], [Located Text])
partitionUncertainty = go [] [] [] [] [] [] []
  where
    go ms fs ns us ufd ufa ts =
      \case
        [] -> (ms, fs, ns, us, ufd, ufa, ts)
        (Located loc (UMissingAnnotation err) : rest) ->
          let (ms', fs', ns', us', ufd', ufa', ts') = go ms fs ns us ufd ufa ts rest
           in (Located loc err : ms', fs', ns', us', ufd', ufa', ts')
        (Located loc UFailedAssert : rest) ->
          let (ms', fs', ns', us', ufd', ufa', ts') = go ms fs ns us ufd ufa ts rest
           in (ms', Located loc () : fs', ns', us', ufd', ufa', ts')
        (Located loc (UUnimplemented unin) : rest) ->
          let (ms', fs', ns', us', ufd', ufa', ts') = go ms fs ns us ufd ufa ts rest
           in (ms', fs', Located loc unin : ns', us', ufd', ufa', ts')
        (Located loc (UUnclassified unclass) : rest) ->
          let (ms', fs', ns', us', ufd', ufa', ts') = go ms fs ns us ufd ufa ts rest
           in (ms', fs', ns', Located loc unclass : us', ufd', ufa', ts')
        (Located loc (UUnfixed uf) : rest) ->
          let (ms', fs', ns', us', ufd', ufa', ts') = go ms fs ns us ufd ufa ts rest
           in (ms', fs', ns', us', Located loc uf : ufd', ufa', ts')
        (Located loc (UUnfixable uf) : rest) ->
          let (ms', fs', ns', us', ufd', ufa', ts') = go ms fs ns us ufd ufa ts rest
           in (ms', fs', ns', us', ufd', Located loc uf : ufa', ts')
        (Located loc (UTimeout fun) : rest) ->
          let (ms', fs', ns', us', ufd', ufa', ts') = go ms fs ns us ufd ufa ts rest
           in (ms', fs', ns', us', ufd', ufa', Located loc fun : ts')

-- | An error is either a true positive, a false positive due to some missing
-- preconditions, or unknown.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data Explanation m arch (argTypes :: Ctx (FullType m))
  = ExTruePositive TruePositive
  | ExDiagnosis (Diagnosis, [NewConstraint m argTypes])
  | ExUncertain Uncertainty
  | -- | Hit recursion/loop bounds
    ExExhaustedBounds !String

partitionExplanations ::
  Functor f =>
  (f (Explanation m arch types) -> Explanation m arch types) ->
  [f (Explanation m arch types)] ->
  ([f TruePositive], [f (Diagnosis, [NewConstraint m types])], [f Uncertainty], [f String])
partitionExplanations project = go [] [] [] []
  where
    go ts cs ds es [] = (ts, cs, ds, es)
    go ts cs ds es (x : xs) =
      case project x of
        ExTruePositive t ->
          let (ts', cs', ds', es') = go ts cs ds es xs
           in (fmap (const t) x : ts', cs', ds', es')
        ExDiagnosis c ->
          let (ts', cs', ds', es') = go ts cs ds es xs
           in (ts', fmap (const c) x : cs', ds', es')
        ExUncertain d ->
          let (ts', cs', ds', es') = go ts cs ds es xs
           in (ts', cs', fmap (const d) x : ds', es')
        ExExhaustedBounds e ->
          let (ts', cs', ds', es') = go ts cs ds es xs
           in (ts', cs', ds', fmap (const e) x : es')

ppUncertainty :: Uncertainty -> Text
ppUncertainty =
  \case
    UUnclassified unclass ->
      Text.unlines
        [ "Unclassified error:",
          unclass ^. doc . to (PP.layoutPretty PP.defaultLayoutOptions) . to PP.renderStrict
        ]
    UUnfixable unfix ->
      Text.unlines
        [ "Unfixable/inactionable error:",
          ppUnfixable unfix
        ]
    UUnfixed unfix ->
      Text.unlines
        [ "Fixable missing precondition, but fix not yet implemented for this error:",
          ppUnfixed unfix
        ]
    UMissingAnnotation err ->
      "(Internal issue) Missing annotation for error:\n" <> Text.pack (show err)
    UFailedAssert -> "Symbolically failing user assertion"
    UUnimplemented pan -> Text.pack (displayException pan)
    UTimeout fun -> Text.pack "Simulation timed out while executing " <> fun
