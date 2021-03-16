{-
Module       : UCCrux.LLVM.Classify
Description  : Classify errors as true positives or due to missing preconditions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module UCCrux.LLVM.Classify
  ( Explanation (..),
    partitionExplanations,
    TruePositive (..),
    TruePositiveTag (..),
    truePositiveTag,
    MissingPreconditionTag (..),
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
    classifyAssertion,
    classifyBadBehavior,
    diagnose,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Exception (displayException)
import           Control.Lens (Lens', lens, to, (^.))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.BitVector.Sized (asUnsigned)
import           Data.Functor.Const (Const(getConst))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (maybeToList)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))
import           Data.Void (Void)
import           Panic (Panic)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import           Data.Parameterized.Classes (IxedF'(ixF'), ShowF)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (foldMapFC)

import qualified What4.Concrete as What4
import qualified What4.Interface as What4
import qualified What4.Expr.Builder as What4
import qualified What4.ProgramLoc as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

import           Lang.Crucible.LLVM.Bytes (bytesToInteger)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import qualified Lang.Crucible.LLVM.Errors.MemoryError as MemError
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPtr
import           Lang.Crucible.LLVM.MemType (memTypeSize)

import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, dataLayout)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentNames, moduleTypes)
import           UCCrux.LLVM.Constraints
import           UCCrux.LLVM.Cursor (Cursor, ppCursor, Selector(..), SomeInSelector(SomeInSelector))
import           UCCrux.LLVM.FullType (MapToCrucibleType, IsPtrRepr(..), isPtrRepr, FullTypeRepr(FTPtrRepr), PartTypeRepr)
import           UCCrux.LLVM.FullType.MemType (toMemType, asFullType)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.Setup.Monad (TypedSelector(..))
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented)
{- ORMOLU_ENABLE -}

data TruePositiveTag
  = TagConcretelyFailingAssert
  | TagDoubleFree
  deriving (Eq, Ord)

data TruePositive
  = ConcretelyFailingAssert !What4.ProgramLoc
  | DoubleFree

truePositiveTag :: TruePositive -> TruePositiveTag
truePositiveTag =
  \case
    ConcretelyFailingAssert {} -> TagConcretelyFailingAssert
    DoubleFree {} -> TagDoubleFree

ppTruePositiveTag :: TruePositiveTag -> Text
ppTruePositiveTag =
  \case
    TagConcretelyFailingAssert -> "Concretely failing user assertion"
    TagDoubleFree -> "Double free"

-- | All of the preconditions that we can deduce. We know how to detect and fix
-- these issues.
data MissingPreconditionTag
  = ArgWriteBadAlignment
  | ArgReadBadAlignment
  | ArgFreeUnallocated
  | ArgFreeBadOffset
  | ArgWriteUnmapped
  | ArgReadUninitialized
  | ArgReadUninitializedOffset
  | ArgPointerConstOffset
  | ArgMemsetTooSmall
  deriving (Eq, Ord)

diagnose :: MissingPreconditionTag -> Text
diagnose =
  \case
    ArgWriteBadAlignment -> "Write to a pointer with insufficient alignment in argument"
    ArgReadBadAlignment -> "Read from a pointer with insufficient alignment in argument"
    ArgFreeUnallocated -> "`free` called on an unallocated pointer in argument"
    ArgFreeBadOffset -> "`free` called on pointer with nonzero offset in argument"
    ArgWriteUnmapped -> "Write to an unmapped pointer in argument"
    ArgReadUninitialized -> "Read from an uninitialized pointer in argument"
    ArgReadUninitializedOffset -> "Read from an uninitialized pointer calculated from a pointer in argument"
    ArgPointerConstOffset -> "Addition of a constant offset to a pointer in argument"
    ArgMemsetTooSmall -> "`memset` called on pointer to too-small allocation in argument"

prescribe :: MissingPreconditionTag -> Text
prescribe =
  ("Prescription: Add a precondition that " <>)
    . \case
      ArgWriteBadAlignment -> "the pointer is sufficiently aligned."
      ArgReadBadAlignment -> "the pointer is sufficiently aligned."
      ArgFreeUnallocated -> "the pointer points to initialized memory."
      ArgFreeBadOffset -> "the pointer points to initialized memory."
      ArgWriteUnmapped -> "the pointer points to allocated memory."
      ArgReadUninitialized -> "the pointer points to initialized memory."
      ArgReadUninitializedOffset -> "the pointer points to initialized memory."
      ArgPointerConstOffset -> "the allocation is at least that size."
      ArgMemsetTooSmall -> "the allocation is at least that size."

-- | There was an error and we know roughly what sort it was, but we still can't
-- do anything about it.
data Unfixable
  = AddSymbolicOffsetToArgPointer
  deriving (Eq, Ord, Show)

ppUnfixable :: Unfixable -> Text
ppUnfixable =
  \case
    AddSymbolicOffsetToArgPointer -> "Addition of a symbolic offset to pointer in argument"

-- | We know how we *could* fix this in theory, but haven't implemented it yet.
data Unfixed
  = UnfixedArgPtrOffsetArg
  | UnfixedFunctionPtrInArg
  deriving (Eq, Ord, Show)

ppUnfixed :: Unfixed -> Text
ppUnfixed =
  \case
    UnfixedArgPtrOffsetArg -> "Addition of an offset from argument to a pointer in argument"
    UnfixedFunctionPtrInArg -> "Called function pointer in argument"

-- | We don't (yet) know what to do about this error
data Unclassified
  = UnclassifiedUndefinedBehavior (Doc Void) (Some UB.UndefinedBehavior)
  | UnclassifiedMemoryError (Doc Void)

doc :: Lens' Unclassified (Doc Void)
doc =
  lens
    ( \case
        UnclassifiedUndefinedBehavior doc' _ -> doc'
        UnclassifiedMemoryError doc' -> doc'
    )
    ( \s doc' ->
        case s of
          UnclassifiedUndefinedBehavior _ val ->
            UnclassifiedUndefinedBehavior doc' val
          UnclassifiedMemoryError _ ->
            UnclassifiedMemoryError doc'
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
    UFailedAssert !What4.ProgramLoc
  deriving (Show)

partitionUncertainty ::
  [Uncertainty] -> ([Crucible.SimError], [What4.ProgramLoc], [Panic Unimplemented], [Unclassified], [Unfixed], [Unfixable])
partitionUncertainty = go [] [] [] [] [] []
  where
    go ms fs ns us ufd ufa =
      \case
        [] -> (ms, fs, ns, us, ufd, ufa)
        (UMissingAnnotation err : rest) ->
          let (ms', fs', ns', us', ufd', ufa') = go ms fs ns us ufd ufa rest
           in (err : ms', fs', ns', us', ufd', ufa')
        (UFailedAssert loc : rest) ->
          let (ms', fs', ns', us', ufd', ufa') = go ms fs ns us ufd ufa rest
           in (ms', loc : fs', ns', us', ufd', ufa')
        (UUnimplemented n : rest) ->
          let (ms', fs', ns', us', ufd', ufa') = go ms fs ns us ufd ufa rest
           in (ms', fs', n : ns', us', ufd', ufa')
        (UUnclassified unclass : rest) ->
          let (ms', fs', ns', us', ufd', ufa') = go ms fs ns us ufd ufa rest
           in (ms', fs', ns', unclass : us', ufd', ufa')
        (UUnfixed uf : rest) ->
          let (ms', fs', ns', us', ufd', ufa') = go ms fs ns us ufd ufa rest
           in (ms', fs', ns', us', uf : ufd', ufa')
        (UUnfixable uf : rest) ->
          let (ms', fs', ns', us', ufd', ufa') = go ms fs ns us ufd ufa rest
           in (ms', fs', ns', us', ufd', uf : ufa')

-- | An error is either a true positive, a false positive due to some missing
-- preconditions, or unknown.
data Explanation m arch argTypes
  = ExTruePositive TruePositive
  | ExMissingPreconditions (MissingPreconditionTag, [NewConstraint m argTypes])
  | ExUncertain Uncertainty
  | -- | Hit recursion/loop bounds
    ExExhaustedBounds !String

partitionExplanations ::
  [Explanation m arch types] ->
  ([TruePositive], [(MissingPreconditionTag, [NewConstraint m types])], [Uncertainty], [String])
partitionExplanations = go [] [] [] []
  where
    go ts cs ds es =
      \case
        [] -> (ts, cs, ds, es)
        (ExTruePositive t : xs) ->
          let (ts', cs', ds', es') = go ts cs ds es xs
           in (t : ts', cs', ds', es')
        (ExMissingPreconditions c : xs) ->
          let (ts', cs', ds', es') = go ts cs ds es xs
           in (ts', c : cs', ds', es')
        (ExUncertain d : xs) ->
          let (ts', cs', ds', es') = go ts cs ds es xs
           in (ts', cs', d : ds', es')
        (ExExhaustedBounds e : xs) ->
          let (ts', cs', ds', es') = go ts cs ds es xs
           in (ts', cs', ds', e : es')

ppTruePositive :: TruePositive -> Text
ppTruePositive =
  \case
    ConcretelyFailingAssert loc ->
      "Concretely failing call to assert() at " <> Text.pack (show loc)
    DoubleFree -> "Pointer freed twice"

ppUncertainty :: Uncertainty -> Text
ppUncertainty =
  \case
    UUnclassified unclass ->
      "Unclassified error:\n"
        <> (unclass ^. doc . to (PP.layoutPretty PP.defaultLayoutOptions) . to PP.renderStrict)
    UUnfixable unfix -> "Unfixable/inactionable error:\n" <> ppUnfixable unfix
    UUnfixed unfix ->
      "Fixable, but fix not yet implemented for this error:\n" <> ppUnfixed unfix
    UMissingAnnotation err ->
      "(Internal issue) Missing annotation for error:\n" <> Text.pack (show err)
    UFailedAssert loc ->
      "Symbolically failing user assertion at " <> Text.pack (show loc)
    UUnimplemented pan -> Text.pack (displayException pan)

summarizeOp :: MemError.MemoryOp sym w -> (Maybe String, LLVMPtr.LLVMPtr sym w)
summarizeOp =
  \case
    MemError.MemLoadOp _storageType expl ptr _mem -> (expl, ptr)
    MemError.MemStoreOp _storageType expl ptr _mem -> (expl, ptr)
    MemError.MemStoreBytesOp expl ptr _sz _mem -> (expl, ptr)
    MemError.MemCopyOp (destExpl, dest) (_srcExpl, _src) _len _mem -> (destExpl, dest)
    MemError.MemLoadHandleOp _llvmType expl ptr _mem -> (expl, ptr)
    MemError.MemInvalidateOp _whatIsThisParam expl ptr _size _mem -> (expl, ptr)

classifyAssertion ::
  What4.IsExpr (What4.SymExpr sym) =>
  sym ->
  What4.Pred sym ->
  What4.ProgramLoc ->
  Explanation m arch argTypes
classifyAssertion _sym predicate loc =
  case What4.asConstantPred predicate of
    Just True -> panic "classifyAssertionFailure" ["Concretely true assertion failure??"]
    Just False -> ExTruePositive (ConcretelyFailingAssert loc)
    Nothing -> ExUncertain (UFailedAssert loc)

-- | Take an error that occurred during symbolic execution, classify it as a
-- true or false positive. If it is a false positive, deduce further
-- preconditions.
classifyBadBehavior ::
  forall f m sym arch argTypes t st fs.
  ( Crucible.IsSymInterface sym,
    sym ~ What4.ExprBuilder t st fs, -- needed for asApp
    MonadIO f,
    ShowF (What4.SymAnnotation sym)
  ) =>
  AppContext ->
  ModuleContext arch ->
  FunctionContext m arch argTypes ->
  sym ->
  -- | Function arguments
  Crucible.RegMap sym (MapToCrucibleType arch argTypes) ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  -- | Data about the error that occurred
  LLVMErrors.BadBehavior sym ->
  f (Explanation m arch argTypes)
classifyBadBehavior appCtx modCtx funCtx sym (Crucible.RegMap _args) annotations badBehavior =
  liftIO $
    (appCtx ^. log) Hi ("Explaining error: " <> Text.pack (show (LLVMErrors.explainBB badBehavior)))
      >> let getTermAnn ::
               What4.SymExpr sym tp ->
               Maybe (Some (TypedSelector m arch argTypes))
             getTermAnn expr =
               flip Map.lookup annotations . Some =<< What4.getAnnotation sym expr
             getPtrOffsetAnn ::
               LLVMPtr.LLVMPtr sym w ->
               Maybe (Some (TypedSelector m arch argTypes))
             getPtrOffsetAnn ptr = getTermAnn (LLVMPtr.llvmPointerOffset ptr)
             getPtrBlockAnn ::
               LLVMPtr.LLVMPtr sym w ->
               IO (Maybe (Some (TypedSelector m arch argTypes)))
             getPtrBlockAnn ptr =
               do
                 int <- What4.natToInteger sym (LLVMPtr.llvmPointerBlock ptr)
                 pure $ getTermAnn int
             getAnyPtrOffsetAnn ::
               LLVMPtr.LLVMPtr sym w ->
               [Some (TypedSelector m arch argTypes)]
             getAnyPtrOffsetAnn ptr =
               let subAnns =
                     case What4.asApp (LLVMPtr.llvmPointerOffset ptr) of
                       Nothing -> []
                       Just app -> foldMapFC (maybeToList . getTermAnn) app
                in case getPtrOffsetAnn ptr of
                     Just ann -> ann : subAnns
                     Nothing -> subAnns

             argName :: Ctx.Index argTypes tp -> String
             argName idx = funCtx ^. argumentNames . ixF' idx . to getConst . to (maybe "<top>" Text.unpack)

             elemsFromOffset ::
               What4.ConcreteVal (What4.BaseBVType w) ->
               PartTypeRepr m ft ->
               Int
             elemsFromOffset offset partType =
               let dl = modCtx ^. dataLayout
                   pointedTo = asFullType (funCtx ^. moduleTypes) partType
                   typeSize = bytesToInteger (memTypeSize dl (toMemType pointedTo))
                in 1 + fromIntegral (asUnsigned (What4.fromConcreteBV offset) `div` fromIntegral typeSize)

             oneArgConstraint :: Ctx.Index argTypes inTy -> Cursor m inTy atTy -> Constraint m atTy -> [NewConstraint m argTypes]
             oneArgConstraint idx cursor constraint =
               [NewConstraint (SomeInSelector (SelectArgument idx cursor)) constraint]

             oneArgShapeConstraint :: Ctx.Index argTypes inTy -> Cursor m inTy atTy -> ShapeConstraint m atTy -> [NewConstraint m argTypes]
             oneArgShapeConstraint idx cursor shapeConstraint =
               [NewShapeConstraint (SomeInSelector (SelectArgument idx cursor)) shapeConstraint]

             unclass =
               do
                 liftIO $ (appCtx ^. log) Hi ("Couldn't classify error." :: Text)
                 pure $
                   ExUncertain $
                     UUnclassified $
                       case badBehavior of
                         LLVMErrors.BBUndefinedBehavior ub ->
                           UnclassifiedUndefinedBehavior (UB.explain ub) (Some ub)
                         LLVMErrors.BBMemoryError memoryError ->
                           UnclassifiedMemoryError (MemError.explain memoryError)

             unfixed :: Unfixed -> IO (Explanation m arch argTypes)
             unfixed tag =
               do
                 (appCtx ^. log) Hi "Prognosis: Fixable, but the fix is not yet implemented."
                 pure $ ExUncertain (UUnfixed tag)

             unfixable :: Unfixable -> IO (Explanation m arch argTypes)
             unfixable tag =
               do
                 (appCtx ^. log) Hi "Prognosis: Don't know how to fix this."
                 pure $ ExUncertain (UUnfixable tag)
          in case badBehavior of
               LLVMErrors.BBUndefinedBehavior
                 (UB.WriteBadAlignment ptr alignment) ->
                   case getPtrOffsetAnn (Crucible.unRV ptr) of
                     Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
                       do
                         let tag = ArgWriteBadAlignment
                         liftIO $
                           (appCtx ^. log) Hi $
                             Text.unwords
                               [ "Diagnosis: ",
                                 diagnose tag,
                                 "#" <> Text.pack (show (Ctx.indexVal idx)),
                                 "at",
                                 Text.pack (show (ppCursor (argName idx) cursor)),
                                 "(" <> Text.pack (show (LLVMPtr.ppPtr (Crucible.unRV ptr))) <> ")"
                               ]
                         liftIO $ (appCtx ^. log) Hi $ prescribe tag
                         case isPtrRepr ftRepr of
                           Nothing -> panic "classify" ["Expected pointer type"]
                           Just (IsPtrRepr Refl) ->
                             return $
                               ExMissingPreconditions $
                                 (tag, oneArgConstraint idx cursor (Aligned alignment))
                     _ -> unclass
               LLVMErrors.BBUndefinedBehavior
                 (UB.ReadBadAlignment ptr alignment) ->
                   case getPtrOffsetAnn (Crucible.unRV ptr) of
                     Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
                       do
                         let tag = ArgWriteBadAlignment
                         liftIO $
                           (appCtx ^. log) Hi $
                             Text.unwords
                               [ "Diagnosis:",
                                 diagnose tag,
                                 "#" <> Text.pack (show (Ctx.indexVal idx)),
                                 "at",
                                 Text.pack (show (ppCursor (argName idx) cursor)),
                                 "(" <> Text.pack (show (LLVMPtr.ppPtr (Crucible.unRV ptr))) <> ")"
                               ]
                         liftIO $ (appCtx ^. log) Hi $ prescribe tag
                         case isPtrRepr ftRepr of
                           Nothing -> panic "classify" ["Expected pointer type"]
                           Just (IsPtrRepr Refl) ->
                             return $
                               ExMissingPreconditions
                                 (tag, oneArgConstraint idx cursor (Aligned alignment))
                     _ -> unclass
               LLVMErrors.BBUndefinedBehavior
                 (UB.FreeUnallocated ptr) ->
                   case getPtrOffsetAnn (Crucible.unRV ptr) of
                     Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
                       do
                         let tag = ArgFreeUnallocated
                         liftIO $
                           (appCtx ^. log) Hi $
                             Text.unwords
                               [ "Diagnosis:",
                                 diagnose tag,
                                 "#" <> Text.pack (show (Ctx.indexVal idx)),
                                 "at",
                                 Text.pack (show (ppCursor (argName idx) cursor)),
                                 "(" <> Text.pack (show (LLVMPtr.ppPtr (Crucible.unRV ptr))) <> ")"
                               ]
                         liftIO $ (appCtx ^. log) Hi $ prescribe tag
                         case isPtrRepr ftRepr of
                           Nothing -> panic "classify" ["Expected pointer type"]
                           Just (IsPtrRepr Refl) ->
                             return $
                               ExMissingPreconditions
                                 (tag, oneArgShapeConstraint idx cursor (Allocated 1))
                     _ -> unclass
               LLVMErrors.BBUndefinedBehavior
                 (UB.FreeBadOffset (Crucible.RV ptr)) ->
                   case getPtrOffsetAnn ptr of
                     Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
                       -- At the moment, we only handle the case where the pointer is
                       -- unallocated.
                       do
                         int <- liftIO $ What4.natToInteger sym (LLVMPtr.llvmPointerBlock ptr)
                         case What4.asConcrete int of
                           Nothing -> unclass
                           Just _ ->
                             do
                               let tag = ArgFreeBadOffset
                               liftIO $
                                 (appCtx ^. log) Hi $
                                   Text.unwords
                                     [ "Diagnosis: ",
                                       diagnose tag,
                                       "#" <> Text.pack (show (Ctx.indexVal idx)),
                                       "at",
                                       Text.pack (show (ppCursor (argName idx) cursor)),
                                       "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                                     ]
                               liftIO $ (appCtx ^. log) Hi $ prescribe tag
                               case isPtrRepr ftRepr of
                                 Nothing -> panic "classify" ["Expected pointer type"]
                                 Just (IsPtrRepr Refl) ->
                                   return $
                                     ExMissingPreconditions
                                       (tag, oneArgShapeConstraint idx cursor (Allocated 1))
                     _ -> unclass
               LLVMErrors.BBUndefinedBehavior
                 (UB.DoubleFree _) ->
                   do
                     let tag = TagDoubleFree
                     liftIO $
                       (appCtx ^. log) Hi $
                         Text.unwords ["Diagnosis:", ppTruePositiveTag tag]
                     return $ ExTruePositive DoubleFree
               LLVMErrors.BBUndefinedBehavior
                 (UB.PtrAddOffsetOutOfBounds (Crucible.RV ptr) (Crucible.RV offset)) ->
                   case getPtrOffsetAnn ptr of
                     Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
                       case getTermAnn offset of
                         Just (Some (TypedSelector _ (SomeInSelector (SelectArgument _ _)))) ->
                           do
                             let tag = UnfixedArgPtrOffsetArg
                             liftIO $
                               (appCtx ^. log) Hi $
                                 Text.unwords
                                   [ "Diagnosis: ",
                                     ppUnfixed tag,
                                     "#" <> Text.pack (show (Ctx.indexVal idx)),
                                     "at",
                                     Text.pack (show (ppCursor (argName idx) cursor)),
                                     "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                                   ]
                             unfixed tag
                         _ ->
                           case What4.asConcrete offset of
                             Just bv ->
                               do
                                 let tag = ArgPointerConstOffset
                                 liftIO $
                                   (appCtx ^. log) Hi $
                                     Text.unwords
                                       [ "Diagnosis: ",
                                         diagnose tag,
                                         "#" <> Text.pack (show (Ctx.indexVal idx)),
                                         "at",
                                         Text.pack (show (ppCursor (argName idx) cursor)),
                                         "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                                       ]
                                 liftIO $ (appCtx ^. log) Hi $ prescribe tag
                                 case ftRepr of
                                   FTPtrRepr partType ->
                                     return $
                                       ExMissingPreconditions
                                         ( tag,
                                           oneArgShapeConstraint
                                             idx
                                             cursor
                                             (Allocated (fromIntegral (elemsFromOffset bv partType)))
                                         )
                                   _ -> panic "classify" ["Expected pointer type"]
                             Nothing ->
                               do
                                 let tag = AddSymbolicOffsetToArgPointer
                                 liftIO $
                                   (appCtx ^. log) Hi $
                                     Text.unwords
                                       [ "Diagnosis:",
                                         ppUnfixable tag,
                                         "#" <> Text.pack (show (Ctx.indexVal idx)),
                                         "at",
                                         Text.pack (show (ppCursor (argName idx) cursor)),
                                         "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                                       ]
                                 unfixable tag
                     _ -> unclass
               LLVMErrors.BBUndefinedBehavior
                 (UB.MemsetInvalidRegion (Crucible.RV ptr) _fillByte (Crucible.RV len)) ->
                   case (getPtrOffsetAnn ptr, What4.asConcrete len) of
                     ( Just
                         ( Some
                             ( TypedSelector
                                 ftRepr
                                 (SomeInSelector (SelectArgument idx cursor))
                               )
                           ),
                       Just concreteLen
                       ) ->
                         do
                           let tag = ArgMemsetTooSmall
                           liftIO $
                             (appCtx ^. log) Hi $
                               Text.unwords
                                 [ "Diagnosis:",
                                   diagnose tag,
                                   "#" <> Text.pack (show (Ctx.indexVal idx)),
                                   "at",
                                   Text.pack (show (ppCursor (argName idx) cursor)),
                                   "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                                 ]
                           case ftRepr of
                             FTPtrRepr partTypeRepr ->
                               return $
                                 ExMissingPreconditions
                                   ( tag,
                                     oneArgShapeConstraint
                                       idx
                                       cursor
                                       ( Initialized
                                           (elemsFromOffset concreteLen partTypeRepr)
                                       )
                                   )
                             _ -> panic "classify" ["Expected pointer type"]
                     _ -> unclass
               LLVMErrors.BBMemoryError
                 ( MemError.MemoryError
                     (summarizeOp -> (_expl, ptr))
                     MemError.UnwritableRegion
                   ) ->
                   case getPtrOffsetAnn ptr of
                     Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
                       -- TODO: Double check that it really was unmapped not read-only
                       -- or something?
                       do
                         int <- liftIO $ What4.natToInteger sym (LLVMPtr.llvmPointerBlock ptr)
                         let tag = ArgWriteUnmapped
                         liftIO $
                           (appCtx ^. log) Hi $
                             Text.unwords
                               [ "Diagnosis:",
                                 diagnose tag,
                                 "#" <> Text.pack (show (Ctx.indexVal idx)),
                                 "at",
                                 Text.pack (show (ppCursor (argName idx) cursor)),
                                 "(allocation: " <> Text.pack (show (What4.printSymExpr int)) <> ")",
                                 "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                               ]
                         liftIO $ (appCtx ^. log) Hi $ prescribe tag
                         case isPtrRepr ftRepr of
                           Nothing -> panic "classify" ["Expected pointer type"]
                           Just (IsPtrRepr Refl) ->
                             return $
                               ExMissingPreconditions
                                 (tag, oneArgShapeConstraint idx cursor (Allocated 1))
                     -- TODO(lb): Something about globals, probably?
                     _ -> unclass
               LLVMErrors.BBMemoryError
                 ( MemError.MemoryError
                     _op
                     (MemError.NoSatisfyingWrite _storageType ptr)
                   ) ->
                   do
                     blockAnn <- liftIO $ getPtrBlockAnn ptr
                     case (blockAnn, getPtrOffsetAnn ptr, getAnyPtrOffsetAnn ptr) of
                       ( Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))),
                         _,
                         _
                         ) ->
                           do
                             let tag = ArgReadUninitialized
                             liftIO $
                               (appCtx ^. log) Hi $
                                 Text.unwords
                                   [ "Diagnosis:",
                                     diagnose tag,
                                     "#" <> Text.pack (show (Ctx.indexVal idx)),
                                     "at",
                                     Text.pack (show (ppCursor (argName idx) cursor)),
                                     "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                                   ]
                             liftIO $ (appCtx ^. log) Hi $ prescribe tag
                             case ftRepr of
                               FTPtrRepr partTypeRepr ->
                                 return $
                                   ExMissingPreconditions
                                     ( tag,
                                       oneArgShapeConstraint
                                         idx
                                         cursor
                                         ( Initialized
                                             ( case What4.asConcrete (LLVMPtr.llvmPointerOffset ptr) of
                                                 Just off -> elemsFromOffset off partTypeRepr
                                                 Nothing -> 1 -- TODO: Maybe unclassified
                                             )
                                         )
                                     )
                               _ -> panic "classify" ["Expected pointer type"]
                       (Nothing, _, [Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))]) ->
                         do
                           let tag = ArgReadUninitializedOffset
                           liftIO $
                             (appCtx ^. log) Hi $
                               Text.unwords
                                 [ "Diagnosis:",
                                   diagnose tag,
                                   "#" <> Text.pack (show (Ctx.indexVal idx)),
                                   "at",
                                   Text.pack (show (ppCursor (argName idx) cursor)),
                                   "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                                 ]
                           liftIO $ (appCtx ^. log) Hi $ prescribe tag
                           case isPtrRepr ftRepr of
                             Nothing -> panic "classify" ["Expected pointer type"]
                             Just (IsPtrRepr Refl) ->
                               return $
                                 ExMissingPreconditions
                                   (tag, oneArgShapeConstraint idx cursor (Initialized 1))
                       _ -> unclass
               LLVMErrors.BBMemoryError
                 ( MemError.MemoryError
                     (MemError.MemLoadHandleOp _type _str ptr _)
                     (MemError.BadFunctionPointer _msg)
                   ) ->
                   case getPtrOffsetAnn ptr of
                     Just (Some (TypedSelector _ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
                       do
                         let tag = UnfixedFunctionPtrInArg
                         liftIO $
                           (appCtx ^. log) Hi $
                             Text.unwords
                               [ "Diagnosis: ",
                                 ppUnfixed tag,
                                 "#" <> Text.pack (show (Ctx.indexVal idx)),
                                 "at",
                                 Text.pack (show (ppCursor (argName idx) cursor)),
                                 "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                               ]
                         unfixed tag
                     _ -> unclass
               _ -> unclass
