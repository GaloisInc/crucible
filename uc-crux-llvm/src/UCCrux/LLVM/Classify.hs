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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module UCCrux.LLVM.Classify
  ( classifyAssertion,
    classifyBadBehavior,
    diagnose,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens (to, (^.))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import           Data.Functor.Const (Const(getConst))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (maybeToList)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Classes (IxedF'(ixF'), ShowF)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (NatRepr, type (<=))
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
import qualified Lang.Crucible.LLVM.Errors.Poison as Poison
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPtr
import           Lang.Crucible.LLVM.MemType (memTypeSize)

import           UCCrux.LLVM.Classify.Types
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, dataLayout)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentNames, moduleTypes)
import           UCCrux.LLVM.Constraints
import           UCCrux.LLVM.Cursor (Cursor, ppCursor, Selector(..), SomeInSelector(SomeInSelector))
import           UCCrux.LLVM.FullType (FullType(FTInt), MapToCrucibleType, IsPtrRepr(..), isPtrRepr, FullTypeRepr(..), PartTypeRepr)
import           UCCrux.LLVM.FullType.MemType (toMemType, asFullType)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.Setup.Monad (TypedSelector(..))
import           UCCrux.LLVM.Errors.Panic (panic)
{- ORMOLU_ENABLE -}

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
                in 1 + fromIntegral (BV.asUnsigned (What4.fromConcreteBV offset) `div` fromIntegral typeSize)

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

             handlePoisonArith ::
               forall g.
               MonadIO g =>
               Poison.Poison (Crucible.RegValue' sym) ->
               g (Explanation m arch argTypes)
             handlePoisonArith =
               let annotationAndValue ::
                     forall w.
                     What4.SymBV sym w ->
                     What4.SymBV sym w ->
                     Maybe (Some (TypedSelector m arch argTypes), BV w)
                   annotationAndValue op1 op2 =
                     case (getTermAnn op1, What4.asConcrete op1, getTermAnn op2, What4.asConcrete op2) of
                       (Just ann, Nothing, Nothing, Just val) ->
                         Just (ann, What4.fromConcreteBV val)
                       (Nothing, Just val, Just ann, _) ->
                         Just (ann, What4.fromConcreteBV val)
                       _ -> Nothing

                   handleBVOp ::
                     MissingPreconditionTag ->
                     What4.SymBV sym w ->
                     What4.SymBV sym w ->
                     ( forall w'.
                       1 <= w' =>
                       NatRepr w' ->
                       BV w' ->
                       Constraint m ('FTInt w')
                     ) ->
                     g (Explanation m arch argTypes)
                   handleBVOp tag op1 op2 constraint =
                     -- NOTE(lb): The trunc' operation here *should* be a
                     -- no-op, but since the Poison constructors don't have a
                     -- NatRepr, we can't check. That's fixable, but not high
                     -- priority since we'd just panic anyway if the widths
                     -- didn't match.
                     case annotationAndValue op1 op2 of
                       Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor))), concreteSummand) ->
                         do
                           liftIO $
                             (appCtx ^. log) Hi $
                               Text.unwords
                                 [ "Diagnosis:",
                                   diagnose tag,
                                   "#" <> Text.pack (show (Ctx.indexVal idx)),
                                   "at",
                                   Text.pack (show (ppCursor (argName idx) cursor))
                                 ]
                           liftIO $ (appCtx ^. log) Hi $ prescribe tag
                           case ftRepr of
                             FTIntRepr w ->
                               return $
                                 ExMissingPreconditions
                                   ( tag,
                                     oneArgConstraint
                                       idx
                                       cursor
                                       (constraint w (BV.trunc' w concreteSummand))
                                   )
                             _ -> liftIO $ unclass
                       _ -> liftIO $ unclass
                in \case
                     Poison.AddNoSignedWrap (Crucible.RV op1) (Crucible.RV op2) ->
                       handleBVOp
                         ArgAddSignedWrap
                         op1
                         op2
                         ( \w concreteSummand ->
                             BVCmp L.Islt (BV.sub w (BV.maxSigned w) concreteSummand)
                         )
                     Poison.SubNoSignedWrap (Crucible.RV op1) (Crucible.RV op2) ->
                       handleBVOp
                         ArgSubSignedWrap
                         op1
                         op2
                         ( \w concreteSummand ->
                             BVCmp L.Isgt (BV.add w (BV.minSigned w) concreteSummand)
                         )
                     _ -> liftIO $ unclass
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
                                           (elemsFromOffset concreteLen partTypeRepr)
                                       )
                                   )
                             _ -> panic "classify" ["Expected pointer type"]
                     _ -> unclass
               LLVMErrors.BBUndefinedBehavior
                 (UB.PoisonValueCreated poison@(Poison.AddNoSignedWrap {})) ->
                   liftIO $ handlePoisonArith poison
               LLVMErrors.BBUndefinedBehavior
                 (UB.PoisonValueCreated poison@(Poison.SubNoSignedWrap {})) ->
                   liftIO $ handlePoisonArith poison
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
