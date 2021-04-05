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
import           Control.Monad (when)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import qualified Data.BitVector.Sized as BV
import           Data.Functor.Const (Const(getConst))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Maybe (maybeToList)
import           Data.Text (Text)
import qualified Data.Text as Text

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Classes (IxedF'(ixF'), ShowF)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (foldMapFC, allFC)

import qualified What4.Concrete as What4
import qualified What4.Interface as What4
import qualified What4.Expr.Builder as What4
import qualified What4.ProgramLoc as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

import           Lang.Crucible.LLVM.Bytes (bytesToInteger)
import           Lang.Crucible.LLVM.DataLayout (DataLayout)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import qualified Lang.Crucible.LLVM.Errors.MemoryError as MemError
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MemModel.Generic (Mem, AllocInfo)
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPtr
import           Lang.Crucible.LLVM.MemType (memTypeSize)

import           UCCrux.LLVM.Classify.Poison
import           UCCrux.LLVM.Classify.Types hiding (truePositive)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, dataLayout, moduleTypes)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentNames)
import           UCCrux.LLVM.Constraints
import           UCCrux.LLVM.Cursor (ppCursor, Selector(..), SomeInSelector(SomeInSelector))
import           UCCrux.LLVM.FullType (FullType(FTPtr), MapToCrucibleType, FullTypeRepr(..), PartTypeRepr, ModuleTypes, asFullType)
import           UCCrux.LLVM.FullType.MemType (toMemType)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName)
import           UCCrux.LLVM.Setup (SymValue)
import           UCCrux.LLVM.Setup.Monad (TypedSelector(..), mallocLocation)
import           UCCrux.LLVM.Shape (Shape)
import qualified UCCrux.LLVM.Shape as Shape
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
{- ORMOLU_ENABLE -}

summarizeOp :: MemError.MemoryOp sym w -> (Maybe String, LLVMPtr.LLVMPtr sym w, Mem sym)
summarizeOp =
  \case
    MemError.MemLoadOp _storageType expl ptr mem -> (expl, ptr, mem)
    MemError.MemStoreOp _storageType expl ptr mem -> (expl, ptr, mem)
    MemError.MemStoreBytesOp expl ptr _sz mem -> (expl, ptr, mem)
    MemError.MemCopyOp (destExpl, dest) (_srcExpl, _src) _len mem -> (destExpl, dest, mem)
    MemError.MemLoadHandleOp _llvmType expl ptr mem -> (expl, ptr, mem)
    MemError.MemInvalidateOp _whatIsThisParam expl ptr _size mem -> (expl, ptr, mem)

classifyAssertion ::
  What4.IsExpr (What4.SymExpr sym) =>
  sym ->
  What4.Pred sym ->
  What4.ProgramLoc ->
  Explanation m arch argTypes
classifyAssertion _sym predicate loc =
  case What4.asConstantPred predicate of
    Just True -> panic "classifyAssertionFailure" ["Concretely true assertion failure??"]
    Just False -> ExTruePositive (LocatedTruePositive ConcretelyFailingAssert loc)
    Nothing -> ExUncertain (UFailedAssert loc)

elemsFromOffset ::
  DataLayout ->
  ModuleTypes m ->
  What4.ConcreteVal (What4.BaseBVType w) ->
  PartTypeRepr m ft ->
  Int
elemsFromOffset dl mts offset partType =
  let pointedTo = asFullType mts partType
      typeSize = bytesToInteger (memTypeSize dl (toMemType pointedTo))
   in 1 + fromIntegral (BV.asUnsigned (What4.fromConcreteBV offset) `div` typeSize)

unclass ::
  (MonadIO f, What4.IsExpr (What4.SymExpr sym)) =>
  AppContext ->
  LLVMErrors.BadBehavior sym ->
  f (Explanation m arch argTypes)
unclass appCtx badBehavior =
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

unfixed ::
  MonadIO f => AppContext -> Unfixed -> f (Explanation m arch argTypes)
unfixed appCtx tag =
  do
    liftIO $ (appCtx ^. log) Hi "Prognosis: Fixable, but the fix is not yet implemented."
    pure $ ExUncertain (UUnfixed tag)

unfixable ::
  MonadIO f => AppContext -> Unfixable -> f (Explanation m arch argTypes)
unfixable appCtx tag =
  do
    liftIO $ (appCtx ^. log) Hi "Prognosis: Don't know how to fix this."
    pure $ ExUncertain (UUnfixable tag)

notAPointer ::
  Crucible.IsSymInterface sym =>
  sym ->
  LLVMPtr.LLVMPtr sym w ->
  IO (Maybe Bool)
notAPointer sym ptr =
  What4.asConstantPred
    <$> (What4.natEq sym (LLVMPtr.llvmPointerBlock ptr) =<< What4.natLit sym 0)

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
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  sym ->
  -- | Functions skipped during execution
  Set SkipOverrideName ->
  -- | Simulation error (including source position)
  Crucible.SimError ->
  -- | Function arguments
  Crucible.RegMap sym (MapToCrucibleType arch argTypes) ->
  -- | Term annotations (origins), see comment on
  -- 'UCCrux.LLVM.Setup.Monad.resultAnnotations'.
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  -- | The arguments that were passed to the function
  Ctx.Assignment (Shape m (SymValue sym arch)) argTypes ->
  -- | Data about the error that occurred
  LLVMErrors.BadBehavior sym ->
  f (Explanation m arch argTypes)
classifyBadBehavior appCtx modCtx funCtx sym skipped simError (Crucible.RegMap _args) annotations argShapes badBehavior =
  case badBehavior of
    LLVMErrors.BBUndefinedBehavior (UB.UDivByZero _dividend (Crucible.RV divisor)) ->
      handleDivRemByZero UDivByConcreteZero divisor
    LLVMErrors.BBUndefinedBehavior (UB.SDivByZero _dividend (Crucible.RV divisor)) ->
      handleDivRemByZero SDivByConcreteZero divisor
    LLVMErrors.BBUndefinedBehavior (UB.URemByZero _dividend (Crucible.RV divisor)) ->
      handleDivRemByZero URemByConcreteZero divisor
    LLVMErrors.BBUndefinedBehavior (UB.SRemByZero _dividend (Crucible.RV divisor)) ->
      handleDivRemByZero SRemByConcreteZero divisor
    LLVMErrors.BBUndefinedBehavior (UB.WriteBadAlignment (Crucible.RV ptr) alignment) ->
      case getPtrOffsetAnn ptr of
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
                    "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                  ]
            liftIO $ (appCtx ^. log) Hi $ prescribe tag
            expectPointerType ftRepr $
              const $
                return $
                  ExMissingPreconditions
                    (tag, oneArgConstraint idx cursor (Aligned alignment))
        Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))) ->
          unfixed appCtx UnfixedRetWriteBadAlignment
        _ -> requirePossiblePointer WriteNonPointer ptr
    LLVMErrors.BBUndefinedBehavior
      (UB.ReadBadAlignment (Crucible.RV ptr) alignment) ->
        case getPtrOffsetAnn ptr of
          Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
            do
              let tag = ArgReadBadAlignment
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
              expectPointerType ftRepr $
                const $
                  return $
                    ExMissingPreconditions
                      (tag, oneArgConstraint idx cursor (Aligned alignment))
          Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))) ->
            unfixed appCtx UnfixedRetReadBadAlignment
          _ -> requirePossiblePointer ReadNonPointer ptr
    LLVMErrors.BBUndefinedBehavior
      (UB.FreeUnallocated (Crucible.RV ptr)) ->
        maybe (requirePossiblePointer FreeNonPointer ptr) pure
          =<< handleFreeUnallocated ptr
    LLVMErrors.BBUndefinedBehavior
      (UB.FreeBadOffset (Crucible.RV ptr)) ->
        case getPtrOffsetAnn ptr of
          Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
            do
              int <- liftIO $ What4.natToInteger sym (LLVMPtr.llvmPointerBlock ptr)
              case What4.asConcrete int of
                Nothing -> unclass appCtx badBehavior
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
                    expectPointerType ftRepr $
                      const $
                        return $
                          ExMissingPreconditions
                            (tag, oneArgShapeConstraint idx cursor (Allocated 1))
          Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))) ->
            unfixed appCtx UnfixedRetPtrFree
          _ -> requirePossiblePointer FreeNonPointer ptr
    LLVMErrors.BBUndefinedBehavior (UB.DoubleFree (Crucible.RV ptr)) ->
      do
        maybeEx <- handleFreeUnallocated ptr
        case maybeEx of
          Just ex ->
            -- `free` was called twice on this pointer, but because it was a
            -- fully symbolic raw bitvector, so add a constraint that it gets
            -- allocated.
            pure ex
          Nothing ->
            do
              case getPtrOffsetAnn ptr of
                Just (Some (TypedSelector _ (SomeInSelector (SelectArgument idx cursor)))) ->
                  liftIO $
                    (appCtx ^. log) Hi $
                      Text.unwords
                        [ "Double-freed pointer appeared in argument",
                          "#"
                            <> Text.pack (show (Ctx.indexVal idx)),
                          "at",
                          Text.pack (show (ppCursor (argName idx) cursor))
                        ]
                _ -> pure ()
              truePositive DoubleFree
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
                  unfixed appCtx tag
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
                      expectPointerType ftRepr $
                        \partTypeRepr ->
                          return $
                            ExMissingPreconditions
                              ( tag,
                                oneArgShapeConstraint
                                  idx
                                  cursor
                                  (Allocated (elemsFromOffset' bv partTypeRepr))
                              )
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
                      unfixable appCtx tag
          Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))) ->
            unfixed appCtx UnfixedRetPtrAddOffset
          _ -> unclass appCtx badBehavior
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
                expectPointerType ftRepr $
                  \partTypeRepr ->
                    return $
                      ExMissingPreconditions
                        ( tag,
                          oneArgShapeConstraint
                            idx
                            cursor
                            ( Initialized
                                (elemsFromOffset' concreteLen partTypeRepr)
                            )
                        )
          (Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))), _) ->
            unfixed appCtx UnfixedRetMemset
          _ -> unclass appCtx badBehavior
    LLVMErrors.BBUndefinedBehavior
      (UB.PoisonValueCreated poison) ->
        classifyPoison appCtx funCtx sym annotations poison
          >>= \case
            Nothing -> unclass appCtx badBehavior
            Just expl -> pure expl
    LLVMErrors.BBMemoryError
      ( MemError.MemoryError
          (summarizeOp -> (_expl, ptr, _mem))
          MemError.UnwritableRegion
        ) ->
        case (getPtrOffsetAnn ptr, getAnyPtrOffsetAnn ptr) of
          (Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))), _) ->
            expectPointerType ftRepr $
              const $
                case argShapes ^. ixF' idx . to (flip Shape.isAllocated cursor) of
                  Left _ -> panic "classify" ["Bad cursor into argument"]
                  Right True ->
                    -- TODO: This should probably be an error, it definitely *can*
                    -- arise from a use-after-free of an argument see
                    -- test/programs/use_after_free.c
                    unclass appCtx badBehavior
                  Right False ->
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
                      return $
                        ExMissingPreconditions
                          (tag, oneArgShapeConstraint idx cursor (Allocated 1))
          (Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))), _) ->
            unfixed appCtx UnfixedRetWriteUnmapped
          -- If the pointer expression doesn't involve the function's
          -- arguments/global variables at all, then it's just a standard null
          -- dereference or similar.
          (Nothing, []) ->
            do
              notPtr <- liftIO $ notAPointer sym ptr
              case notPtr of
                Just True -> truePositive WriteNonPointer
                _ -> unclass appCtx badBehavior
          -- If the "pointer" concretely wasn't a pointer, it's a bug.
          _ -> requirePossiblePointer WriteNonPointer ptr
    LLVMErrors.BBMemoryError
      ( MemError.MemoryError
          (summarizeOp -> (_expl, ptr, _mem))
          MemError.UnreadableRegion
        ) ->
        -- If the "pointer" concretely wasn't a pointer, it's a bug.
        requirePossiblePointer ReadNonPointer ptr
    LLVMErrors.BBMemoryError
      ( MemError.MemoryError
          (summarizeOp -> (_expl, _ptr, mem))
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
                  expectPointerType ftRepr $
                    \partTypeRepr ->
                      return $
                        ExMissingPreconditions
                          ( tag,
                            oneArgShapeConstraint
                              idx
                              cursor
                              ( Initialized
                                  ( case What4.asConcrete (LLVMPtr.llvmPointerOffset ptr) of
                                      Just off -> elemsFromOffset' off partTypeRepr
                                      Nothing -> 1 -- TODO: Maybe unclassified
                                  )
                              )
                          )
            ( Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))),
              _,
              _
              ) -> unfixed appCtx UnfixedRetReadUninitialized
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
                expectPointerType ftRepr $
                  const $
                    return $
                      ExMissingPreconditions
                        (tag, oneArgShapeConstraint idx cursor (Initialized 1))
            _ ->
              liftIO (allocInfoFromPtr mem ptr)
                >>= \case
                  Just (G.AllocInfo G.StackAlloc _sz _mut _align loc) ->
                    do
                      when (loc == mallocLocation) $
                        panic "classify" ["Setup allocated something on the stack?"]
                      -- Skipping execution of functions tends to lead to false
                      -- positives here, often such functions initialize a stack
                      -- variable.
                      if Set.null skipped
                        then truePositive (ReadUninitializedStack loc)
                        else unclass appCtx badBehavior
                  Just (G.AllocInfo G.HeapAlloc _sz _mut _align loc) ->
                    if loc == mallocLocation
                      then unclass appCtx badBehavior
                      else truePositive (ReadUninitializedHeap loc)
                  -- TODO(lb): Result in false negatives
                  -- Just (G.AllocInfo G.GlobalAlloc _sz _mut _align _loc) ->
                  --   unfixed appCtx UnfixedUninitializedGlobal
                  -- If the "pointer" concretely wasn't a pointer, it's a bug.
                  _ -> requirePossiblePointer ReadNonPointer ptr
    LLVMErrors.BBMemoryError
      ( MemError.MemoryError
          (MemError.MemLoadHandleOp _type _str ptr mem)
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
              unfixed appCtx tag
          Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))) ->
            unfixed appCtx UnfixedRetCall
          _ ->
            liftIO (allocInfoFromPtr mem ptr)
              >>= \case
                Just (G.AllocInfo G.StackAlloc _sz _mut _align loc) ->
                  do
                    when (loc == mallocLocation) $
                      panic "classify" ["Setup allocated something on the stack?"]
                    truePositive (CallNonFunctionPointer loc)
                Just (G.AllocInfo G.HeapAlloc _sz _mut _align loc) ->
                  if loc == mallocLocation
                    then unclass appCtx badBehavior
                    else truePositive (CallNonFunctionPointer loc)
                _ -> unclass appCtx badBehavior
    _ -> unclass appCtx badBehavior
  where
    expectPointerType ::
      FullTypeRepr m ft ->
      ( forall ft'.
        ft ~ 'FTPtr ft' =>
        PartTypeRepr m ft' ->
        f (Explanation m arch argTypes)
      ) ->
      f (Explanation m arch argTypes)
    expectPointerType ftRepr k =
      case ftRepr of
        FTPtrRepr partTypeRepr -> k partTypeRepr
        FTIntRepr {} ->
          unimplemented "classify" Unimplemented.CastIntegerToPointer
        FTFloatRepr {} -> truePositive FloatToPointer
        _ -> panic "classify" ["Expected pointer type"]

    getTermAnn ::
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

    elemsFromOffset' ::
      What4.ConcreteVal (What4.BaseBVType w) ->
      PartTypeRepr m ft ->
      Int
    elemsFromOffset' =
      elemsFromOffset (modCtx ^. dataLayout) (modCtx ^. moduleTypes)

    handleFreeUnallocated :: LLVMPtr.LLVMPtr sym w -> f (Maybe (Explanation m arch argTypes))
    handleFreeUnallocated ptr =
      do
        notPtr <- liftIO $ notAPointer sym ptr
        let isUnallocated =
              case notPtr of
                Just False -> False
                _ -> True
        if isUnallocated
          then case getPtrOffsetAnn ptr of
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
                        "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                      ]
                liftIO $ (appCtx ^. log) Hi $ prescribe tag
                Just
                  <$> expectPointerType
                    ftRepr
                    ( const $
                        return $
                          ExMissingPreconditions
                            (tag, oneArgShapeConstraint idx cursor (Allocated 1))
                    )
            Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))) ->
              Just <$> unfixed appCtx UnfixedRetPtrFree
            _ -> return Nothing
          else return Nothing

    -- If the divisor is concretely zero, it's a bug. If the divisor is from an
    -- argument, add a precondition that that value isn't zero.
    handleDivRemByZero ::
      TruePositive -> What4.SymBV sym w -> f (Explanation m arch argTypes)
    handleDivRemByZero truePos divisor =
      case What4.asConcrete divisor of
        Nothing ->
          case getTermAnn divisor of
            Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor)))) ->
              do
                let tag' = ArgNonZero
                liftIO $
                  (appCtx ^. log) Hi $
                    Text.unwords
                      [ "Diagnosis:",
                        diagnose tag',
                        "#" <> Text.pack (show (Ctx.indexVal idx)),
                        "at",
                        Text.pack (show (ppCursor (argName idx) cursor))
                      ]
                liftIO $ (appCtx ^. log) Hi $ prescribe tag'
                case ftRepr of
                  FTIntRepr w ->
                    return $
                      ExMissingPreconditions
                        ( tag',
                          oneArgConstraint idx cursor (BVCmp L.Ine w (BV.mkBV w 0))
                        )
                  _ -> panic "classify" ["Expected integer type"]
            Just (Some (TypedSelector _ (SomeInSelector SelectReturn {}))) ->
              unfixed appCtx UnfixedRetDivRemByZero
            _ -> unclass appCtx badBehavior
        Just _ -> truePositive truePos

    argName :: Ctx.Index argTypes tp -> String
    argName idx = funCtx ^. argumentNames . ixF' idx . to getConst . to (maybe "<top>" Text.unpack)

    oneArgConstraint idx cursor constraint =
      [NewConstraint (SomeInSelector (SelectArgument idx cursor)) constraint]

    oneArgShapeConstraint idx cursor shapeConstraint =
      [NewShapeConstraint (SomeInSelector (SelectArgument idx cursor)) shapeConstraint]

    allocInfoFromPtr :: Mem sym -> LLVMPtr.LLVMPtr sym w -> IO (Maybe (AllocInfo sym))
    allocInfoFromPtr mem ptr =
      do
        int <- liftIO $ What4.natToInteger sym (LLVMPtr.llvmPointerBlock ptr)
        pure $
          do
            concreteInt <- What4.asConcrete int
            G.possibleAllocInfo
              (fromIntegral (What4.fromConcreteInteger concreteInt))
              (G.memAllocs mem)

    truePositive :: TruePositive -> f (Explanation m arch argTypes)
    truePositive pos =
      do
        liftIO $
          (appCtx ^. log) Hi $
            Text.unwords ["Diagnosis:", ppTruePositive pos]
        return $
          ExTruePositive
            ( LocatedTruePositive
                pos
                (Crucible.simErrorLoc simError)
            )

    -- Unfortunately, this check is pretty coarse. We can conclude that the
    -- given pointer concretely isn't a pointer only if *all* of the following
    -- are true:
    --
    -- (1) It has a concrete, zero block number
    -- (2) There are no remaining unallocated pointers in the function's
    --     arguments
    -- (3) No functions were unsoundly skipped during execution
    --
    -- The second and third conditions are necessary because unallocated
    -- pointers in the function arguments/return values have a concretely zero block number,
    -- but they can be combined with other program data in arbitrarily complex
    -- ways that cause them to lose their annotations.
    --
    -- A possible fix would be to mux input pointers with a fresh, allocated
    -- pointer (so that their block number is not concretely zero), but this
    -- causes all kinds of other breakage.
    --
    -- To see the problem in action, replace the predicate with "const True"
    -- below and you should see the test free_with_offset.c start to fail.
    requirePossiblePointer ::
      TruePositive ->
      LLVMPtr.LLVMPtr sym w ->
      f (Explanation m arch argTypes)
    requirePossiblePointer pos ptr =
      do
        notPtr <- liftIO $ notAPointer sym ptr
        case (notPtr, allFC (not . Shape.isAnyUnallocated) argShapes, Set.null skipped) of
          (Just True, True, True) -> truePositive pos
          _ -> unclass appCtx badBehavior
