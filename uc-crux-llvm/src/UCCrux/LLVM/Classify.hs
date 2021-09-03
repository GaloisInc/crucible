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
import           Control.Applicative ((<|>))
import qualified Data.BitVector.Sized as BV
import           Data.Functor.Const (Const(getConst))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Maybe (maybeToList)
import qualified Data.Text as Text
import           Numeric.Natural (Natural)

import qualified Text.LLVM.AST as L

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
import           Lang.Crucible.LLVM.DataLayout (DataLayout)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import qualified Lang.Crucible.LLVM.Errors.MemoryError as MemError
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemModel.Generic (Mem, AllocInfo)
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPtr
import           Lang.Crucible.LLVM.MemType (memTypeSize)

import           UCCrux.LLVM.Classify.Poison
import           UCCrux.LLVM.Classify.Types
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, dataLayout, moduleTypes, funcTypes, globalTypes)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentNames)
import           UCCrux.LLVM.Constraints
import           UCCrux.LLVM.Cursor (ppCursor, Selector(..), SomeInSelector(SomeInSelector), selectWhere, selectorCursor)
import           UCCrux.LLVM.FullType (FullType(FTPtr), MapToCrucibleType, FullTypeRepr(..), PartTypeRepr, ModuleTypes, asFullType)
import           UCCrux.LLVM.FullType.MemType (toMemType)
import           UCCrux.LLVM.FullType.Translation (makeFuncSymbol, makeGlobalSymbol, globalSymbol)
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
  Located (Explanation m arch argTypes)
classifyAssertion _sym predicate loc =
  case What4.asConstantPred predicate of
    Just True -> panic "classifyAssertionFailure" ["Concretely true assertion failure??"]
    Just False ->
      Located
        loc
        (ExTruePositive ConcretelyFailingAssert)
    Nothing ->
      Located
        loc
        (ExUncertain UFailedAssert)

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
  -- | Source position where error occurred
  What4.ProgramLoc ->
  f (Explanation m arch argTypes)
unclass appCtx badBehavior errorLoc =
  do
    liftIO $
      (appCtx ^. log)
        Hi
        ("Couldn't classify error. At: " <> ppProgramLoc errorLoc)
    pure $
      ExUncertain $
        UUnclassified $
          case badBehavior of
            LLVMErrors.BBUndefinedBehavior ub ->
              UnclassifiedUndefinedBehavior errorLoc (UB.explain ub) (Some ub)
            LLVMErrors.BBMemoryError memoryError ->
              UnclassifiedMemoryError errorLoc (MemError.explain memoryError)

unfixed ::
  MonadIO f =>
  AppContext ->
  Unfixed ->
  -- | Source position where error occurred
  What4.ProgramLoc ->
  f (Explanation m arch argTypes)
unfixed appCtx tag errorLoc =
  do
    liftIO $
      (appCtx ^. log)
        Hi
        ( "Prognosis: Fixable, but the fix is not yet implemented. At: "
            <> ppProgramLoc errorLoc
        )
    pure $ ExUncertain (UUnfixed tag)

unfixable ::
  MonadIO f =>
  AppContext ->
  Unfixable ->
  -- | Source position where error occurred
  What4.ProgramLoc ->
  f (Explanation m arch argTypes)
unfixable appCtx tag errorLoc =
  do
    liftIO $
      (appCtx ^. log)
        Hi
        ( "Prognosis: Don't know how to fix this error. At: "
            <> ppProgramLoc errorLoc
        )
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
  -- | Initial LLVM memory (containing globals and functions)
  LLVMMem.MemImpl sym ->
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
  f (Located (Explanation m arch argTypes))
classifyBadBehavior appCtx modCtx funCtx sym memImpl skipped simError args annotations argShapes badBehavior =
  Located (Crucible.simErrorLoc simError)
    <$> doClassifyBadBehavior
      appCtx
      modCtx
      funCtx
      sym
      memImpl
      skipped
      simError
      args
      annotations
      argShapes
      badBehavior

doClassifyBadBehavior ::
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
  -- | Program memory
  LLVMMem.MemImpl sym ->
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
doClassifyBadBehavior appCtx modCtx funCtx sym memImpl skipped simError (Crucible.RegMap _args) annotations argShapes badBehavior =
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
      do
        ann <- liftIO $ getPtrBlockOrOffsetAnn ptr
        case ann of
          Just (Some (TypedSelector ftRepr (SomeInSelector selector))) ->
            do
              let diagnosis = Diagnosis DiagnoseWriteBadAlignment (selectWhere selector)
              diagnoseAndPrescribe diagnosis selector
              expectPointerType ftRepr $
                const $
                  return $
                    ExDiagnosis
                      (diagnosis, oneConstraint selector (Aligned alignment))
          _ -> requirePossiblePointer WriteNonPointer ptr
    LLVMErrors.BBUndefinedBehavior
      (UB.ReadBadAlignment (Crucible.RV ptr) alignment) ->
        do
          ann <- liftIO $ getPtrBlockOrOffsetAnn ptr
          case ann of
            Just (Some (TypedSelector ftRepr (SomeInSelector selector))) ->
              do
                let diagnosis = Diagnosis DiagnoseReadBadAlignment (selectWhere selector)
                diagnoseAndPrescribe diagnosis selector
                expectPointerType ftRepr $
                  const $
                    return $
                      ExDiagnosis
                        (diagnosis, oneConstraint selector (Aligned alignment))
            _ -> requirePossiblePointer ReadNonPointer ptr
    LLVMErrors.BBUndefinedBehavior
      (UB.FreeUnallocated (Crucible.RV ptr)) ->
        maybe (requirePossiblePointer FreeNonPointer ptr) pure
          =<< handleFreeUnallocated ptr
    LLVMErrors.BBUndefinedBehavior
      (UB.FreeBadOffset (Crucible.RV ptr)) ->
        do
          ann <- liftIO $ getPtrBlockOrOffsetAnn ptr
          case ann of
            Just (Some (TypedSelector ftRepr (SomeInSelector selector))) ->
              do
                int <- liftIO $ getConcretePointerBlock ptr
                case int of
                  Nothing -> unclass appCtx badBehavior errorLoc
                  Just _ ->
                    do
                      let diagnosis = Diagnosis DiagnoseFreeBadOffset (selectWhere selector)
                      diagnoseAndPrescribe diagnosis selector
                      expectPointerType ftRepr $
                        const $
                          return $
                            ExDiagnosis
                              (diagnosis, oneShapeConstraint selector (Allocated 1))
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
          Nothing -> truePositive DoubleFree
    LLVMErrors.BBUndefinedBehavior
      (UB.PtrAddOffsetOutOfBounds (Crucible.RV ptr) (Crucible.RV offset)) ->
        do
          ann <- liftIO $ getPtrBlockOrOffsetAnn ptr
          case ann of
            Just (Some (TypedSelector ftRepr (SomeInSelector selector))) ->
              case getTermAnn offset of
                Just (Some (TypedSelector _ (SomeInSelector (SelectArgument idx cursor)))) ->
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
                    unfixed appCtx tag errorLoc
                _ ->
                  case What4.asConcrete offset of
                    Just bv ->
                      do
                        let diagnosis =
                              Diagnosis DiagnosePointerConstOffset (selectWhere selector)
                        diagnoseAndPrescribe diagnosis selector
                        expectPointerType ftRepr $
                          \partTypeRepr ->
                            return $
                              ExDiagnosis
                                ( diagnosis,
                                  oneShapeConstraint
                                    selector
                                    (Allocated (elemsFromOffset' bv partTypeRepr))
                                )
                    Nothing ->
                      do
                        let tag = AddSymbolicOffsetToInputPointer
                        liftIO $
                          (appCtx ^. log) Hi $
                            Text.unwords
                              [ "Diagnosis:",
                                ppUnfixable tag,
                                "(" <> Text.pack (show (LLVMPtr.ppPtr ptr)) <> ")"
                              ]
                        unfixable appCtx tag errorLoc
            _ -> unclass appCtx badBehavior errorLoc
    LLVMErrors.BBUndefinedBehavior
      (UB.MemsetInvalidRegion (Crucible.RV ptr) _fillByte (Crucible.RV len)) ->
        do
          ann <- liftIO $ getPtrBlockOrOffsetAnn ptr
          case (ann, What4.asConcrete len) of
            ( Just (Some (TypedSelector ftRepr (SomeInSelector selector))),
              Just concreteLen
              ) ->
                do
                  let diagnosis = Diagnosis DiagnoseMemsetTooSmall (selectWhere selector)
                  diagnoseAndPrescribe diagnosis selector
                  expectPointerType ftRepr $
                    \partTypeRepr ->
                      return $
                        ExDiagnosis
                          ( diagnosis,
                            oneShapeConstraint
                              selector
                              ( Initialized
                                  (elemsFromOffset' concreteLen partTypeRepr)
                              )
                          )
            _ -> unclass appCtx badBehavior errorLoc
    LLVMErrors.BBUndefinedBehavior
      (UB.PoisonValueCreated poison) ->
        classifyPoison appCtx sym annotations poison
          >>= \case
            Nothing -> unclass appCtx badBehavior errorLoc
            Just expl -> pure expl
    LLVMErrors.BBMemoryError
      ( MemError.MemoryError
          (summarizeOp -> (_expl, ptr, _mem))
          MemError.UnwritableRegion
        ) ->
        do
          ann <- liftIO $ getPtrBlockOrOffsetAnn ptr
          case (ann, getAnyPtrOffsetAnn ptr) of
            (Just (Some (TypedSelector ftRepr (SomeInSelector selector))), _) ->
              expectPointerType ftRepr $
                const $
                  let isAllocated =
                        case selector of
                          SelectArgument idx cursor ->
                            argShapes ^. ixF' idx . to (flip Shape.isAllocated cursor)
                          -- TODO(lb): Make shapes of globals, return values
                          -- available here
                          _ -> Right True
                   in case isAllocated of
                        Left _ -> panic "classify" ["Bad cursor into argument"]
                        Right True ->
                          -- TODO: This should probably be an error, it definitely *can*
                          -- arise from a use-after-free of an argument see
                          -- test/programs/use_after_free.c
                          unclass appCtx badBehavior errorLoc
                        Right False ->
                          do
                            let diagnosis =
                                  Diagnosis DiagnoseWriteUnmapped (selectWhere selector)
                            diagnoseAndPrescribe diagnosis selector
                            return $
                              ExDiagnosis
                                (diagnosis, oneShapeConstraint selector (Allocated 1))
            -- If the pointer expression doesn't involve the function's
            -- arguments/global variables at all, then it's just a standard null
            -- dereference or similar.
            (Nothing, []) ->
              do
                notPtr <- liftIO $ notAPointer sym ptr
                case notPtr of
                  Just True -> truePositive WriteNonPointer
                  _ -> unclass appCtx badBehavior errorLoc
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
          ann <- liftIO $ getPtrBlockOrOffsetAnn ptr
          blk <- liftIO $ getConcretePointerBlock ptr
          case (ann, getAnyPtrOffsetAnn ptr) of
            ( Just (Some (TypedSelector ftRepr (SomeInSelector selector))),
              _
              ) ->
                do
                  let diagnosis =
                        Diagnosis
                          DiagnoseReadUninitialized
                          (selectWhere selector)
                  diagnoseAndPrescribe diagnosis selector
                  expectPointerType ftRepr $
                    \partTypeRepr ->
                      return $
                        ExDiagnosis
                          ( diagnosis,
                            oneShapeConstraint
                              selector
                              ( Initialized
                                  ( case What4.asConcrete (LLVMPtr.llvmPointerOffset ptr) of
                                      Just off -> elemsFromOffset' off partTypeRepr
                                      Nothing -> 1 -- TODO: Maybe unclassified
                                  )
                              )
                          )
            (Nothing, [Some (TypedSelector ftRepr (SomeInSelector selector))]) ->
              do
                let diagnosis =
                      Diagnosis
                        DiagnoseReadUninitializedOffset
                        (selectWhere selector)
                diagnoseAndPrescribe diagnosis selector
                expectPointerType ftRepr $
                  const $
                    return $
                      ExDiagnosis
                        (diagnosis, oneShapeConstraint selector (Initialized 1))
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
                        else unclass appCtx badBehavior errorLoc
                  Just (G.AllocInfo G.HeapAlloc _sz _mut _align loc) ->
                    if loc == mallocLocation
                      then unclass appCtx badBehavior errorLoc
                      else truePositive (ReadUninitializedHeap loc)
                  Just (G.AllocInfo G.GlobalAlloc _sz _mut _align _loc) ->
                    case flip Map.lookup (LLVMMem.memImplSymbolMap memImpl) =<< blk of
                      Nothing -> requirePossiblePointer ReadNonPointer ptr
                      Just glob ->
                        case ( makeFuncSymbol glob (modCtx ^. funcTypes),
                               makeGlobalSymbol (modCtx ^. globalTypes) glob
                             ) of
                          (Just {}, _) -> truePositive (DerefFunctionPointer glob)
                          (_, Just gSymb) ->
                            case modCtx ^. globalTypes . globalSymbol gSymb of
                              Some FTUnboundedArrayRepr {} ->
                                unimplemented
                                  "classify"
                                  Unimplemented.NonEmptyUnboundedSizeArrays
                              _ -> unclass appCtx badBehavior errorLoc
                          _ ->
                            panic
                              "classify"
                              ["Global not present in module: " ++ show glob]
                  -- If the "pointer" concretely wasn't a pointer, it's a bug.
                  _ -> requirePossiblePointer ReadNonPointer ptr
    LLVMErrors.BBMemoryError
      ( MemError.MemoryError
          (MemError.MemLoadHandleOp _type _str ptr mem)
          (MemError.BadFunctionPointer _msg)
        ) ->
        do
          ann <- liftIO $ getPtrBlockOrOffsetAnn ptr
          case ann of
            Just (Some (TypedSelector _ftRepr (SomeInSelector _selector))) ->
              do
                let tag = UnfixedFunctionPtrInInput
                liftIO $
                  (appCtx ^. log) Hi $
                    Text.unwords ["Diagnosis: ", ppUnfixed tag]
                unfixed appCtx tag errorLoc
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
                      then unclass appCtx badBehavior errorLoc
                      else truePositive (CallNonFunctionPointer loc)
                  _ -> unclass appCtx badBehavior errorLoc
    _ -> unclass appCtx badBehavior errorLoc
  where
    errorLoc = Crucible.simErrorLoc simError

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

    getPtrBlockOrOffsetAnn ::
      LLVMPtr.LLVMPtr sym w ->
      IO (Maybe (Some (TypedSelector m arch argTypes)))
    getPtrBlockOrOffsetAnn ptr = (getPtrOffsetAnn ptr <|>) <$> getPtrBlockAnn ptr

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
            Just (Some (TypedSelector ftRepr (SomeInSelector selector))) ->
              do
                let diagnosis =
                      Diagnosis
                        DiagnoseFreeUnallocated
                        (selectWhere selector)
                diagnoseAndPrescribe diagnosis selector
                Just
                  <$> expectPointerType
                    ftRepr
                    ( const $
                        return $
                          ExDiagnosis
                            (diagnosis, oneShapeConstraint selector (Allocated 1))
                    )
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
            Just (Some (TypedSelector ftRepr (SomeInSelector selector))) ->
              do
                let diagnosis' = Diagnosis DiagnoseNonZero (selectWhere selector)
                diagnoseAndPrescribe diagnosis' selector
                case ftRepr of
                  FTIntRepr w ->
                    return $
                      ExDiagnosis
                        ( diagnosis',
                          oneConstraint selector (BVCmp L.Ine w (BV.mkBV w 0))
                        )
                  _ -> panic "classify" ["Expected integer type"]
            _ -> unclass appCtx badBehavior errorLoc
        Just _ -> truePositive truePos

    argName :: Ctx.Index argTypes tp -> String
    argName idx = funCtx ^. argumentNames . ixF' idx . to getConst . to (maybe "<top>" Text.unpack)

    oneConstraint selector constraint =
      [NewConstraint (SomeInSelector selector) constraint]

    oneShapeConstraint selector shapeConstraint =
      [NewShapeConstraint (SomeInSelector selector) shapeConstraint]

    getConcretePointerBlock :: LLVMPtr.LLVMPtr sym w -> IO (Maybe Natural)
    getConcretePointerBlock ptr =
      do
        int <- liftIO $ What4.natToInteger sym (LLVMPtr.llvmPointerBlock ptr)
        pure (fromIntegral . What4.fromConcreteInteger <$> What4.asConcrete int)

    allocInfoFromPtr :: Mem sym -> LLVMPtr.LLVMPtr sym w -> IO (Maybe (AllocInfo sym))
    allocInfoFromPtr mem ptr =
      do
        int <- liftIO $ getConcretePointerBlock ptr
        pure $
          case int of
            Just int' -> G.possibleAllocInfo int' (G.memAllocs mem)
            Nothing -> Nothing

    diagnoseAndPrescribe :: Diagnosis -> Selector m argTypes inTy atTy -> f ()
    diagnoseAndPrescribe diagnosis selector =
      do
        liftIO $
          (appCtx ^. log) Hi $
            Text.unwords
              [ "Diagnosis: ",
                diagnose diagnosis,
                "at",
                Text.pack (show (ppCursor "<top>" (selector ^. selectorCursor)))
              ]
        liftIO $ (appCtx ^. log) Hi $ prescribe (diagnosisTag diagnosis)

    truePositive :: TruePositive -> f (Explanation m arch argTypes)
    truePositive pos =
      do
        liftIO $
          (appCtx ^. log) Hi $
            Text.unwords ["Diagnosis:", ppTruePositive pos]
        return $ ExTruePositive pos

    -- Unfortunately, this check is pretty coarse. We can conclude that the
    -- given pointer concretely isn't a pointer only if *all* of the following
    -- are true:
    --
    -- (1) It has a concrete, zero block number
    -- (2) Its offset expression didn't involve any arguments, globals, or
    -- return values of skipped functions
    --
    -- The second condition is necessary because unallocated pointers in the
    -- function arguments/return values have a concretely zero block number, but
    -- might just represent "currently unallocated" pointers.
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
        case (notPtr, null (getAnyPtrOffsetAnn ptr)) of
          (Just True, True) -> truePositive pos
          _ -> unclass appCtx badBehavior errorLoc
