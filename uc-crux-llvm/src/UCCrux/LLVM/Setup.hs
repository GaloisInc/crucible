{-
Module       : UCCrux.LLVM.Setup
Description  : Generate constrained symbolic values and memory from a 'ConstrainedShape'
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Setup
  ( setupExecution,
    SetupAssumption (SetupAssumption),
    SetupResult (SetupResult),
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (head, reverse, zip)

import           Control.Lens ((^.), (%~),to)
import           Control.Monad (foldM, forM)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.List.NonEmpty (NonEmpty((:|)), head, reverse, zip, toList)
import           Data.Foldable (for_)
import           Data.Function ((&))
import           Data.Functor.Compose (Compose(Compose))
import           Data.Proxy (Proxy(Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector as Vec

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Classes (IxedF' (ixF'))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (NatRepr, type (<=))

import qualified What4.Interface as W4I
import qualified What4.InterpretedFloatingPoint as W4IFP

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.Globals as LLVMGlobals
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPointer
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentCrucibleTypes, argumentFullTypes, moduleTypes)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTranslation, withTypeContext, llvmModule)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.FullType.CrucibleType (toCrucibleType)
import qualified UCCrux.LLVM.FullType.CrucibleType as FTCT
import           UCCrux.LLVM.FullType.MemType (asFullType)
import           UCCrux.LLVM.FullType.ModuleTypes (ModuleTypes)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), ToCrucibleType, MapToCrucibleType, ToBaseType)
import           UCCrux.LLVM.Cursor (Selector(..), Cursor(..), selectorCursor, deepenStruct, deepenPtr)
import           UCCrux.LLVM.Setup.Monad
import           UCCrux.LLVM.Shape (Shape)
import qualified UCCrux.LLVM.Shape as Shape
import           UCCrux.LLVM.Constraints (ConstrainedShape(..), Constraint(..))
{- ORMOLU_ENABLE -}

newtype SymValue sym arch ft = SymValue {getSymValue :: Crucible.RegValue sym (ToCrucibleType arch ft)}

constrainHere ::
  forall m arch sym argTypes inTy atTy.
  ( Crucible.IsSymInterface sym,
    ArchOk arch
  ) =>
  sym ->
  -- | Top-level selector
  Selector m argTypes inTy atTy ->
  Constraint m atTy ->
  FullTypeRepr m atTy ->
  Crucible.RegEntry sym (ToCrucibleType arch atTy) ->
  Setup m arch sym argTypes (Crucible.RegEntry sym (ToCrucibleType arch atTy))
constrainHere sym _selector constraint fullTypeRepr regEntry@(Crucible.RegEntry typeRepr regValue) =
  case (fullTypeRepr, constraint) of
    (_, Aligned alignment) ->
      assumeOne =<< liftIO (LLVMMem.isAligned sym ?ptrWidth regValue alignment)
    (FTIntRepr w, BVCmp op bv) ->
      assumeOne
        =<< liftIO
          ( interpretOp op (LLVMPointer.llvmPointerOffset regValue)
              =<< W4I.bvLit sym w bv
          )
  where
    assumeOne :: W4I.Pred sym -> Setup m arch sym argTypes (Crucible.RegEntry sym (ToCrucibleType arch atTy))
    assumeOne pred = assume constraint pred >> pure regEntry
    interpretOp ::
      forall w. 1 <= w => L.ICmpOp -> W4I.SymBV sym w -> W4I.SymBV sym w -> IO (W4I.Pred sym)
    interpretOp =
      \case
        L.Ieq -> W4I.bvEq sym
        L.Ine -> W4I.bvNe sym
        L.Iult -> W4I.bvUlt sym
        L.Iule -> W4I.bvUle sym
        L.Iugt -> W4I.bvUgt sym
        L.Iuge -> W4I.bvUge sym
        L.Islt -> W4I.bvSlt sym
        L.Isle -> W4I.bvSle sym
        L.Isgt -> W4I.bvSgt sym
        L.Isge -> W4I.bvSge sym

annotatedTerm ::
  forall m arch sym inTy atTy argTypes.
  (Crucible.IsSymInterface sym) =>
  sym ->
  FullTypeRepr m atTy ->
  CrucibleTypes.BaseTypeRepr (ToBaseType sym arch atTy) ->
  -- | Path to this value
  Selector m argTypes inTy atTy ->
  Setup m arch sym argTypes (W4I.SymExpr sym (ToBaseType sym arch atTy))
annotatedTerm sym fullTypeRepr baseTypeRepr selector =
  do
    symbol <- freshSymbol
    (_, expr) <-
      getAnnotation sym selector fullTypeRepr
        =<< liftIO (W4I.freshConstant sym symbol baseTypeRepr)
    pure expr

-- | A fresh pointer with an annotated block and offset
annotatedLLVMPtr ::
  forall m arch sym inTy atTy argTypes w.
  (1 <= w, Crucible.IsSymInterface sym) =>
  sym ->
  NatRepr w ->
  FullTypeRepr m atTy ->
  -- | Path to this pointer
  Selector m argTypes inTy atTy ->
  Setup m arch sym argTypes (LLVMMem.LLVMPtr sym w)
annotatedLLVMPtr sym w fullTypeRepr selector =
  do
    symbol <- freshSymbol
    ptr <-
      liftIO . LLVMMem.llvmPointer_bv sym
        =<< liftIO (W4I.freshConstant sym symbol (W4I.BaseBVRepr w))
    annotatePointer sym selector fullTypeRepr ptr

pointerRange ::
  ( ArchOk arch,
    Crucible.IsSymInterface sym
  ) =>
  proxy arch ->
  sym ->
  -- | Base pointer
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  -- | Offset to add
  W4I.SymBV sym (ArchWidth arch) ->
  -- | Number of pointers to generate/times to add the offset
  Int ->
  IO (NonEmpty (LLVMMem.LLVMPtr sym (ArchWidth arch)))
pointerRange _proxy sym ptr offset size =
  reverse
    <$> foldM
      ( \(p :| ps) () ->
          do
            p' <- LLVMMem.ptrAdd sym ?ptrWidth p offset
            pure (p' :| (p : ps))
      )
      (ptr :| [])
      (replicate (size - 1) ())

-- | Generate and constrain all the symbolic values
generate ::
  forall arch sym m atTy inTy argTypes.
  ( ArchOk arch,
    LLVMMem.HasLLVMAnn sym,
    Crucible.IsSymInterface sym
  ) =>
  sym ->
  ModuleTypes m ->
  FullTypeRepr m atTy ->
  Selector m argTypes inTy atTy ->
  ConstrainedShape m atTy ->
  Setup m arch sym argTypes (Shape m (SymValue sym arch) atTy)
generate sym mts ftRepr selector (ConstrainedShape shape) =
  constrain
    (shape ^. Shape.tag)
    =<< case (shape, ftRepr) of
      (Shape.ShapeInt _constraints, FTIntRepr w) ->
        Shape.ShapeInt . SymValue
          <$> annotatedLLVMPtr sym w ftRepr selector
      (Shape.ShapeFloat _constraints, FTFloatRepr floatInfo) ->
        Shape.ShapeFloat . SymValue
          <$> annotatedTerm
            sym
            ftRepr
            (W4IFP.iFloatBaseTypeRepr sym floatInfo)
            selector
      (Shape.ShapePtr _constraints Shape.ShapeUnallocated, FTPtrRepr {}) ->
        Shape.ShapePtr
          <$> (SymValue <$> annotatedLLVMPtr sym ?ptrWidth ftRepr selector)
          <*> pure Shape.ShapeUnallocated
      (Shape.ShapeFuncPtr _constraints, _) ->
        Shape.ShapeFuncPtr . SymValue
          <$> annotatedLLVMPtr sym ?ptrWidth ftRepr selector
      (Shape.ShapeOpaquePtr _constraints, FTOpaquePtrRepr {}) ->
        Shape.ShapeOpaquePtr . SymValue
          <$> annotatedLLVMPtr sym ?ptrWidth ftRepr selector
      (Shape.ShapePtr _constraints (Shape.ShapeAllocated n), FTPtrRepr _ptdTo) ->
        Shape.ShapePtr
          <$> (SymValue <$> malloc sym ftRepr selector n)
          <*> pure (Shape.ShapeAllocated n)
      (Shape.ShapePtr _constraints (Shape.ShapeInitialized vec), FTPtrRepr ptPtdTo) ->
        do
          let num = Vec.length vec
          ptr <- malloc sym ftRepr selector num
          let ftPtdTo = asFullType mts ptPtdTo
          size <- sizeBv proxy sym ftPtdTo 1
          -- For each offset, generate a value and store it there.
          pointers <- liftIO $ pointerRange proxy sym ptr size num
          pointedTos <-
            forM (zip (0 :| [1 .. num - 1]) pointers) $ \(i, ptrAtOffset) ->
              do
                let selector' = selector & selectorCursor %~ deepenPtr mts
                pointedTo <-
                  generate sym mts ftPtdTo selector' (ConstrainedShape (vec Vec.! i))
                annotatedPtrAtOffset <-
                  store
                    sym
                    mts
                    ftRepr
                    selector
                    ptrAtOffset
                    (pointedTo ^. Shape.tag . to getSymValue)
                pure (annotatedPtrAtOffset, pointedTo)
          -- Make sure we use the fully-annotated pointer in the return value,
          -- so that its annotations can be looked up during classification.
          let annotatedPtr = fst (head pointedTos)
          pure $
            Shape.ShapePtr
              (SymValue annotatedPtr)
              (Shape.ShapeInitialized (Vec.fromList (toList (fmap snd pointedTos))))
      (Shape.ShapeArray (Compose _constraints) _n _rest, FTArrayRepr _ _ftRepr') ->
        unimplemented "generate" Unimplemented.GeneratingArrays
      (Shape.ShapeStruct (Compose _constraints) fields, FTStructRepr _ fieldTypes) ->
        do
          fields' <-
            Ctx.generateM (Ctx.size fields) $
              \idx ->
                generate
                  sym
                  mts
                  (fieldTypes ^. ixF' idx)
                  (selector & selectorCursor %~ deepenStruct idx)
                  (ConstrainedShape (fields ^. ixF' idx))
          let fieldVals =
                FTCT.generate (Proxy :: Proxy arch) (Ctx.size fields) $
                  \idx _ Refl -> fields' ^. ixF' idx . Shape.tag . to getSymValue . to Crucible.RV
          pure $ Shape.ShapeStruct (SymValue fieldVals) fields'
  where
    proxy = Proxy :: Proxy arch
    constrain ::
      Compose [] (Constraint m) atTy ->
      Shape m (SymValue sym arch) atTy ->
      Setup m arch sym argTypes (Shape m (SymValue sym arch) atTy)
    constrain (Compose constraints) s =
      do
        for_ constraints $
          \c -> constrainHere sym selector c ftRepr (Crucible.RegEntry (toCrucibleType proxy ftRepr) (s ^. Shape.tag . to getSymValue))
        pure s

generateArgs ::
  forall m arch sym argTypes.
  ( Crucible.IsSymInterface sym,
    LLVMMem.HasLLVMAnn sym,
    ArchOk arch
  ) =>
  AppContext ->
  FunctionContext m arch argTypes ->
  sym ->
  Ctx.Assignment (ConstrainedShape m) argTypes ->
  Setup m arch sym argTypes (Crucible.RegMap sym (MapToCrucibleType arch argTypes))
generateArgs _appCtx funCtx sym argSpecs = do
  let argTypesRepr = funCtx ^. argumentCrucibleTypes
  Crucible.RegMap
    <$> FTCT.generateM
      (Proxy :: Proxy arch)
      (Ctx.size (funCtx ^. argumentFullTypes))
      ( \index index' Refl ->
          let typeRepr = argTypesRepr Ctx.! index'
              ft = funCtx ^. argumentFullTypes . ixF' index
           in Crucible.RegEntry typeRepr . (^. Shape.tag . to getSymValue)
                <$> generate
                  sym
                  (funCtx ^. moduleTypes)
                  ft
                  (SelectArgument index (Here ft))
                  (argSpecs Ctx.! index)
      )

setupExecution ::
  ( Crucible.IsSymInterface sym,
    LLVMMem.HasLLVMAnn sym,
    ArchOk arch,
    MonadIO f
  ) =>
  AppContext ->
  ModuleContext arch ->
  FunctionContext m arch argTypes ->
  sym ->
  Ctx.Assignment (ConstrainedShape m) argTypes ->
  f
    ( Either
        (SetupError m arch argTypes)
        ( SetupResult m arch sym argTypes,
          Crucible.RegMap sym (MapToCrucibleType arch argTypes)
        )
    )
setupExecution appCtx modCtx funCtx sym argSpecs = do
  let moduleTrans = modCtx ^. moduleTranslation
  let llvmCtxt = moduleTrans ^. LLVMTrans.transContext
  -- TODO(lb): This could be more lazy: We could initialize and allocate only
  -- those variables and functions that are used by the program, using the same
  -- machinery as for function arguments. This would also help with the
  -- execution of functions that have preconditions on global variables beyond
  -- them being initialized.
  mem <-
    withTypeContext modCtx $
      liftIO $
        LLVMGlobals.populateAllGlobals sym (LLVMTrans.globalInitMap moduleTrans)
          =<< LLVMGlobals.initializeAllMemory sym llvmCtxt (modCtx ^. llvmModule)
  runSetup modCtx mem (generateArgs appCtx funCtx sym argSpecs)
