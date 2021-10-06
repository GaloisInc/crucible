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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Setup
  ( generate,
    setupExecution,
    SetupAssumption (SetupAssumption),
    SetupResult (SetupResult),
    SymValue (..),
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (head, zip)

import           Control.Lens ((^.), (%~), to, at)
import           Control.Monad (void)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Foldable (for_, toList)
import           Data.Function ((&))
import           Data.Functor.Compose (Compose(Compose))
import           Data.Traversable.WithIndex (ifor)
import           Data.Map (Map)
import           Data.Proxy (Proxy(Proxy))
import           Data.Type.Equality ((:~:)(Refl), testEquality)
import qualified Data.Sequence as Seq
import qualified Data.Vector as Vec

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Classes (IxedF' (ixF'))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.NatRepr (NatRepr, type (<=), type (+), LeqProof(LeqProof))
import qualified Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.Vector as PVec

-- what4
import qualified What4.Interface as W4I
import qualified What4.InterpretedFloatingPoint as W4IFP

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import qualified Lang.Crucible.LLVM.Globals as LLVMGlobals
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

-- crux
import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Constraints (Constraints, ConstrainedTypedValue(..), ConstrainedShape(..), Constraint(..), argConstraints, globalConstraints, minimalConstrainedShape)
import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentCrucibleTypes, argumentFullTypes)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTranslation, withTypeContext, llvmModule, moduleTypes, globalTypes)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.FullType.CrucibleType (toCrucibleType)
import qualified UCCrux.LLVM.FullType.CrucibleType as FTCT
import           UCCrux.LLVM.FullType.Memory (pointerRange, sizeBv)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), ToCrucibleType, MapToCrucibleType, ToBaseType, asFullType)
import           UCCrux.LLVM.Cursor (Selector(..), Cursor(..), selectorCursor, deepenStruct, deepenArray, deepenPtr)
import           UCCrux.LLVM.Module (GlobalSymbol, globalSymbol, makeGlobalSymbol, getModule)
import           UCCrux.LLVM.Setup.Constraints (constraintToPred)
import           UCCrux.LLVM.Setup.Monad
import           UCCrux.LLVM.Shape (Shape)
import qualified UCCrux.LLVM.Shape as Shape
{- ORMOLU_ENABLE -}

newtype SymValue sym arch ft = SymValue {getSymValue :: Crucible.RegValue sym (ToCrucibleType arch ft)}

-- | Take a symbolic value (a 'Crucible.RegEntry') and a 'Constraint' that
-- applies to it, and generate a 'W4I.Pred' that gets stored in the 'Setup'
-- monad, and assumed in "UCCrux.LLVM.Run.Simulate".
constrainHere ::
  forall m arch sym argTypes inTy atTy.
  ( Crucible.IsSymInterface sym,
    ArchOk arch
  ) =>
  sym ->
  -- | Top-level selector
  Selector m argTypes inTy atTy ->
  -- | The constraint that should be assumed to be true of this value
  Constraint m atTy ->
  FullTypeRepr m atTy ->
  -- | The value to be constrained
  Crucible.RegEntry sym (ToCrucibleType arch atTy) ->
  Setup m arch sym argTypes (Crucible.RegEntry sym (ToCrucibleType arch atTy))
constrainHere sym _selector constraint fullTypeRepr regEntry@(Crucible.RegEntry _typeRepr regValue) =
  liftIO (constraintToPred (Proxy :: Proxy arch) sym constraint fullTypeRepr regValue) >>=
    assume constraint >>
    return regEntry

-- | Generate a fresh symbolic value, recording its \"origin\", i.e. what part
-- of which global variable or argument it is. That annotation will later be
-- looked up in "UCCrux.LLVM.Classify.classify" and used to generate additional
-- preconditions.
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

-- | Like 'annotatedTerm'. Generates a fresh pointer with an annotated block and
-- offset.
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

generateM' ::
  forall m h a.
  Monad m =>
  NatRepr (h + 1) ->
  (forall n. n + 1 <= h + 1 => NatRepr n -> m a) ->
  m (PVec.Vector (h + 1) a)
generateM' h1 gen =
  PVec.generateM
    (NatRepr.predNat h1)
    ( \(n :: NatRepr n) ->
        case NatRepr.leqAdd2
               (LeqProof :: LeqProof n h)
               (NatRepr.leqRefl (Proxy :: Proxy 1) :: LeqProof 1 1) ::
               LeqProof (n + 1) (h + 1) of
          LeqProof -> gen n
    )

-- | Generate and constrain all the symbolic values. This is currently only used
-- for arguments, but once global constraints are collected/supported, it can be
-- used for those as well.
--
-- Traverses the input 'ConstrainedShape' and replaces the lists of constraints
-- with a 'SymValue' that conforms to those constraints. Allocates memory along
-- the way as required by the form of the 'ConstrainedShape'.
generate ::
  forall arch sym m atTy inTy argTypes.
  ( ArchOk arch,
    LLVMMem.HasLLVMAnn sym,
    Crucible.IsSymInterface sym
  ) =>
  sym ->
  ModuleContext m arch ->
  FullTypeRepr m atTy ->
  -- | The argument or global variable to be generated
  Selector m argTypes inTy atTy ->
  -- | The set of constraints and memory layout of the value to be generated
  ConstrainedShape m atTy ->
  Setup m arch sym argTypes (Shape m (SymValue sym arch) atTy)
generate sym modCtx ftRepr selector (ConstrainedShape shape) =
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
          <$> (SymValue <$> malloc sym ftRepr selector (toEnum n))
          <*> pure (Shape.ShapeAllocated n)
      (Shape.ShapePtr _constraints (Shape.ShapeInitialized vec), FTPtrRepr ptPtdTo) ->
        do
          let num = Seq.length vec
          Some numRepr <-
            case NatRepr.mkNatRepr (toEnum num) of
              Some nr ->
                -- pointerRange adds 1 to the size, so we have to subtract 1.
                case NatRepr.isZeroNat nr of
                  NatRepr.ZeroNat -> panic "generate" ["Empty vector"]
                  NatRepr.NonZeroNat -> return (Some (NatRepr.predNat nr))
          ptr <- malloc sym ftRepr selector (toEnum num)
          let ftPtdTo = asFullType (modCtx ^. moduleTypes) ptPtdTo
          size <- liftIO $ sizeBv modCtx sym ftPtdTo 1
          -- For each offset, generate a value and store it there.
          pointers <- liftIO $ pointerRange proxy sym ptr size numRepr
          pointedTos <-
            ifor pointers $ \i ptrAtOffset ->
              do
                let selector' = selector & selectorCursor %~ deepenPtr (modCtx ^. moduleTypes)
                pointedTo <-
                  generate
                    sym
                    modCtx
                    ftPtdTo
                    selector'
                    (ConstrainedShape
                      (vec `Seq.index`
                        fromIntegral (Fin.finToNat i)))
                annotatedPtrAtOffset <-
                  store
                    sym
                    (modCtx ^. moduleTypes)
                    ftRepr
                    selector
                    ptrAtOffset
                    (pointedTo ^. Shape.tag . to getSymValue)
                pure (annotatedPtrAtOffset, pointedTo)
          -- Make sure we use the fully-annotated pointer in the return value,
          -- so that its annotations can be looked up during classification.
          let annotatedPtr = fst (fst (PVec.uncons pointedTos))
          pure $
            Shape.ShapePtr
              (SymValue annotatedPtr)
              (Shape.ShapeInitialized (Seq.fromList (toList (fmap snd pointedTos))))
      (Shape.ShapeArray (Compose _constraints) n elems, FTArrayRepr _len ftRepr') ->
        case NatRepr.isZeroNat n of
          NatRepr.NonZeroNat ->
            do
              elems' <-
                generateM' n $ \idx ->
                  generate
                    sym
                    modCtx
                    ftRepr'
                    (selector & selectorCursor %~ deepenArray idx n)
                    (ConstrainedShape (PVec.elemAt idx elems))
              pure $
                Shape.ShapeArray
                  -- TODO: Upstream a toVector function
                  ( SymValue
                      ( Vec.fromList
                          ( map
                              (^. Shape.tag . to getSymValue)
                              (PVec.toList elems')
                          )
                      )
                  )
                  n
                  elems'
      (Shape.ShapeUnboundedArray (Compose _constraints) elems, _) ->
        if Seq.null elems
          then pure $ Shape.ShapeUnboundedArray (SymValue Vec.empty) Seq.empty
          else -- TODO(lb): This needs a new constructor for Cursor.
            unimplemented "generate" Unimplemented.NonEmptyUnboundedSizeArrays
      (Shape.ShapeStruct (Compose _constraints) fields, FTStructRepr _ fieldTypes) ->
        do
          fields' <-
            Ctx.generateM (Ctx.size fields) $
              \idx ->
                generate
                  sym
                  modCtx
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
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  sym ->
  Ctx.Assignment (ConstrainedShape m) argTypes ->
  Setup
    m
    arch
    sym
    argTypes
    ( Ctx.Assignment (Shape m (SymValue sym arch)) argTypes,
      Crucible.RegMap sym (MapToCrucibleType arch argTypes)
    )
generateArgs _appCtx modCtx funCtx sym argSpecs =
  do
    let argTypesRepr = funCtx ^. argumentCrucibleTypes
    shapes <-
      Ctx.generateM
        (Ctx.size (funCtx ^. argumentFullTypes))
        ( \index ->
            let ft = funCtx ^. argumentFullTypes . ixF' index
             in generate
                  sym
                  modCtx
                  ft
                  (SelectArgument index (Here ft))
                  (argSpecs Ctx.! index)
        )
    pure
      ( shapes,
        Crucible.RegMap $
          FTCT.generate
            (Proxy :: Proxy arch)
            (Ctx.size (funCtx ^. argumentFullTypes))
            ( \index index' Refl ->
                Crucible.RegEntry
                  (argTypesRepr Ctx.! index')
                  (shapes ^. ixF' index . Shape.tag . to getSymValue)
            )
      )

-- | Populate non-constant global variables with symbolic data, constrained
-- according to the given preconditions.
populateNonConstGlobals ::
  forall m arch sym argTypes.
  ( Crucible.IsSymInterface sym,
    LLVMMem.HasLLVMAnn sym,
    ArchOk arch
  ) =>
  ModuleContext m arch ->
  sym ->
  Map (GlobalSymbol m) (ConstrainedTypedValue m) ->
  Setup m arch sym argTypes ()
populateNonConstGlobals modCtx sym constrainedGlobals =
  for_
    (modCtx ^. llvmModule . to getModule . to L.modGlobals . to (filter (not . isConstGlobal)))
    populateNonConstGlobal
  where
    isConstGlobal = L.gaConstant . L.globalAttrs

    populateNonConstGlobal :: L.Global -> Setup m arch sym argTypes ()
    populateNonConstGlobal glob =
      let symb = L.globalSym glob
          gSymb =
            case makeGlobalSymbol (modCtx ^. globalTypes) symb of
              Nothing ->
                panic
                  "populateNonConstGlobal"
                  ["Missing type for global " ++ show symb]
              Just gs -> gs
       in case modCtx ^. globalTypes . globalSymbol gSymb of
            (Some fullTy) ->
              do
                val <-
                  generate
                    sym
                    modCtx
                    fullTy
                    (SelectGlobal gSymb (Here fullTy))
                    ( case constrainedGlobals ^. at gSymb of
                        Just (ConstrainedTypedValue cgTy cgShape) ->
                          case testEquality cgTy fullTy of
                            Nothing ->
                              panic
                                "populateNonConstGlobal"
                                ["Ill-typed constraints on global " ++ show symb]
                            Just Refl -> cgShape
                        Nothing -> minimalConstrainedShape fullTy
                    )
                void $
                  storeGlobal
                    sym
                    fullTy
                    (SelectGlobal gSymb (Here fullTy))
                    symb
                    (val ^. Shape.tag . to getSymValue)

-- | Generate arguments and global variables that conform to the preconditions
-- specified in the 'Constraints'.
--
-- Constant global variables are also populated by their initializers.
--
-- The two returned assignments contain duplicate data, but they are used for
-- different purposes: The 'Crucible.RegMap' can be (and is) passed directly to
-- a Crucible CFG, whereas the 'Ctx.Assignment' of 'Shape' is more amenable to
-- introspection, for instance in the classification process, because it can be
-- traversed and examined like the inductive datatype it is, rather than dealing
-- with reading from the Crucible-LLVM memory model.
setupExecution ::
  ( Crucible.IsSymInterface sym,
    LLVMMem.HasLLVMAnn sym,
    ArchOk arch,
    MonadIO f
  ) =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  sym ->
  -- | Constraints and memory layouts of each argument and global
  Constraints m argTypes ->
  f
    ( SetupResult m arch sym argTypes,
      ( Ctx.Assignment (Shape m (SymValue sym arch)) argTypes,
        Crucible.RegMap sym (MapToCrucibleType arch argTypes)
      )
    )
setupExecution appCtx modCtx funCtx sym constraints = do
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
        LLVMGlobals.populateConstGlobals sym (LLVMTrans.globalInitMap moduleTrans)
          =<< LLVMGlobals.initializeAllMemory sym llvmCtxt (modCtx ^. llvmModule . to getModule)
  runSetup modCtx mem $
    do
      populateNonConstGlobals modCtx sym (constraints ^. globalConstraints)
      generateArgs appCtx modCtx funCtx sym (constraints ^. argConstraints)
