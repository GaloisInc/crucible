{-
Module       : UCCrux.LLVM.Setup.Monad
Description  : Monad for setting up memory and function arguments.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.Setup.Monad
  ( Setup,
    SetupError (..),
    ppSetupError,
    SetupState,
    SetupAssumption (..),
    SetupResult (..),
    setupMem,
    TypedSelector (..),
    freshSymbol,
    assume,
    getAnnotation,
    annotatePointer,
    runSetup,
    storableType,
    sizeInBytes,
    sizeBv,
    malloc,
    store,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens (to, (.=), (%=), (<+=), Simple, Lens, lens, (^.), view)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Control.Monad.Except (throwError, ExceptT, MonadError, runExceptT)
import           Control.Monad.Reader (MonadReader, ask)
import           Control.Monad.State.Strict (MonadState, gets)
import           Control.Monad.Writer (MonadWriter, tell)
import           Control.Monad.RWS (RWST, runRWST)
import           Data.BitVector.Sized (mkBV)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(Proxy))
import           Data.Text (Text)
import qualified Data.Text.IO as TextIO
import           Data.Void (Void)
import qualified Prettyprinter as PP
import           Prettyprinter (Doc)

import qualified Lumberjack as LJ

import           Data.Parameterized.Classes (OrdF)
import           Data.Parameterized.Ctx (Ctx)
import           Data.Parameterized.Some (Some(Some))

import qualified What4.Interface as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

import           Lang.Crucible.LLVM.Bytes (bytesToInteger)
import           Lang.Crucible.LLVM.DataLayout (noAlignment, maxAlignment)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPtr
import           Lang.Crucible.LLVM.MemType (MemType, memTypeSize)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext(llvmDataLayout))

import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTranslation)
import           UCCrux.LLVM.Cursor (Selector, SomeInSelector(..))
import           UCCrux.LLVM.FullType.CrucibleType (toCrucibleType)
import           UCCrux.LLVM.FullType.Type (FullType(FTPtr), FullTypeRepr(FTPtrRepr), ToCrucibleType, ToBaseType, ModuleTypes, asFullType)
import           UCCrux.LLVM.FullType.MemType (toMemType)
import           UCCrux.LLVM.Constraints (Constraint)
{- ORMOLU_ENABLE -}

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data TypedSelector m arch (argTypes :: Ctx (FullType m)) (ft :: FullType m)
  = TypedSelector (FullTypeRepr m ft) (SomeInSelector m argTypes ft)

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data SetupError m arch (argTypes :: Ctx (FullType m))
  = SetupTypeTranslationError MemType

ppSetupError :: SetupError m arch argTypes -> Doc Void
ppSetupError =
  \case
    SetupTypeTranslationError memType ->
      PP.pretty ("Couldn't translate MemType" :: Text) <> PP.viaShow memType

data SetupAssumption m sym = SetupAssumption
  { assumptionReason :: Some (Constraint m),
    assumptionPred :: What4.Pred sym
  }

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data SetupState m arch sym (argTypes :: Ctx (FullType m)) = SetupState
  { _setupMem :: LLVMMem.MemImpl sym,
    -- | This map tracks where a given expression originated from
    _setupAnnotations :: Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)),
    -- | Counter for generating unique/fresh symbols
    _symbolCounter :: !Int
  }

makeSetupState :: LLVMMem.MemImpl sym -> SetupState m arch sym argTypes
makeSetupState mem = SetupState mem Map.empty 0

setupMem :: Simple Lens (SetupState m arch sym argTypes) (LLVMMem.MemImpl sym)
setupMem = lens _setupMem (\s v -> s {_setupMem = v})

setupAnnotations :: Simple Lens (SetupState m arch sym argTypes) (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)))
setupAnnotations = lens _setupAnnotations (\s v -> s {_setupAnnotations = v})

symbolCounter :: Simple Lens (SetupState m arch sym argTypes) Int
symbolCounter = lens _symbolCounter (\s v -> s {_symbolCounter = v})

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
newtype Setup m arch sym (argTypes :: Ctx (FullType m)) a
  = Setup
      ( ExceptT
          (SetupError m arch argTypes)
          ( RWST
              (ModuleContext arch)
              [SetupAssumption m sym]
              (SetupState m arch sym argTypes)
              IO
          )
          a
      )
  deriving (Applicative, Functor, Monad, MonadIO)

deriving instance MonadError (SetupError m arch argTypes) (Setup m arch sym argTypes)

deriving instance MonadState (SetupState m arch sym argTypes) (Setup m arch sym argTypes)

deriving instance MonadReader (ModuleContext arch) (Setup m arch sym argTypes)

deriving instance MonadWriter [SetupAssumption m sym] (Setup m arch sym argTypes)

instance LJ.HasLog Text (Setup m arch sym argTypes) where
  getLogAction = pure $ LJ.LogAction (liftIO . TextIO.putStrLn . ("[Crux] " <>))

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data SetupResult m arch sym (argTypes :: Ctx (FullType m)) = SetupResult
  { resultMem :: LLVMMem.MemImpl sym,
    -- | This map tracks where a given expression originated from, i.e. whether
    -- it was generated as part of an argument of global variable, and if so,
    -- where in said value it resides (via a 'Selector'). This is used by
    -- 'UCCrux.LLVM.Classify.classifyBadBehavior' to deduce new preconditions
    -- and attach constraints in the right place.
    --
    -- For example, if the error is an OOB write and classification looks up the
    -- pointer in this map and it appears in an argument, it will attach a
    -- precondition that that part of the argument gets allocated with more
    -- space. If it looks up the pointer and it's not in this map, it's not clear
    -- how this error could be prevented, and the error will be unclassified.
    resultAnnotations ::
      Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)),
    resultAssumptions ::
      [SetupAssumption m sym]
  }

runSetup ::
  MonadIO f =>
  ModuleContext arch ->
  LLVMMem.MemImpl sym ->
  Setup m arch sym argTypes a ->
  f (Either (SetupError m arch argTypes) (SetupResult m arch sym argTypes, a))
runSetup modCtx mem (Setup computation) = do
  result <-
    liftIO $
      runRWST (runExceptT computation) modCtx (makeSetupState mem)
  pure $
    case result of
      (Left err, _, _) -> Left err
      (Right result', state, assumptions) ->
        Right
          ( SetupResult
              (state ^. setupMem)
              (state ^. setupAnnotations)
              assumptions,
            result'
          )

freshSymbol :: Setup m arch sym argTypes What4.SolverSymbol
freshSymbol =
  do
    counter <- symbolCounter <+= 1
    pure $ What4.safeSymbol ("fresh" ++ show counter)

assume ::
  Constraint m ty ->
  What4.Pred sym ->
  Setup m arch sym argTypes ()
assume constraint predicate = tell [SetupAssumption (Some constraint) predicate]

addAnnotation ::
  OrdF (What4.SymAnnotation sym) =>
  Some (What4.SymAnnotation sym) ->
  -- | Path to this value
  Selector m argTypes inTy atTy ->
  FullTypeRepr m atTy ->
  Setup m arch sym argTypes ()
addAnnotation ann selector fullTypeRepr =
  setupAnnotations
    %= Map.insert ann (Some (TypedSelector fullTypeRepr (SomeInSelector selector)))

-- | Retrieve a pre-existing annotation, or make a new one.
getAnnotation ::
  Crucible.IsSymInterface sym =>
  sym ->
  -- | Path to this value
  Selector m argTypes inTy atTy ->
  FullTypeRepr m atTy ->
  What4.SymExpr sym (ToBaseType sym arch atTy) ->
  Setup
    m
    arch
    sym
    argTypes
    ( What4.SymAnnotation sym (ToBaseType sym arch atTy),
      What4.SymExpr sym (ToBaseType sym arch atTy)
    )
getAnnotation sym selector fullTypeRepr expr =
  case What4.getAnnotation sym expr of
    Just annotation ->
      do
        addAnnotation (Some annotation) selector fullTypeRepr
        pure (annotation, expr)
    Nothing ->
      do
        (annotation, expr') <- liftIO $ What4.annotateTerm sym expr
        addAnnotation (Some annotation) selector fullTypeRepr
        pure (annotation, expr')

annotatePointer ::
  Crucible.IsSymInterface sym =>
  sym ->
  -- | Path to this pointer
  Selector m argTypes inTy atTy ->
  FullTypeRepr m atTy ->
  LLVMMem.LLVMPtr sym w ->
  Setup m arch sym argTypes (LLVMMem.LLVMPtr sym w)
annotatePointer sym selector fullTypeRepr ptr =
  do
    block <- liftIO $ What4.natToInteger sym (LLVMPtr.llvmPointerBlock ptr)
    ptr' <-
      case What4.getAnnotation sym block of
        Just annotation ->
          do
            addAnnotation (Some annotation) selector fullTypeRepr
            pure ptr
        Nothing ->
          do
            (annotation, ptr') <- liftIO (LLVMPtr.annotatePointerBlock sym ptr)
            addAnnotation (Some annotation) selector fullTypeRepr
            pure ptr'
    let offset = LLVMPtr.llvmPointerOffset ptr'
    case What4.getAnnotation sym offset of
      Just annotation ->
        do
          addAnnotation (Some annotation) selector fullTypeRepr
          pure ptr'
      Nothing ->
        do
          (annotation, ptr'') <- liftIO (LLVMPtr.annotatePointerOffset sym ptr)
          addAnnotation (Some annotation) selector fullTypeRepr
          pure ptr''

storableType :: ArchOk arch => MemType -> Setup m arch sym argTypes LLVMMem.StorageType
storableType memType =
  maybe (throwError (SetupTypeTranslationError memType)) pure (LLVMMem.toStorableType memType)

modifyMem ::
  (LLVMMem.MemImpl sym -> Setup m arch sym argTypes (a, LLVMMem.MemImpl sym)) ->
  Setup m arch sym argTypes a
modifyMem f =
  do
    mem <- gets (view setupMem)
    (val, mem') <- f mem
    setupMem .= mem'
    pure val

_modifyMem_ ::
  (LLVMMem.MemImpl sym -> Setup m arch sym argTypes (LLVMMem.MemImpl sym)) ->
  Setup m arch sym argTypes ()
_modifyMem_ f = modifyMem (fmap ((),) . f)

sizeInBytes :: FullTypeRepr m ft -> Int -> Setup m arch sym argTypes Integer
sizeInBytes ftRepr size =
  do
    moduleContext <- ask
    let dl =
          moduleContext
            ^. moduleTranslation
              . LLVMTrans.transContext
              . LLVMTrans.llvmTypeCtx
              . to llvmDataLayout
    pure $ fromIntegral size * bytesToInteger (memTypeSize dl (toMemType ftRepr))

sizeBv ::
  ( Crucible.IsSymInterface sym,
    ArchOk arch
  ) =>
  proxy arch ->
  sym ->
  FullTypeRepr m ft ->
  Int ->
  Setup m arch sym argTypes (What4.SymExpr sym (What4.BaseBVType (ArchWidth arch)))
sizeBv _proxy sym ftRepr size =
  liftIO . What4.bvLit sym ?ptrWidth . mkBV ?ptrWidth =<< sizeInBytes ftRepr size

malloc ::
  forall m sym arch argTypes inTy atTy.
  ( Crucible.IsSymInterface sym,
    ArchOk arch
  ) =>
  sym ->
  FullTypeRepr m ('FTPtr atTy) ->
  -- | Path to this pointer
  Selector m argTypes inTy ('FTPtr atTy) ->
  -- | Size, as in number of elements. Should be strictly positive.
  Int ->
  Setup m arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch))
malloc sym fullTypeRepr selector size =
  do
    moduleContext <- ask
    let dl =
          moduleContext
            ^. moduleTranslation
              . LLVMTrans.transContext
              . LLVMTrans.llvmTypeCtx
              . to llvmDataLayout
    ptr <-
      modifyMem $
        \mem ->
          do
            sz <- sizeBv (Proxy :: Proxy arch) sym fullTypeRepr size
            (p, mem') <-
              liftIO $
                do
                  LLVMMem.doMalloc
                    sym
                    LLVMMem.HeapAlloc -- TODO(lb): Change based on arg/global
                    LLVMMem.Mutable -- TODO(lb): Change based on arg/global
                    "crux-llvm bugfinding auto-setup"
                    mem
                    sz
                    (maxAlignment dl) -- TODO is this OK?
            p' <- annotatePointer sym selector fullTypeRepr p
            pure (p', mem')

    annotatePointer sym selector fullTypeRepr ptr

store ::
  forall m arch sym argTypes inTy ft.
  ( Crucible.IsSymInterface sym,
    LLVMMem.HasLLVMAnn sym,
    ArchOk arch
  ) =>
  sym ->
  ModuleTypes m ->
  FullTypeRepr m ('FTPtr ft) ->
  -- | Path to this pointer
  Selector m argTypes inTy ('FTPtr ft) ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  Setup m arch sym argTypes (LLVMMem.LLVMPtr sym (ArchWidth arch))
store sym mts ptrRepr@(FTPtrRepr ptPtdTo) selector ptr regValue =
  do
    let ftPtdTo = asFullType mts ptPtdTo
    storageType <- storableType (toMemType ftPtdTo)
    modifyMem $
      \mem ->
        do
          ptr' <- annotatePointer sym selector ptrRepr ptr
          mem' <- liftIO $ LLVMMem.doStore sym mem ptr' (toCrucibleType (Proxy :: Proxy arch) ftPtdTo) storageType noAlignment regValue
          pure (ptr', mem')
