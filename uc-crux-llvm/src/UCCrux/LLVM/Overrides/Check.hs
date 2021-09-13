{-
Module       : UCCrux.LLVM.Overrides.Check
Description  : Overrides that check that deduced preconditions are met.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

After UC-Crux-LLVM has deduced the preconditions of a function, it can install
an override that checks that the preconditions are met at callsites.

In particular, creating a check override takes the result of contract inference
on a function f (namely, 'Constraints') and makes an override that has the same
signature as f, and when called will:

- Create a bunch of predicates that represent whether or not the constraints
  were violated at this call
- Stash them away in an 'IORef'
- Call the original implementation of f

The hope is that this will be useful for refining overly pessimistic (sufficient
but unnecessary) preconditions in inferred contracts, or for indicating the
presence of bugs (when the contract really *should* hold).
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Overrides.Check
  ( CheckOverrideName (..),
    createCheckOverride,
    checkOverrideFromResult
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)
import           Control.Lens ((^.))
import           Control.Monad (foldM, unless)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable.WithIndex (FoldableWithIndex, ifoldrM)
import           Data.Functor.Compose (Compose(Compose))
import           Data.IORef (IORef, modifyIORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))
import qualified Data.Vector as Vec

import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Classes (IndexF)
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.TraversableFC.WithIndex (FoldableFCWithIndex, ifoldrMFC)

-- what4
import           What4.Interface (Pred)

-- crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Override

-- crucible-llvm
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.Intrinsics (LLVM, LLVMOverride(..), basic_llvm_override)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Constraints (Constraint, Constraints, ConstrainedShape(..), argConstraints, globalConstraints, ppConstraints)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleDecls, moduleTypes)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.FullType.CrucibleType (SomeIndex(SomeIndex), translateIndex, toCrucibleType)
import           UCCrux.LLVM.FullType.StorageType (toStorageType)
import           UCCrux.LLVM.FullType.Type (FullType(FTPtr), FullTypeRepr, MapToCrucibleType, ToCrucibleType, pointedToType, arrayElementType)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.Module (FuncSymbol, funcSymbol)
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, makePolymorphicLLVMOverride)
import           UCCrux.LLVM.Run.Result (BugfindingResult)
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Setup.Constraints (constraintToPred)
import qualified UCCrux.LLVM.Shape as Shape
{- ORMOLU_ENABLE -}

newtype CheckOverrideName = CheckOverrideName {getCheckOverrideName :: Text}
  deriving (Eq, Ord, Show)

declName :: L.Declare -> Text
declName decl =
  let L.Symbol name = L.decName decl
   in Text.pack name

-- TODO: Alignment...?
doLoad ::
  forall arch m sym ft.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr ft)) ->
  FullTypeRepr m ('FTPtr ft) ->
  IO (Pred sym, Maybe (Crucible.RegValue sym (ToCrucibleType arch ft)))
doLoad modCtx sym mem val fullTypeRepr =
  do let pointedToRepr = pointedToType (modCtx ^. moduleTypes) fullTypeRepr
         typeRepr = toCrucibleType modCtx pointedToRepr
     -- TODO Is this alignment right?
     partVal <-
       LLVMMem.loadRaw sym mem val (toStorageType pointedToRepr) noAlignment
     case partVal of
       LLVMMem.Err p -> return (p, Nothing)
       LLVMMem.NoErr p ptdToVal ->
         (p,) . Just <$> LLVMMem.unpackMemValue sym typeRepr ptdToVal


ifoldMapM ::
  FoldableWithIndex i t =>
  Monoid m =>
  Monad f =>
  (i -> a -> f m) ->
  t a ->
  f m
ifoldMapM f = ifoldrM (\i x acc -> fmap (<> acc) (f i x)) mempty

ifoldMapMFC ::
  FoldableFCWithIndex t =>
  Monoid m =>
  Monad g =>
  (forall x. IndexF (t f z) x -> f x -> g m) ->
  t f z ->
  g m
ifoldMapMFC f = ifoldrMFC (\i x acc -> fmap (<> acc) (f i x)) mempty

-- | Create a predicate that checks that a Crucible(-LLVM) value conforms to the
-- 'ConstrainedShape'.
--
-- TODO: Add selector for provenance
checkConstraints ::
  forall arch m sym ft.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  ConstrainedShape m ft ->
  FullTypeRepr m ft ->
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (Seq (Pred sym))
checkConstraints modCtx sym mem cShape fullTypeRepr val =
  case getConstrainedShape cShape of
    Shape.ShapeInt (Compose cs) -> constraintsToPreds fullTypeRepr cs val
    Shape.ShapeFloat (Compose cs) -> constraintsToPreds fullTypeRepr cs val
    Shape.ShapePtr (Compose cs) Shape.ShapeUnallocated ->
      constraintsToPreds fullTypeRepr cs val
    Shape.ShapePtr (Compose cs) (Shape.ShapeAllocated {}) ->
      constraintsToPreds fullTypeRepr cs val
    Shape.ShapePtr (Compose cs) (Shape.ShapeInitialized subShapes) ->
      do -- TODO: Is there code from Setup that helps with the other addresses?
         unless (Seq.length subShapes == 1) $
           Unimplemented.unimplemented
             "checkConstraints"
             Unimplemented.CheckConstraintsPtrArray
         (ptdToPred, mbPtdToVal) <- doLoad modCtx sym mem val fullTypeRepr
         let shape = ConstrainedShape (subShapes `Seq.index` 0)
         let ptdToRepr = pointedToType (modCtx ^. moduleTypes) fullTypeRepr
         subs <-
           case mbPtdToVal of
             Nothing -> pure Seq.empty
             Just ptdToVal ->
               checkConstraints modCtx sym mem shape ptdToRepr ptdToVal
         here <- constraintsToPreds fullTypeRepr cs val
         return (ptdToPred Seq.<| here <> subs)
    Shape.ShapeFuncPtr (Compose cs) -> constraintsToPreds fullTypeRepr cs val
    Shape.ShapeOpaquePtr (Compose cs) -> constraintsToPreds fullTypeRepr cs val
    Shape.ShapeArray (Compose cs) _ subShapes ->
      (<>)
      <$> constraintsToPreds fullTypeRepr cs val
      <*> ifoldMapM
            (\i shape ->
               checkConstraints
                 modCtx
                 sym
                 mem
                 (ConstrainedShape shape)
                 (arrayElementType fullTypeRepr)
                 (val Vec.! fromIntegral (Fin.finToNat i)))
            subShapes
    Shape.ShapeUnboundedArray (Compose cs) subShapes ->
      (<>)
      <$> constraintsToPreds fullTypeRepr cs val
      <*> ifoldMapM
            (\i shape ->
               checkConstraints
                 modCtx
                 sym
                 mem
                 (ConstrainedShape shape)
                 (arrayElementType fullTypeRepr)
                 (val Vec.! i))
            subShapes
    Shape.ShapeStruct (Compose cs) _ ->
      (<>)
      <$> constraintsToPreds fullTypeRepr cs val
      <*> Unimplemented.unimplemented
            "checkConstraints"
            Unimplemented.CheckConstraintsStruct

  where
    foldMapM :: forall t f m' a. Foldable t => Monoid m' => Monad f => (a -> f m') -> t a -> f m'
    foldMapM f = foldM (\acc -> fmap (<> acc) . f) mempty

    constraintsToPreds ::
      forall ft'.
      FullTypeRepr m ft' ->
      [Constraint m ft'] ->
      Crucible.RegValue sym (ToCrucibleType arch ft') ->
      IO (Seq (Pred sym))
    constraintsToPreds ftRepr cs v =
      foldMapM (\c -> Seq.singleton <$> constraintToPred modCtx sym c ftRepr v) cs

createCheckOverride ::
  forall arch p sym m argTypes ret blocks.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  AppContext ->
  ModuleContext m arch ->
  -- | Set of check overrides encountered during execution
  --
  -- TODO: Add constraint, selector for provenance
  IORef (Map CheckOverrideName [Pred sym]) ->
  -- | Function argument types
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  -- | Function contract to check
  Constraints m argTypes ->
  -- | Function implementation
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  -- | Name of function to override
  FuncSymbol m ->
  PolymorphicLLVMOverride arch p sym
createCheckOverride appCtx modCtx usedRef argFTys constraints cfg funcSym =
  let decl = modCtx ^. moduleDecls . funcSymbol funcSym
      name = declName decl
  in makePolymorphicLLVMOverride $
       basic_llvm_override $
         LLVMOverride
           { llvmOverride_declare = decl,
             llvmOverride_args = Crucible.cfgArgTypes cfg,
             llvmOverride_ret = Crucible.cfgReturnType cfg,
             llvmOverride_def =
               \mvar (sym :: sym) args ->
                 Override.modifyGlobal mvar $ \mem ->
                   do
                     liftIO $ (appCtx ^. log) Hi $ "Checking preconditions of " <> name
                     let pp = PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions
                     liftIO $ (appCtx ^. log) Hi "Constraints:"
                     liftIO $ (appCtx ^. log) Hi $ pp (ppConstraints constraints)

                     argCs <- liftIO $ getArgConstraints sym mem args
                     globCs <- liftIO $ getGlobalConstraints sym mem
                     let cs = argCs <> globCs
                     let nm = CheckOverrideName name
                     liftIO $
                       modifyIORef usedRef $
                         \m -> foldr (Map.insertWith (++) nm . (:[])) m cs
                     retEntry <- Crucible.callCFG cfg (Crucible.RegMap args)
                     return (Crucible.regValue retEntry, mem)
           }
  where
    getArgConstraints ::
      IsSymInterface sym =>
      sym ->
      LLVMMem.MemImpl sym ->
      Ctx.Assignment (Crucible.RegEntry sym) (MapToCrucibleType arch argTypes) ->
      IO (Seq (Pred sym))
    getArgConstraints sym mem args =
      ifoldMapMFC
         (\idx constraint ->
           do SomeIndex idx' Refl <-
                pure $
                  let sz = Ctx.size (constraints ^. argConstraints)
                  in translateIndex modCtx sz idx
              let arg = args Ctx.! idx'
              checkConstraints
                modCtx
                sym
                mem
                constraint
                (argFTys Ctx.! idx)
                (Crucible.regValue arg))
         (constraints ^. argConstraints)

    getGlobalConstraints ::
      IsSymInterface sym =>
      sym ->
      LLVMMem.MemImpl sym ->
      IO (Seq (Pred sym))
    getGlobalConstraints _sym _mem =
      ifoldMapM
        (Unimplemented.unimplemented
          "createCheckOverride"
          Unimplemented.CheckConstraintsGlobal)
        (constraints ^. globalConstraints)

-- | Create an override for checking deduced preconditions
checkOverrideFromResult ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  AppContext ->
  ModuleContext m arch ->
  IORef (Map CheckOverrideName [Pred sym]) ->
  -- | Function argument types
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  -- | Function implementation
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  -- | Name of function to override
  FuncSymbol m ->
  -- | Result from which to take constraints
  BugfindingResult m arch argTypes ->
  Maybe (PolymorphicLLVMOverride arch p sym)
checkOverrideFromResult appCtx modCtx ref argFTys cfg f result =
  case Result.summary result of
    Result.SafeWithPreconditions _bounds _unsound constraints ->
      Just $
        createCheckOverride
          appCtx
          modCtx
          ref
          argFTys
          constraints
          cfg
          f
    _ -> Nothing
