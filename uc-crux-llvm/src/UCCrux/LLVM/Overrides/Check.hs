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
on a function f (namely, 'Preconds') and makes an override that has the same
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

module UCCrux.LLVM.Overrides.Check
  ( CheckOverrideName (..),
    createCheckOverride,
    checkOverrideFromResult,
    CheckedConstraint(..),
    SomeCheckedConstraint(..),
    SomeCheckedConstraint'(..),
    CheckedCall,
    checkedCallContext,
    checkedCallArgs,
    checkedCallPreconds
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)
import           Control.Lens ((^.), (%~))
import           Control.Monad (foldM, unless)
import           Control.Monad.IO.Class (liftIO)
import           Data.Function ((&))
import           Data.Foldable.WithIndex (FoldableWithIndex, ifoldrM)
import           Data.Functor.Compose (Compose(Compose))
import           Data.IORef (IORef, modifyIORef)
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
import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.TraversableFC (fmapFC)
import           Data.Parameterized.TraversableFC.WithIndex (FoldableFCWithIndex, ifoldrMFC)
import           Data.Parameterized.Some (Some(Some), viewSome)
import qualified Data.Parameterized.Vector as PVec

-- what4
import           What4.Interface (Pred)

-- crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import           Lang.Crucible.Backend (IsSymInterface, IsSymBackend, backendGetSym)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Override

-- crucible-llvm
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.Intrinsics (LLVM, LLVMOverride(..), basic_llvm_override)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Constraints (Constraint, ShapeConstraint(Initialized), ConstrainedShape(..), ConstrainedTypedValue(..))
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleDecls, moduleTypes)
import           UCCrux.LLVM.Cursor (Selector, selectorCursor)
import qualified UCCrux.LLVM.Cursor as Cursor
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.FullType.CrucibleType (SomeIndex(SomeIndex), translateIndex)
import           UCCrux.LLVM.FullType.Type (FullType, FullTypeRepr, MapToCrucibleType, ToCrucibleType, pointedToType, arrayElementType)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import qualified UCCrux.LLVM.Mem as Mem
import           UCCrux.LLVM.Module (FuncSymbol, funcSymbol, getGlobalSymbol)
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, makePolymorphicLLVMOverride)
import           UCCrux.LLVM.Overrides.Stack (Stack, collectStack)
import           UCCrux.LLVM.Precondition (Preconds, argPreconds, globalPreconds, ppPreconds)
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

-- | A constraint, together with where it was applied and the resulting 'Pred'
-- it was \"compiled\" to.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data CheckedConstraint m sym (argTypes :: Ctx (FullType m)) inTy atTy
  = CheckedConstraint
      { -- | The 'Constraint' that was applied at this 'Selector' to yield this
        -- 'Pred'
        checkedConstraint :: Either (ShapeConstraint m atTy) (Constraint m atTy),
        -- | The location in an argument or global variable where this
        -- 'Constraint' was applied
        checkedSelector :: Selector m argTypes inTy atTy,
        -- | The \"compiled\"/applied form of the 'Constraint'
        checkedPred :: Pred sym
      }

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data SomeCheckedConstraint m sym (argTypes :: Ctx (FullType m)) =
  forall inTy atTy.
    SomeCheckedConstraint (CheckedConstraint m sym argTypes inTy atTy)

data SomeCheckedConstraint' m =
  forall sym argTypes inTy atTy.
    SomeCheckedConstraint' (CheckedConstraint m sym argTypes inTy atTy)

-- | This is what a check override (see 'createCheckOverride') records when it
-- is called during execution, consisting of the calling context, the arguments,
-- and the results of checking all of the constraints on arguments and global
-- variables.
--
-- TODO(lb): Might be nice to add the values of global variables that were
-- constrained.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data CheckedCall m sym arch (argTypes :: Ctx (FullType m)) =
  CheckedCall
    { -- | Call stack, including the checked function
      checkedCallContext :: Stack sym,
      -- | Function arguments
      checkedCallArgs :: Ctx.Assignment (Crucible.RegValue' sym) (MapToCrucibleType arch argTypes),
      checkedCallPreconds :: Seq (SomeCheckedConstraint m sym argTypes)
    }

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
checkPreconds ::
  forall arch m sym argTypes inTy atTy.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  -- | Selector for provenance information
  Selector m argTypes inTy atTy ->
  ConstrainedShape m atTy ->
  FullTypeRepr m atTy ->
  Crucible.RegValue sym (ToCrucibleType arch atTy) ->
  IO (Seq (Some (CheckedConstraint m sym argTypes inTy)))
checkPreconds modCtx sym mem selector cShape fullTypeRepr val =
  case getConstrainedShape cShape of
    Shape.ShapeInt (Compose cs) ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapeFloat (Compose cs) ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapePtr (Compose cs) Shape.ShapeUnallocated ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapePtr (Compose cs) Shape.ShapeAllocated{} ->
      -- TODO: How to actually tell if the pointer points to something of the
      -- right size? Might be something in MemModel.* that could help?
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapePtr (Compose cs) (Shape.ShapeInitialized subShapes) ->
      do -- TODO: Is there code from Setup that helps with the other addresses?
         -- (Look at 'pointerRange'?)
         unless (Seq.length subShapes == 1) $
           Unimplemented.unimplemented
             "checkPreconds"
             Unimplemented.CheckPrecondsPtrArray
         let mts = modCtx ^. moduleTypes
         (ptdToPred, mbPtdToVal) <- Mem.loadRaw' modCtx sym mem mts val fullTypeRepr
         let shape = ConstrainedShape (subShapes `Seq.index` 0)
         let ptdToRepr = pointedToType (modCtx ^. moduleTypes) fullTypeRepr
         let ptdToSelector = selector & selectorCursor %~ Cursor.deepenPtr mts
         subs <-
           case mbPtdToVal of
             Nothing -> pure Seq.empty
             Just ptdToVal ->
               checkPreconds modCtx sym mem ptdToSelector shape ptdToRepr ptdToVal
         here <- constraintsToSomePreds fullTypeRepr selector cs val
         let ptdToConstraint =
               CheckedConstraint
                 { checkedConstraint =
                     Left (Initialized (Seq.length subShapes)),
                   checkedSelector = selector,
                   checkedPred = ptdToPred
                 }
         return (Some ptdToConstraint Seq.<| here <> subs)
    Shape.ShapeFuncPtr (Compose cs) ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapeOpaquePtr (Compose cs) ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapeArray (Compose cs) _ subShapes ->
      (<>)
      <$> constraintsToSomePreds fullTypeRepr selector cs val
      <*> ifoldMapM
            (\i shape ->
               checkPreconds
                 modCtx
                 sym
                 mem
                 (selector &
                  selectorCursor %~
                  (\c ->
                    Fin.viewFin
                      (\i' -> Cursor.deepenArray i' (PVec.length subShapes) c)
                      i))
                 (ConstrainedShape shape)
                 (arrayElementType fullTypeRepr)
                 (val Vec.! fromIntegral (Fin.finToNat i)))
            subShapes
    Shape.ShapeUnboundedArray (Compose cs) subShapes ->
      (<>)
      <$> constraintsToSomePreds fullTypeRepr selector cs val
      <*> ifoldMapM
            (\i shape ->
               checkPreconds
                 modCtx
                 sym
                 mem
                 (Unimplemented.unimplemented
                    "checkPreconds"
                    Unimplemented.NonEmptyUnboundedSizeArrays)
                 (ConstrainedShape shape)
                 (arrayElementType fullTypeRepr)
                 (val Vec.! i))
            subShapes
    Shape.ShapeStruct (Compose cs) _ ->
      (<>)
      <$> constraintsToSomePreds fullTypeRepr selector cs val
      <*> Unimplemented.unimplemented
            "checkPreconds"
            Unimplemented.CheckPrecondsStruct

  where
    foldMapM :: forall t f m' a. Foldable t => Monoid m' => Monad f => (a -> f m') -> t a -> f m'
    foldMapM f = foldM (\acc -> fmap (<> acc) . f) mempty

    constraintsToSomePreds ::
      forall atTy'.
      FullTypeRepr m atTy' ->
      Selector m argTypes inTy atTy' ->
      [Constraint m atTy'] ->
      Crucible.RegValue sym (ToCrucibleType arch atTy') ->
      IO (Seq (Some (CheckedConstraint m sym argTypes inTy)))
    constraintsToSomePreds ftRepr selector_ cs v =
      fmap (fmap Some) (constraintsToPreds ftRepr selector_ cs v)

    constraintsToPreds ::
      forall atTy'.
      FullTypeRepr m atTy' ->
      Selector m argTypes inTy atTy' ->
      [Constraint m atTy'] ->
      Crucible.RegValue sym (ToCrucibleType arch atTy') ->
      IO (Seq (CheckedConstraint m sym argTypes inTy atTy'))
    constraintsToPreds ftRepr selector_ cs v =
      foldMapM
        (\c ->
          Seq.singleton . CheckedConstraint (Right c) selector_ <$>
            constraintToPred modCtx sym c ftRepr v)
        cs

-- TODO: Split out the part that simply wraps a call to an existing LLVM CFG
-- with additional Override actions before and after into its own module.

-- | Create an override which checks the given 'Preconds' during symbolic
-- execution (basically, compiles them to 'Pred's).
createCheckOverride ::
  forall arch p sym m argTypes ret blocks.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  AppContext ->
  ModuleContext m arch ->
  -- | When this override is called during symbolic execution, it will stash the
  -- predictes/constraints it checks (see 'CheckedCall') in this 'IORef'. The
  -- order of the calls will be the reverse of the order they were encountered
  -- during symbolic execution.
  IORef [CheckedCall m sym arch argTypes] ->
  -- | Function argument types
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  -- | Function contract to check
  Preconds m argTypes ->
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
               \mvar bak args ->
                 Override.modifyGlobal mvar $ \mem ->
                   do
                     let sym = backendGetSym bak
                     liftIO $ (appCtx ^. log) Hi $ "Checking preconditions of " <> name
                     let pp = PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions
                     liftIO $ (appCtx ^. log) Hi "Preconditions:"
                     liftIO $ (appCtx ^. log) Hi $ pp (ppPreconds constraints)
                     stack <- collectStack
                     argCs <- liftIO $ getArgPreconds sym mem args
                     globCs <- liftIO $ getGlobalPreconds bak mem
                     let cs = argCs <> globCs
                     let args' = fmapFC (Crucible.RV . Crucible.regValue) args
                     liftIO $
                       modifyIORef usedRef (CheckedCall stack args' cs:)
                     retEntry <- Crucible.callCFG cfg (Crucible.RegMap args)
                     return (Crucible.regValue retEntry, mem)
           }
  where
    getArgPreconds ::
      IsSymInterface sym =>
      sym ->
      LLVMMem.MemImpl sym ->
      Ctx.Assignment (Crucible.RegEntry sym) (MapToCrucibleType arch argTypes) ->
      IO (Seq (SomeCheckedConstraint m sym argTypes))
    getArgPreconds sym mem args =
      ifoldMapMFC
         (\idx constraint ->
           do SomeIndex idx' Refl <-
                pure $
                  let sz = Ctx.size (constraints ^. argPreconds)
                  in translateIndex modCtx sz idx
              let arg = args Ctx.! idx'
              let fTy = argFTys Ctx.! idx
              fmap (viewSome SomeCheckedConstraint) <$>
                checkPreconds
                  modCtx
                  sym
                  mem
                  (Cursor.SelectArgument idx (Cursor.Here fTy))
                  constraint
                  fTy
                  (Crucible.regValue arg))
         (constraints ^. argPreconds)

    getGlobalPreconds ::
      IsSymBackend sym bak =>
      bak ->
      LLVMMem.MemImpl sym ->
      IO (Seq (SomeCheckedConstraint m sym argTypes))
    getGlobalPreconds bak mem =
      let sym = backendGetSym bak in
      ifoldMapM
        (\gSymb (ConstrainedTypedValue globTy shape) ->
           do -- 'loadGlobal' will make some safety assertions, but if they fail
              -- that indicates a bug in UC-Crux or the constraints themselves
              -- rather than a constraint failure, so we don't collect them.
              glob <- Mem.loadGlobal modCtx bak mem globTy (getGlobalSymbol gSymb)
              fmap (viewSome SomeCheckedConstraint) <$>
                checkPreconds
                  modCtx
                  sym
                  mem
                  (Cursor.SelectGlobal gSymb (Cursor.Here globTy))
                  shape
                  globTy
                  glob
           )
        (constraints ^. globalPreconds)

-- | Create an override for checking deduced preconditions
checkOverrideFromResult ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  AppContext ->
  ModuleContext m arch ->
  -- | Predicates checked during simulation
  IORef [CheckedCall m sym arch argTypes] ->
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
