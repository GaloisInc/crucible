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
    CheckedCall,
    checkedCallContext,
    checkedCallArgs,
    checkedCallPreconds
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)
import           Control.Lens ((^.), to)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable.WithIndex (FoldableWithIndex, ifoldrM)
import           Data.IORef (IORef, modifyIORef)
import           Data.Sequence (Seq)
import           Data.Text (Text)
import qualified Data.Text as Text

import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (fmapFC)
import           Data.Parameterized.Some (viewSome)

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
import           UCCrux.LLVM.Check (SomeCheckedConstraint(..), checkConstrainedShape, checkConstrainedShapes)
import           UCCrux.LLVM.Constraints (ConstrainedTypedValue(..))
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleDecls, moduleTypes)
import qualified UCCrux.LLVM.Cursor as Cursor
import           UCCrux.LLVM.FullType.Type (FullType, FullTypeRepr, MapToCrucibleType, dataLayout)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import qualified UCCrux.LLVM.Mem as Mem
import           UCCrux.LLVM.Module (FuncSymbol, funcSymbol, getGlobalSymbol)
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, makePolymorphicLLVMOverride)
import           UCCrux.LLVM.Overrides.Stack (Stack, collectStack)
import           UCCrux.LLVM.Precondition (Preconds, argPreconds, globalPreconds, ppPreconds)
import           UCCrux.LLVM.Run.Result (BugfindingResult)
import qualified UCCrux.LLVM.Run.Result as Result
{- ORMOLU_ENABLE -}

newtype CheckOverrideName = CheckOverrideName {getCheckOverrideName :: Text}
  deriving (Eq, Ord, Show)

declName :: L.Declare -> Text
declName decl =
  let L.Symbol name = L.decName decl
   in Text.pack name

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

-- | Helper, not exported
ifoldMapM ::
  FoldableWithIndex i t =>
  Monoid m =>
  Monad f =>
  (i -> a -> f m) ->
  t a ->
  f m
ifoldMapM f = ifoldrM (\i x acc -> fmap (<> acc) (f i x)) mempty

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
      checkConstrainedShapes modCtx sym mem argFTys (constraints ^. argPreconds) args

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
              let dl = modCtx ^. moduleTypes . to dataLayout
              glob <- Mem.loadGlobal modCtx dl bak mem globTy (getGlobalSymbol gSymb)
              fmap (viewSome SomeCheckedConstraint) <$>
                checkConstrainedShape
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
