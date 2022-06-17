{-
Module           : UCCrux.LLVM.Specs.Apply
Description      : Apply collections of specifications for LLVM functions
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

TODO(lb): Improve tracking + logging of when specs failed to apply, and why.
Should be easy enough given the information in 'CheckedConstraint'.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Specs.Apply
  ( applySpecs
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (zip)

import qualified Control.Lens as Lens
import           Control.Monad.IO.Class (liftIO)
import           Data.Maybe (fromMaybe)
import           Data.Foldable (toList)
import           Data.IORef (IORef)

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx

-- what4
import qualified What4.Interface as What4

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, Mem, MemImpl, MemOptions)
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Check (checkConstrainedShapes, SomeCheckedConstraint(..), CheckedConstraint(checkedPred))
import           UCCrux.LLVM.Context.Module (ModuleContext)
import           UCCrux.LLVM.ExprTracker (ExprTracker)
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.FullType.Type (FullTypeRepr, MapToCrucibleType)
import           UCCrux.LLVM.Module (FuncSymbol)
import           UCCrux.LLVM.Postcondition.Apply (applyPostcond)
import qualified UCCrux.LLVM.Postcondition.Type as Post
import           UCCrux.LLVM.Specs.Type (Specs)
import qualified UCCrux.LLVM.Specs.Type as Spec
{- ORMOLU_ENABLE -}

-- | Collapse all the preconditions of a 'Spec' to a single predicate
matchPreconds ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  ModuleContext m arch ->
  sym ->
  MemImpl sym ->
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Spec.SpecPreconds m argTypes ->
  Ctx.Assignment (Crucible.RegEntry sym) (MapToCrucibleType arch argTypes) ->
  IO (What4.Pred sym)
matchPreconds modCtx sym mem argFTys preconds args =
  do constraints <-
       checkConstrainedShapes modCtx sym mem argFTys (Spec.specArgPreconds preconds) args
     What4.andAllOf
       sym
       (Lens.folding (fmap (\(SomeCheckedConstraint c) -> checkedPred c)))
       constraints

-- | Apply a spec postcondition, modifying memory and creating a return value
--
-- If the postcondition of the spec is 'Nothing', apply 'Post.minimalPostcond'.
applyPost ::
  forall m arch sym bak fs va mft args argTypes p ext r cargs ret.
  Crucible.IsSymBackend sym bak =>
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  (fs ~ 'FS.FuncSig va mft args) =>
  bak ->
  ModuleContext m arch ->
  -- | Track origins of created values
  IORef (ExprTracker m sym argTypes) ->
  -- | Function name
  FuncSymbol m ->
  -- | Function type
  FS.FuncSigRepr m fs ->
  -- | LLVM memory variable
  Crucible.GlobalVar Mem ->
  Spec.Spec m fs ->
  -- | Arguments to function
  Ctx.Assignment (Crucible.RegEntry sym) (MapToCrucibleType arch args) ->
  Crucible.OverrideSim p sym ext r cargs ret
    (Crucible.RegValue sym (FS.ReturnTypeToCrucibleType arch mft))
applyPost bak modCtx tracker funcSymb fsRep mvar spec args =
  do FS.FuncSigRepr _ _ retTy <- return fsRep
     Spec.Spec _ _ specPost _ <- return spec
     let post = fromMaybe (Post.minimalPostcond fsRep) specPost
     Crucible.modifyGlobal mvar $ \mem ->
       liftIO (applyPostcond bak modCtx tracker funcSymb post retTy mem args)

-- | Apply a collection of specs (a 'Specs') to the current program state.
--
-- Creates one symbolic branches per spec, as described on the Haddock for
-- 'Specs' the semantics is that the first spec with a matching precondition has
-- its postcondition applied to mutate memory and supply a return value.
applySpecs ::
  forall m arch sym bak fs va mft args argTypes p ext r cargs ret.
  ArchOk arch =>
  HasLLVMAnn sym =>
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  (fs ~ 'FS.FuncSig va mft args) =>
  Crucible.IsSymBackend sym bak =>
  -- | Symbolic backend
  bak ->
  ModuleContext m arch ->
  -- | Track origins of created values
  IORef (ExprTracker m sym argTypes) ->
  -- | Function name
  FuncSymbol m ->
  -- | Function specs
  Specs m fs ->
  -- | Function type
  FS.FuncSigRepr m fs ->
  -- | LLVM memory variable
  Crucible.GlobalVar Mem ->
  -- | Arguments to function
  Ctx.Assignment (Crucible.RegEntry sym) (MapToCrucibleType arch args) ->
  Crucible.OverrideSim p sym ext r cargs ret
    (Crucible.RegValue sym (FS.ReturnTypeToCrucibleType arch mft))
applySpecs bak modCtx tracker funcSymb specs fsRep mvar args =
  do FS.FuncSigRepr _ argTys _ <- return fsRep
     let sym = Crucible.backendGetSym bak

     -- Collapse preconditions into predicates
     mem <- Crucible.readGlobal mvar
     let matchPre (Spec.Spec specPre _ _ _) =
           matchPreconds modCtx sym mem argTys specPre args
     specs' <-
       traverse (\s -> (s,) <$> liftIO (matchPre s)) (Spec.getSpecs specs)

     -- Create one symbolic branch per Spec, conditioned on the preconditions
     let specBranches =
           [ ( precond
             , applyPost bak modCtx tracker funcSymb fsRep mvar spec args
             , Nothing
             )
           | (spec, precond) <- toList specs'
           ]

     -- Add a fallback branch that (depending on the Spec) either fails or
     -- applies a minimal postcondition.
     let fallbackBranch =
           ( What4.truePred sym
           , liftIO $ do
               -- TODO(lb): this behavior should depend on spec config, see TODO
               -- on 'Specs'
               Crucible.addFailedAssertion
                 bak
                 (Crucible.GenericSimError "No spec applied!")
           , Nothing
           )

     let branches = specBranches ++ [fallbackBranch]
     Crucible.symbolicBranches Crucible.emptyRegMap branches
