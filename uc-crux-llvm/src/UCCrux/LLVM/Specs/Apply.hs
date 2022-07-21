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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

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
import qualified What4.ProgramLoc as What4

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator.RegMap as Crucible
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

-- | Collapse all the preconditions of a 'Spec' to a single predicate.
--
-- The predicate denotes whether or not the precondition holds in the given
-- state, where a state is the arguments, ('Ctx.Assignment' of
-- 'Crucible.RegEntry') plus the LLVM memory ('MemImpl').
--
-- Used in 'applySpecs' to construct the predicates determining which spec's
-- postcondition gets applied, i.e., the predicates governing a chain of
-- symbolic branches.
matchPreconds ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  ModuleContext m arch ->
  sym ->
  -- | LLVM memory
  MemImpl sym ->
  -- | Types of function arguments
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  -- | Preconditions over arguments and memory
  Spec.SpecPreconds m argTypes ->
  -- | Arguments to function
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

-- | Like 'nondetBranches', but with a fallback case.
--
-- The fallback case has a branch condition equivalent to the negation of the
-- disjunction of the branch conditions of all the supplied branches; i.e., it
-- is taken just when none of the other branches are.
nondetBranchesWithFallback :: forall p sym ext rtp args new_args res a.
  IsSymInterface sym =>
  -- | Argument values for the branches
  Crucible.RegMap sym new_args  ->
  -- | Branches to consider
  [ ( What4.Pred sym
    , Crucible.OverrideSim p sym ext rtp (args Ctx.<+> new_args) res a
    , Maybe What4.Position
    )
  ] ->
  -- | Fallback branch
  Crucible.OverrideSim p sym ext rtp (args Ctx.<+> new_args) res a ->
  Crucible.OverrideSim p sym ext rtp args res a
nondetBranchesWithFallback newArgs branches fallbackBranch =
  do sym <- Crucible.getSymInterface
     orPred <- liftIO $ What4.orOneOf sym Lens.folded [p | (p, _, _) <- branches]
     fallbackPred <- liftIO $ What4.notPred sym orPred
     let p = Just (What4.OtherPos "fallback branch")
     Crucible.nondetBranches newArgs ((fallbackPred, fallbackBranch, p):branches)

-- | Apply a collection of specs (a 'Specs') to the current program state.
--
-- Creates one symbolic branch per spec; as described on the Haddock for
-- 'Specs' the semantics is that every spec with a true precondition has its
-- postcondition applied to mutate memory and supply a return value.
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
  do -- Create one symbolic branch per Spec, conditioned on the preconditions
     FS.FuncSigRepr _ argTys _ <- return fsRep
     let sym = Crucible.backendGetSym bak
     mem <- Crucible.readGlobal mvar
     branches <-
       mapM (specToBranch sym mem argTys) (toList (Spec.getSpecs specs))

     let reason = Crucible.GenericSimError "No spec applied!"
     let err = Crucible.overrideError reason
     -- TODO(lb): Whether or not to error in the fallback case should depend on
     -- spec config, see TODO on 'Specs'
     let fallback = err

     nondetBranchesWithFallback (Crucible.RegMap args) branches fallback

  where
    splitRegs ::
      Ctx.Size ctx ->
      Ctx.Size ctx' ->
      Crucible.RegMap sym (ctx Ctx.<+> ctx') ->
      (Crucible.RegMap sym ctx, Crucible.RegMap sym ctx')
    splitRegs sz sz' (Crucible.RegMap m) =
      (Crucible.RegMap (Ctx.take sz sz' m), Crucible.RegMap (Ctx.drop sz sz' m))

    withSplitOverrideArgs ::
      Ctx.Size old_args ->
      Ctx.Size new_args ->
      (forall args'.
       Crucible.RegMap sym old_args ->
       Crucible.RegMap sym new_args ->
       Crucible.OverrideSim p sym ext rtp args' res a) ->
      Crucible.OverrideSim p sym ext rtp (old_args Ctx.<+> new_args) res a
    withSplitOverrideArgs oldSz newSz k =
      do (args_, new_args) <- splitRegs oldSz newSz <$> Crucible.getOverrideArgs
         k args_ new_args

    -- Convert a Spec into a branch for 'nondetBranches'
    specToBranch sym mem argTys spec@(Spec.Spec specPre _ _ _) =
      do precond <- liftIO (matchPreconds modCtx sym mem argTys specPre args)
         let argsSize = Ctx.size args
         cargsSize <- Crucible.regMapSize <$> Crucible.getOverrideArgs
         return
           ( precond
           , -- Can't use 'args' in this block, see warning on
             -- 'Crucible.nondetBranches'.
             withSplitOverrideArgs cargsSize argsSize $
               \_ (Crucible.RegMap safeArgs) ->
                 applyPost bak modCtx tracker funcSymb fsRep mvar spec safeArgs
           , Nothing  -- position
           )
