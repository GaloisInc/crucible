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

-- | A variant of 'Crucible.symbolicBranches'.
--
-- Useful when the branches use a 'Crucible.RegMap' of values of types @args@
-- that are unrelated to the argument types of the override (@args'@).
--
-- For convenience, passes the given 'Crucible.RegMap' of type @args@ directly
-- to the action taken in each branch, rather than requiring each branch to call
-- 'Crucible.getOverrideArgs' and @splitRegs@.
symbolicBranches' :: forall p sym ext rtp args args' res a.
  IsSymInterface sym =>
  -- | Argument values for the branches
  Crucible.RegMap sym args ->
  -- | Branches to consider
  [ ( What4.Pred sym
    , Crucible.RegMap sym args -> Crucible.OverrideSim p sym ext rtp (args' Ctx.<+> args) res a
    , Maybe What4.Position
    )
  ] ->
  Crucible.OverrideSim p sym ext rtp args' res a
symbolicBranches' args branches =
  do let argsSize = Crucible.regMapSize args
     args'Size <- Crucible.regMapSize <$> Crucible.getOverrideArgs
     let branches' =
           [ ( precond
             , -- Don't use args from outer scope directly (see warning on
               -- 'Crucible.symbolicBranches').
               do args'args <- Crucible.getOverrideArgs
                  let (_, safeArgs) = splitRegs args'Size argsSize args'args
                  action safeArgs
             , pos
             )
           | (precond, action, pos) <- branches
           ]
     Crucible.symbolicBranches args branches'
  where
    splitRegs ::
      Ctx.Size ctx ->
      Ctx.Size ctx' ->
      Crucible.RegMap sym (ctx Ctx.<+> ctx') ->
      (Crucible.RegMap sym ctx, Crucible.RegMap sym ctx')
    splitRegs sz sz' (Crucible.RegMap m) =
      (Crucible.RegMap (Ctx.take sz sz' m), Crucible.RegMap (Ctx.drop sz sz' m))

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
             , -- Can't use 'args' in this block, see warning on
               -- 'Crucible.symbolicBranches'.
               \(Crucible.RegMap args') ->
                 applyPost bak modCtx tracker funcSymb fsRep mvar spec args'
             , Nothing
             )
           | (spec, precond) <- toList specs'
           ]

     -- Add a fallback branch that (depending on the Spec) either fails or
     -- applies a minimal postcondition.
     let fallbackBranch =
           ( What4.truePred sym
           , -- Can't use 'args' in this block, see warning on
             -- 'Crucible.symbolicBranches'.
             \_args ->
               -- TODO(lb): this behavior should depend on spec config, see TODO
               -- on 'Specs'
               do Crucible.overrideError (Crucible.GenericSimError "No spec applied!")
           , Nothing
           )

     let branches = specBranches ++ [fallbackBranch]
     symbolicBranches' (Crucible.RegMap args) branches
