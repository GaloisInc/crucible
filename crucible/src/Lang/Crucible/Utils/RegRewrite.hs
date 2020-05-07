-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.RegRewrite
-- Description      : Operations for manipulating registerized CFGs
-- Copyright        : (c) Galois, Inc 2014-2018
-- License          : BSD3
-- Maintainer       : Luke Maurer <lukemaurer@galois.com>
-- Stability        : provisional
--
-- A rewrite engine for registerized CFGs.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Utils.RegRewrite
  ( -- * Main interface
    annotateCFGStmts
    -- * Annotation monad
  , Rewriter
  , addStmt
  , addInternalStmt
  , ifte
  , freshAtom
  ) where

import           Control.Monad.RWS.Strict
import           Control.Monad.State.Strict ( StateT, evalStateT )
import           Control.Monad.ST ( ST, runST )
import           Data.Foldable ( toList )
import           Data.Parameterized.Map ( MapF )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce ( Nonce, NonceGenerator, freshNonce
                                          , newSTNonceGenerator )
import           Data.Parameterized.Some ( Some(Some) )
import           Data.Sequence ( Seq )
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.CFG.Reg
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Types

------------------------------------------------------------------------
-- Public interface

-- | Add statements to each block in a CFG according to the given
-- instrumentation functions. See the 'Rewriter' monad for the
-- operations provided for adding code.
annotateCFGStmts :: TraverseExt ext
                 => u
                 -- ^ Initial user state
                 -> (forall s h. Posd (Stmt ext s) -> Rewriter ext h s ret u ())
                 -- ^ Action to run on each non-terminating statement;
                 -- must explicitly add the original statement back if
                 -- desired
                 -> (forall s h. Posd (TermStmt s ret) -> Rewriter ext h s ret u ())
                 -- ^ Action to run on each terminating statement
                 -> SomeCFG ext init ret
                 -- ^ Graph to rewrite
                 -> SomeCFG ext init ret
annotateCFGStmts u fS fT (SomeCFG cfg) =
  runRewriter u $
    do cfg1 <- renameAll cfg
       blocks' <- mapM (annotateBlockStmts fS fT) (cfgBlocks cfg1)
       SomeCFG <$> newCFG cfg1 (concat blocks')

-- | Monad providing operations for modifying a basic block by adding
-- statements and/or splicing in conditional braches. Also provides a
-- 'MonadState' instance for storing user state.
newtype Rewriter ext h s (ret :: CrucibleType) u a =
  Rewriter (RWST (NonceGenerator (ST h) s)
                 (Seq (ComplexStmt ext s))
                 u (ST h) a)
  deriving ( Functor, Applicative, Monad, MonadState u
           , MonadWriter (Seq (ComplexStmt ext s))
           )

-- | Add a new statement at the current position.
addStmt :: Posd (Stmt ext s) -> Rewriter ext h s ret u ()
addStmt stmt = tell (Seq.singleton (Stmt stmt))

-- | Add a new statement at the current position, marking it as
-- internally generated.
addInternalStmt :: Stmt ext s -> Rewriter ext h s ret u ()
addInternalStmt = addStmt . Posd InternalPos

-- | Add a conditional at the current position. This will cause the
-- current block to end and new blocks to be generated for the two
-- branches and the remaining statements in the original block.
ifte :: Atom s BoolType
       -> Rewriter ext h s ret u ()
       -> Rewriter ext h s ret u ()
       -> Rewriter ext h s ret u ()
ifte atom thn els =
  do (~(), thnSeq) <- gather thn
     (~(), elsSeq) <- gather els
     tell $ Seq.singleton (IfThenElse atom thnSeq elsSeq)

-- | Create a new atom with a freshly allocated id. The id will not
-- have been used anywhere in the original CFG.
freshAtom :: TypeRepr tp -> Rewriter ext h s ret u (Atom s tp)
freshAtom tp =
  do ng <- Rewriter $ ask
     n <- Rewriter $ lift $ freshNonce ng
     return $ Atom { atomPosition = InternalPos
                   , atomId = n
                   , atomSource = Assigned
                   , typeOfAtom = tp }

------------------------------------------------------------------------
-- Monad
--
-- For each block, rewriting occurs in two stages:
--
-- 1. Generate a sequence of "complex statements", each of which may
--    be an internal if-then-else.
-- 2. Rebuild the block from the complex statements, creating
--    additional blocks for internal control flow.
--
-- Step 1 occurs through a simple writer monad, leaving the nasty details
-- of block mangling to step 2.

data ComplexStmt ext s
  = Stmt (Posd (Stmt ext s))
  | IfThenElse (Atom s BoolType)
               (Seq (ComplexStmt ext s))
               (Seq (ComplexStmt ext s))

runRewriter :: forall u ext ret a
             . u -> (forall h s. Rewriter ext h s ret u a) -> a
runRewriter u m = runST $ do
  Some ng <- newSTNonceGenerator
  case m of
    -- Have to do this pattern match *after* unpacking the Some from
    -- newSTNonceGenerator for obscure reasons involving Skolem
    -- functions
    Rewriter f -> do
      (a, _, _) <- runRWST f ng u
      return a

freshLabel :: forall ext h s ret u. Rewriter ext h s ret u (Label s)
freshLabel =
  do ng <- Rewriter $ ask
     n <- Rewriter $ lift $ freshNonce ng
     return $ Label { labelId = n }

-- | Return the output of a writer action without passing it onward.
gather :: MonadWriter w m => m a -> m (a, w)
gather m = censor (const mempty) $ listen m

------------------------------------------------------------------------
-- Implementation

-- Give fresh names to everything.  The only point of this is that the
-- new names come from a known nonce generator, so we can now generate
-- more names.  We do this in a separate pass up front so that we
-- don't have to juggle two namespaces afterward.
renameAll :: forall s0 s ext init ret h u
           . ( TraverseExt ext )
          => CFG ext s0 init ret
          -> Rewriter ext h s ret u (CFG ext s init ret)
renameAll cfg = do
  ng <- Rewriter $ ask
  Rewriter $ lift $ evalStateT (substCFG (rename ng) cfg) MapF.empty
  where
    rename :: NonceGenerator (ST h) s
           -> Nonce s0 (tp :: CrucibleType)
#if !MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
           -> StateT (MapF (Nonce s0) (Nonce s)) (ST h) (Nonce s tp)
#else
           -> StateT (MapF @CrucibleType (Nonce s0) (Nonce s)) (ST h) (Nonce s tp)
#endif
    rename ng n = do
      mapping <- get
      case MapF.lookup n mapping of
        Just n' ->
          return n'
        Nothing -> do
          n' <- lift $ freshNonce ng
          modify (MapF.insert n n')
          return n'

newCFG :: CFG ext s init ret
       -> [Block ext s ret]
       -> Rewriter ext h s ret u (CFG ext s init ret)
newCFG cfg blocks = do
  return $ cfg { cfgBlocks = blocks }

annotateBlockStmts :: TraverseExt ext
                   => (Posd (Stmt ext s) -> Rewriter ext h s ret u ())
                   -> (Posd (TermStmt s ret) -> Rewriter ext h s ret u ())
                   -> Block ext s ret
                   -> Rewriter ext h s ret u [Block ext s ret]
annotateBlockStmts fS fT block =
  do -- Step 1
     stmts <- annotateAsComplexStmts fS fT block
     -- Step 2
     rebuildBlock stmts block

annotateAsComplexStmts :: (Posd (Stmt ext s) -> Rewriter ext h s ret u ())
                       -> (Posd (TermStmt s ret) -> Rewriter ext h s ret u ())
                       -> Block ext s ret
                       -> Rewriter ext h s ret u (Seq (ComplexStmt ext s))
annotateAsComplexStmts fS fT block =
  do (~(), stmts) <- gather $
       do mapM_ fS (blockStmts block)
          fT (blockTerm block)
     return stmts

rebuildBlock :: TraverseExt ext
             => Seq (ComplexStmt ext s)
             -> Block ext s ret
             -> Rewriter ext h s ret u [Block ext s ret]
rebuildBlock stmts block =
  toList <$> go stmts Seq.empty Seq.empty
     (blockID block) (blockExtraInputs block) (blockTerm block)
  where
    go :: TraverseExt ext
       => Seq (ComplexStmt ext s) -- Statements to process
       -> Seq (Posd (Stmt ext s)) -- Statements added to current block
       -> Seq (Block ext s ret)   -- Blocks created so far
       -> BlockID s               -- Id of current block
       -> ValueSet s              -- Extra inputs to current block
       -> Posd (TermStmt s ret)   -- Terminal statement of current block
       -> Rewriter ext h s ret u (Seq (Block ext s ret))
    go s accStmts accBlocks bid ext term = case s of
      Seq.Empty ->
        return $ accBlocks Seq.|> mkBlock bid ext accStmts term
      (Stmt stmt Seq.:<| s') ->
        go s' (accStmts Seq.|> stmt) accBlocks bid ext term
      (IfThenElse a thn els Seq.:<| s') ->
        do thnLab <- freshLabel
           elsLab <- freshLabel
           newLab <- freshLabel
           -- End the block, terminating with a branch statement
           let branch = Posd InternalPos (Br a thnLab elsLab)
               thisBlock = mkBlock bid ext accStmts branch
           -- Make the branches into (sets of) blocks
           let jump = Posd InternalPos (Jump newLab)
           thnBlocks <-
             go thn Seq.empty Seq.empty (LabelID thnLab) Set.empty jump
           elsBlocks <-
             go els Seq.empty Seq.empty (LabelID elsLab) Set.empty jump
           -- Keep going with a new, currently empty block
           let accBlocks' = (accBlocks Seq.|> thisBlock) Seq.><
                            thnBlocks Seq.>< elsBlocks
           go s' Seq.empty accBlocks' (LabelID newLab) Set.empty term
