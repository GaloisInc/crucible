-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.RegRewrite
-- Description      : Operations for manipulating registerized CFGs
-- Copyright        : (c) Galois, Inc 2014-2018
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- A rewrite engine for registerized CFGs.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
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
import           Data.Foldable ( toList )
import           Data.Sequence ( Seq )
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import           What4.ProgramLoc

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.CFG.Reg
import           Lang.Crucible.Types

------------------------------------------------------------------------
-- Public interface

-- | Add statements to each block in a CFG according to the given
-- instrumentation functions. See the 'Rewriter' monad for the
-- operations provided for adding code.
annotateCFGStmts :: TraverseExt ext
                 => u
                 -- ^ Initial user state
                 -> (Posd (Stmt ext s) -> Rewriter ext s ret u ())
                 -- ^ Action to run on each non-terminating statement;
                 -- must explicitly add the original statement back if
                 -- desired
                 -> (Posd (TermStmt s ret) -> Rewriter ext s ret u ())
                 -- ^ Action to run on each terminating statement
                 -> CFG ext s init ret
                 -- ^ Graph to rewrite
                 -> CFG ext s init ret
annotateCFGStmts u fS fT cfg =
  runRewriter u cfg $
    do blocks' <- mapM (annotateBlockStmts fS fT) (cfgBlocks cfg)
       newCFG cfg (concat blocks')

-- | Monad providing operations for modifying a basic block by adding
-- statements and/or splicing in conditional braches. Also provides a
-- 'MonadState' instance for storing user state.
newtype Rewriter ext s (ret :: CrucibleType) u a =
  Rewriter (RWS () (Seq (ComplexStmt ext s)) (RewState u) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Seq (ComplexStmt ext s)))

instance MonadState u (Rewriter ext s ret u) where
  get = Rewriter $ gets rsUserState
  put u = Rewriter $ modify $ \s -> s { rsUserState = u }

-- | Add a new statement at the current position.
addStmt :: Posd (Stmt ext s) -> Rewriter ext s ret u ()
addStmt stmt = tell (Seq.singleton (Stmt stmt))

-- | Add a new statement at the current position, marking it as
-- internally generated.
addInternalStmt :: Stmt ext s -> Rewriter ext s ret u ()
addInternalStmt = addStmt . Posd InternalPos

-- | Add a conditional at the current position. This will cause the
-- current block to end and new blocks to be generated for the two
-- branches and the remaining statements in the original block.
ifte :: Atom s BoolType
       -> Rewriter ext s ret u ()
       -> Rewriter ext s ret u ()
       -> Rewriter ext s ret u ()
ifte atom thn els =
  do (~(), thnSeq) <- gather thn
     (~(), elsSeq) <- gather els
     tell $ Seq.singleton (IfThenElse atom thnSeq elsSeq)

-- | Create a new atom with a freshly allocated id. The id will not
-- have been used anywhere in the original CFG.
freshAtom :: TypeRepr tp -> Rewriter ext s ret u (Atom s tp)
freshAtom tp =
  do i <- Rewriter $ gets rsNextAtomID
     Rewriter $ modify $ \s -> s { rsNextAtomID = i + 1 }
     return $ Atom { atomPosition = InternalPos
                   , atomId = i
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

data RewState u = RewState { rsNextAtomID :: !Int
                           , rsNextLabelID :: !Int
                           , rsUserState :: !u }

data ComplexStmt ext s
  = Stmt (Posd (Stmt ext s))
  | IfThenElse (Atom s BoolType)
               (Seq (ComplexStmt ext s))
               (Seq (ComplexStmt ext s))

initState :: u -> CFG ext s init ret -> RewState u
initState u cfg = RewState { rsNextAtomID = cfgNextValue cfg
                           , rsNextLabelID = cfgNextLabel cfg
                           , rsUserState = u }

runRewriter :: u -> CFG ext s init ret -> Rewriter ext s ret u a -> a
runRewriter u cfg (Rewriter f) =
  case runRWS f () (initState u cfg) of (a, _, _) -> a

freshLabel :: Rewriter ext s ret u (Label s)
freshLabel =
  do i <- Rewriter $ gets rsNextLabelID
     Rewriter $ modify $ \s -> s { rsNextLabelID = i + 1 }
     return $ Label { labelInt = i }

-- | Return the output of a writer action without passing it onward.
gather :: MonadWriter w m => m a -> m (a, w)
gather m = censor (const mempty) $ listen m

------------------------------------------------------------------------
-- Implementation

newCFG :: CFG ext s init ret
       -> [Block ext s ret]
       -> Rewriter ext s ret u (CFG ext s init ret)
newCFG cfg blocks =
  do nextAtomID <- Rewriter $ gets rsNextAtomID
     return $ cfg { cfgBlocks = blocks
                  , cfgNextValue = nextAtomID }

annotateBlockStmts :: TraverseExt ext
                   => (Posd (Stmt ext s) -> Rewriter ext s ret u ())
                   -> (Posd (TermStmt s ret) -> Rewriter ext s ret u ())
                   -> Block ext s ret
                   -> Rewriter ext s ret u [Block ext s ret]
annotateBlockStmts fS fT block =
  do -- Step 1
     stmts <- annotateAsComplexStmts fS fT block
     -- Step 2
     rebuildBlock stmts block

annotateAsComplexStmts :: (Posd (Stmt ext s) -> Rewriter ext s ret u ())
                       -> (Posd (TermStmt s ret) -> Rewriter ext s ret u ())
                       -> Block ext s ret
                       -> Rewriter ext s ret u (Seq (ComplexStmt ext s))
annotateAsComplexStmts fS fT block =
  do (~(), stmts) <- gather $
       do mapM_ fS (blockStmts block)
          fT (blockTerm block)
     return stmts

rebuildBlock :: TraverseExt ext
             => Seq (ComplexStmt ext s)
             -> Block ext s ret
             -> Rewriter ext s ret u [Block ext s ret]
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
       -> Rewriter ext s ret u (Seq (Block ext s ret))
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
