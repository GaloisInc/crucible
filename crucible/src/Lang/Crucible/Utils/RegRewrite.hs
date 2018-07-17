-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.RegRewrite
-- Description      : Operations for manipulating registerized CFGs
-- Copyright        : (c) Galois, Inc 2014-2018
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- A rewrite engine for registerized CFGs. Currently just supports
-- changing blocks by adding statements in the middle; blocks can't be
-- created, removed, or otherwise altered.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
module Lang.Crucible.Utils.RegRewrite
  ( -- * Main interface
    annotateCFGStmts
    -- * Annotation monad
  , Annotator
  , addStmtBefore
  , addStmtAfter
  , freshAtom
  ) where

import           Control.Monad.State.Strict
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import           What4.ProgramLoc

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.CFG.Reg
import           Lang.Crucible.Types

------------------------------------------------------------------------
-- Public interface

-- | Add statements to each block in a CFG according to the given
-- instrumentation functions. See the 'Annotator' monad for the
-- operations provided for adding code.
annotateCFGStmts :: TraverseExt ext
                 => (Stmt ext s -> Annotator ext s ret ())
                 -- ^ Action to run on each non-terminating statement
                 -> (TermStmt s ret -> Annotator ext s ret ())
                 -- ^ Action to run on each terminating statement
                 -> CFG ext s init ret
                 -- ^ Graph to rewrite
                 -> CFG ext s init ret
annotateCFGStmts fS fT cfg =
  runAnnotator cfg $
    do blocks' <- mapM (annotateBlockStmts fS fT) (cfgBlocks cfg)
       newCFG cfg blocks'

-- | Monad providing operations for adding statements to a basic
-- block. There is implicitly a current statement that has been
-- matched, so that new statements can be added before or after the
-- current statement.
newtype Annotator ext s (ret :: CrucibleType) a =
  Annotator (State (AnnState ext s ret) a)
  deriving ( Functor, Applicative, Monad, MonadState (AnnState ext s ret) )

-- | Add a new statement, immediately preceding the current statement.
addStmtBefore :: Stmt ext s -> Annotator ext s ret ()
addStmtBefore stmt =
  modify $ \s -> s { asStmtsBefore = asStmtsBefore s Seq.:|>
                                     Posd InternalPos stmt }

-- | Add a new statement, immediately following the current statement
-- (and any statements added by previous calls).
addStmtAfter :: Stmt ext s -> Annotator ext s ret ()
addStmtAfter stmt =
  modify $ \s -> s { asStmtsAfter = asStmtsAfter s Seq.:|>
                                    Posd InternalPos stmt }

-- | Create a new atom with a freshly allocated id. The id will not
-- have been used anywhere in the original CFG.
freshAtom :: TypeRepr tp -> Annotator ext s ret (Atom s tp)
freshAtom tp =
  do i <- gets asNextAtomId
     modify $ \s -> s { asNextAtomId = i + 1 }
     return $ Atom { atomPosition = InternalPos
                   , atomId = i
                   , atomSource = Assigned
                   , typeOfAtom = tp }

------------------------------------------------------------------------
-- Monad

data AnnState ext s (ret :: CrucibleType) =
  AnnState { asStmtsBefore :: !(Seq (Posd (Stmt ext s)))
           , asStmtsAfter  :: !(Seq (Posd (Stmt ext s)))
           , asNextAtomId  :: !Int }

initState :: CFG ext s init ret -> AnnState ext s ret
initState cfg = AnnState { asStmtsBefore = Seq.Empty
                         , asStmtsAfter = Seq.Empty
                         , asNextAtomId = cfgNextValue cfg }

runAnnotator :: CFG ext s init ret -> Annotator ext s ret a -> a
runAnnotator cfg (Annotator f) = fst $ runState f (initState cfg)

clearStmts :: Annotator ext s ret ()
clearStmts =
  modify $ \s -> s { asStmtsBefore = Seq.Empty
                   , asStmtsAfter = Seq.Empty }

------------------------------------------------------------------------
-- Implementation

newCFG :: CFG ext s init ret
       -> [Block ext s ret]
       -> Annotator ext s ret (CFG ext s init ret)
newCFG cfg blocks =
  do nextAtomId <- gets asNextAtomId
     return $ cfg { cfgBlocks = blocks
                  , cfgNextValue = nextAtomId }

annotateBlockStmts :: TraverseExt ext
                   => (Stmt ext s -> Annotator ext s ret ())
                   -> (TermStmt s ret -> Annotator ext s ret ())
                   -> Block ext s ret
                   -> Annotator ext s ret (Block ext s ret)
annotateBlockStmts fS fT block =
  do newStmts <- fmap catSeqs $ forM (blockStmts block) $ \stmt ->
       do fS (pos_val stmt)
          bef <- gets asStmtsBefore
          aft <- gets asStmtsAfter
          clearStmts
          return $ bef Seq.>< (stmt Seq.<| aft)
     newFinalStmts <-
       do fT (pos_val (blockTerm block))
          bef <- gets asStmtsBefore
          -- Ignore asStmtsAfter
          clearStmts
          return bef
     let stmts = newStmts Seq.>< newFinalStmts
     -- TODO Check that it's okay to pass an over-approximation of the
     -- inputs to mkBlock, whose documentation says it only expects
     -- "extra" inputs; we only have access to blockKnownInputs and
     -- have no way of determining which inputs were the extra ones
     return $ mkBlock (blockID block) (blockKnownInputs block)
                      stmts (blockTerm block)
  where
    catSeqs seqs = foldr (Seq.><) Seq.Empty seqs
