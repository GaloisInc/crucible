-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.RegRewrite
-- Description      : Operations for manipulating registerized CFGs
-- Copyright        : (c) Galois, Inc 2014-2018
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
module Lang.Crucible.Utils.RegRewrite
  ( annotateCFGStmts
  , Annotator
  , addStmtBefore
  , addStmtAfter
  , freshAtom
  ) where

import           Control.Monad.State.Strict
import           Control.Monad.Writer.Strict
import qualified Data.Semigroup as Sem
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import qualified Data.Parameterized.Context as Ctx
import           What4.ProgramLoc

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.CFG.Reg
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types

------------------------------------------------------------------------
-- Public interface

annotateCFGStmts :: TraverseExt ext
                 => (Stmt ext s -> Annotator ext s ret ())
                 -> (TermStmt s ret -> Annotator ext s ret ())
                 -> CFG ext s init ret
                 -> CFG ext s init ret
annotateCFGStmts fS fT cfg =
  runAnnotator cfg $
    do blocks' <- mapM (annotateBlockStmts fS fT) (cfgBlocks cfg)
       return $ cfg { cfgBlocks = blocks' }

newtype Annotator ext s (ret :: CrucibleType) a =
  Annotator (State (AnnState ext s ret) a)
  deriving ( Functor, Applicative, Monad, MonadState (AnnState ext s ret) )

addStmtBefore :: Stmt ext s -> Annotator ext s ret ()
addStmtBefore stmt =
  modify $ \s -> s { asStmtsBefore = asStmtsBefore s Seq.:|>
                                     Posd InternalPos stmt }

addStmtAfter :: Stmt ext s -> Annotator ext s ret ()
addStmtAfter stmt =
  modify $ \s -> s { asStmtsAfter = asStmtsAfter s Seq.:|>
                                    Posd InternalPos stmt }

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
                         , asNextAtomId = initialNextAtomId cfg }

runAnnotator :: CFG ext s init ret -> Annotator ext s ret a -> a
runAnnotator cfg (Annotator f) = fst $ runState f (initState cfg)

clearStmts :: Annotator ext s ret ()
clearStmts =
  modify $ \s -> s { asStmtsBefore = Seq.Empty
                   , asStmtsAfter = Seq.Empty }

------------------------------------------------------------------------
-- Implementation

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

------------------------------------------------------------------------
-- Computation of initial next atom id for CFG
--
-- We need to be sure and generate only atom ids that don't appear in
-- the CFG already. Simple way to do that is to find the highest atom
-- id and add one.

newtype MaxAtomId = MaxAtomId { getMaxAtomId :: Int }

instance Sem.Semigroup MaxAtomId where
  MaxAtomId n <> MaxAtomId m = MaxAtomId (n `max` m)

instance Monoid MaxAtomId where
  mempty = MaxAtomId 0
  mappend = (Sem.<>)
       
initialNextAtomId :: CFG ext s init ret -> Int
initialNextAtomId cfg = 1 + maxValueId cfg

maxValueId :: CFG ext s init ret -> Int
maxValueId cfg = getMaxAtomId $ execWriter $ go
  where
    go :: Writer MaxAtomId ()
    go = do considerArgumentAtoms

            forM_ (cfgBlocks cfg) $ \block ->
              do case blockID block of
                   LambdaID l -> foundAtom (lambdaAtom l)
                   LabelID _ -> return ()

                 forM_ (blockStmts block) $ \(Posd { pos_val = stmt }) ->
                   case stmt of
                     DefineAtom atom _ -> foundAtom atom
                     _ -> return ()

    foundAtom atom = tell $ MaxAtomId (atomId atom)
    
    -- There are implicitly atoms with ids [0..n-1] for n arguments
    considerArgumentAtoms =
      tell $ MaxAtomId $
        Ctx.sizeInt (Ctx.size (handleArgTypes (cfgHandle cfg))) - 1
