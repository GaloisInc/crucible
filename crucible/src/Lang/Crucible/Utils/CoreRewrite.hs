------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.CoreRewrite
-- Description      : Operations for manipulating Core CFGs
-- Copyright        : (c) Galois, Inc 2016
-- License          : BSD3
-- Maintainer       : Simon Winwood <sjw@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.Utils.CoreRewrite
( annotateCFGStmts
) where

import           Control.Lens

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (Pair(..))
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension

------------------------------------------------------------------------
-- CFG annotation


-- | This function walks through all the blocks in the CFG calling
-- @fS@ on each @Stmt@ and @fT@ on each @TermStmt@.  These functions
-- return a possible annotaition statement (which has access to the
-- result of the statement, if any) along with a context diff which
-- describes any new variables.
annotateCFGStmts ::
   TraverseExt ext =>
   (forall cin cout. Some (BlockID blocks) -> Ctx.Size cout -> Stmt ext cin cout -> Maybe (StmtSeq ext blocks UnitType cout))
  -- ^ This is the annotation function.  The resulting @StmtSeq@ gets
  -- spliced in after the statement so that they can inspect the
  -- result if desired.  The terminal statement is ignored.
  -> (forall ctx'. Some (BlockID blocks)  -> Ctx.Size ctx' -> TermStmt blocks ret ctx' -> Maybe (StmtSeq ext blocks UnitType ctx'))
  -- ^ As above but for the final term stmt, where the annotation will
  -- be _before_ the term stmt.
  -> CFG ext blocks ctx ret -> CFG ext blocks ctx ret
annotateCFGStmts fS fT = mapCFGBlocks (annotateBlockStmts fS fT)

mapCFGBlocks :: (forall x. Block ext blocks ret x -> Block ext blocks ret x)
             -> CFG ext blocks ctx ret -> CFG ext blocks ctx ret
mapCFGBlocks f cfg = cfg { cfgBlockMap = fmapFC f (cfgBlockMap cfg) }

annotateBlockStmts ::
  forall ext blocks ret ctx.
  TraverseExt ext =>
  (forall cin cout. Some (BlockID blocks) -> Ctx.Size cout -> Stmt ext cin cout -> Maybe (StmtSeq ext blocks UnitType cout))
  -- ^ This is the annotation function.  Annotation statements go
  -- after the statement so that they can inspect the result if
  -- desired.  We use Diff here over CtxEmbedding as the remainder of
  -- the statements can't use the result of the annotation function
  -> (forall ctx'. Some (BlockID blocks) -> Ctx.Size ctx' -> TermStmt blocks ret ctx' -> Maybe (StmtSeq ext blocks UnitType ctx'))
  -- ^ As above but for the final term stmt, where the annotation will
  -- be _before_ the term stmt.
  -> Block ext blocks ret ctx
  -> Block ext blocks ret ctx
annotateBlockStmts fS fT b = b & blockStmts %~ goStmts initialCtxe
  where
    initialCtxe = Ctx.identityEmbedding (Ctx.size (blockInputs b))
    goStmts :: forall ctx' ctx''. Ctx.CtxEmbedding ctx' ctx''
            -> StmtSeq ext blocks ret ctx' -> StmtSeq ext blocks ret ctx''
    goStmts ctxe (ConsStmt loc stmt rest) =
      case applyEmbeddingStmt ctxe stmt of
        Pair stmt' ctxe' ->
          case fS (Some $ blockID b) (ctxe' ^. Ctx.ctxeSize) stmt' of
            Nothing  -> ConsStmt loc stmt' (goStmts ctxe' rest)
            Just annotSeq ->
              ConsStmt loc stmt' (appendStmtSeq ctxe' annotSeq (flip goStmts rest))
    goStmts ctxe (TermStmt loc term) =
      let term' = Ctx.applyEmbedding ctxe term in
      case fT (Some $ blockID b) (ctxe ^. Ctx.ctxeSize) term' of
        Nothing -> TermStmt loc term'
        Just annotSeq ->
          -- FIXME: we could use extendContext here instead
          let restf :: forall fctx. Ctx.CtxEmbedding ctx' fctx -> StmtSeq ext blocks ret fctx
              restf ctxe'' = TermStmt loc (Ctx.applyEmbedding ctxe'' term)
          in appendStmtSeq ctxe annotSeq restf

stmtDiff :: Stmt ext ctx ctx' -> Ctx.Diff ctx ctx'
stmtDiff stmt =
  case stmt of
    SetReg {}        -> Ctx.knownDiff
    ExtendAssign{}   -> Ctx.knownDiff
    CallHandle {}    -> Ctx.knownDiff
    Print {}         -> Ctx.knownDiff
    ReadGlobal {}    -> Ctx.knownDiff
    WriteGlobal {}   -> Ctx.knownDiff
    FreshConstant{}  -> Ctx.knownDiff
    FreshFloat{}     -> Ctx.knownDiff
    FreshNat{}       -> Ctx.knownDiff
    NewRefCell {}    -> Ctx.knownDiff
    NewEmptyRefCell{}-> Ctx.knownDiff
    ReadRefCell {}   -> Ctx.knownDiff
    WriteRefCell {}  -> Ctx.knownDiff
    DropRefCell {}   -> Ctx.knownDiff
    Assert {}        -> Ctx.knownDiff
    Assume {}        -> Ctx.knownDiff

-- | This appends two @StmtSeq@, throwing away the @TermStmt@ from the first @StmtSeq@
-- It could probably be generalized to @Ctx.Diff@ instead of an embedding.
appendStmtSeq :: forall ext blocks ret ret' ctx ctx'.
                 Ctx.CtxEmbedding ctx ctx'
              -> StmtSeq ext blocks ret  ctx'
              -> (forall ctx''. Ctx.CtxEmbedding ctx ctx'' -> StmtSeq ext blocks ret' ctx'')
              -> StmtSeq ext blocks ret' ctx'
appendStmtSeq ctxe seq1 seq2f = go ctxe seq1
  where
    go :: forall ctx''.
          Ctx.CtxEmbedding ctx ctx''
          -> StmtSeq ext blocks ret ctx''
          -> StmtSeq ext blocks ret' ctx''
    go ctxe' (ConsStmt loc stmt rest) =
      -- This just throws away the new variables, which is OK as seq2
      -- can't reference them.
      let ctxe'' = Ctx.extendEmbeddingRightDiff (stmtDiff stmt) ctxe'
      in ConsStmt loc stmt (go ctxe'' rest)
    go ctxe' (TermStmt _loc _term)    = seq2f ctxe'
