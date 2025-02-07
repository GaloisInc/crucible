{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.Debug.Trace
  ( TraceEntry(..)
  , Trace
  , empty
  , append
  , latest
  ) where

import Control.Lens qualified as Lens
import Data.Parameterized.Classes (ixF')
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.NatRepr qualified as NatRepr
import Data.Parameterized.NatRepr (type (<=), NatRepr)
import Data.Parameterized.Some (Some(Some))
import Data.RingBuffer qualified as RB
import Data.Vector qualified as V
import Lang.Crucible.CFG.Core qualified as C
import Lang.Crucible.CFG.Extension qualified as C
import Prettyprinter qualified as PP
import What4.ProgramLoc qualified as W4

data TraceEntry ext
  = forall blocks init ret.
    TraceEntry
    { traceCfg :: C.CFG ext blocks init ret
    , traceBlock :: Some (C.BlockID blocks)
    }

instance C.PrettyExt ext => PP.Pretty (TraceEntry ext) where
  pretty (TraceEntry cfg (Some blkId)) =
    let blk = C.cfgBlockMap cfg Lens.^. ixF' (C.blockIDIndex blkId) in
    ppStmtSeq True (Ctx.size (C.blockInputs blk)) (C._blockStmts blk)
    -- TODO: Taken from Crucible. Export upstream?
    where
      prefixLineNum :: Bool -> W4.ProgramLoc -> PP.Doc ann -> PP.Doc ann
      prefixLineNum True pl d = PP.vcat [PP.pretty "%" PP.<+> W4.ppNoFileName (W4.plSourceLoc pl), d]
      prefixLineNum False _ d = d

      ppStmtSeq :: C.PrettyExt ext => Bool -> Ctx.Size ctx -> C.StmtSeq ext blocks ret ctx -> PP.Doc ann
      ppStmtSeq ppLineNum h (C.ConsStmt pl s r) =
        PP.vcat
        [ prefixLineNum ppLineNum pl (C.ppStmt h s)
        , ppStmtSeq ppLineNum (C.nextStmtHeight h s) r
        ]
      ppStmtSeq ppLineNum _ (C.TermStmt pl s) =
        prefixLineNum ppLineNum pl (PP.pretty s)


newtype Trace ext = Trace (RB.RingBuffer V.Vector (TraceEntry ext))

-- 'RB.new' requires a nonzero input, which we enforce with types
empty :: (1 <= n) => NatRepr n -> IO (Trace ext)
empty n = Trace <$> RB.new (fromIntegral (NatRepr.natValue n))

-- | O(1).
append :: Trace ext -> TraceEntry ext -> IO ()
append (Trace b) e = RB.append e b
{-# INLINEABLE append #-}

-- | Get up to the @N@ latest entries
latest :: Trace ext -> Int -> IO [TraceEntry ext]
latest (Trace b) n = go n
  where
    go x | x <= 0 = pure []
    go x = do
      mEnt <- RB.latest b (n - x)
      case mEnt of
        Nothing -> pure []
        Just ent -> (ent :) <$> go (x - 1)
