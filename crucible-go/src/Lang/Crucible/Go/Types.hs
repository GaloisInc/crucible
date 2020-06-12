{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.Go.Types where

import           Language.Go.AST
import           Language.Go.Types

import           Lang.Crucible.CFG.Extension

----------------------------------------------------------------------
-- | Go extension tag.

newtype Go = Go ()

type instance ExprExtension Go = EmptyExprExtension
type instance StmtExtension Go = EmptyStmtExtension

instance IsSyntaxExtension Go

type Verbosity = Int
