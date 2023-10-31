{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.LLVM.Syntax where

import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State.Strict (MonadState(..))
import Control.Monad.Writer.Strict (MonadWriter(..))
import Data.Functor ((<&>))

import Data.Parameterized.Some (Some(..))

import What4.ProgramLoc (Posd(..))

import Lang.Crucible.CFG.Reg (Atom(..), Stmt(..))
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.Types (TypeRepr(..))

import Lang.Crucible.LLVM.Extension (LLVM)
import Lang.Crucible.LLVM.MemModel (pattern LLVMPointerRepr)

import Lang.Crucible.Syntax.Atoms (Atomic)
import Lang.Crucible.Syntax.Concrete (ParserHooks(..), SyntaxState)
import Lang.Crucible.Syntax.ExprParse (MonadSyntax)
import qualified Lang.Crucible.Syntax.Concrete as Parse
import qualified Lang.Crucible.Syntax.ExprParse as Parse

unary :: MonadSyntax Atomic m => m b -> m a -> m a
unary p0 p = Parse.followedBy p0 (Parse.commit *> Parse.cons p Parse.emptyList) <&> fst

llvmParserHooks :: ParserHooks LLVM
llvmParserHooks =
  ParserHooks
  { extensionTypeParser = llvmTypeParser
  , extensionParser = llvmAtomParser
  }

llvmTypeParser :: MonadSyntax Atomic m => m (Some TypeRepr)
llvmTypeParser = Parse.describe "LLVM type" $ Parse.call ptrType
  where
    ptrType :: MonadSyntax Atomic m => m (Some TypeRepr)
    ptrType = do
      let ptrName = do
            s <- Parse.string
            unless (s == "Ptr") Parse.cut

      let ptrWidth = do
            Parse.BoundedNat n <- Parse.posNat
            pure (Some (LLVMPointerRepr n))

      unary ptrName ptrWidth

llvmAtomParser ::
  ( MonadSyntax Atomic m
  , MonadWriter [Posd (Stmt ext s)] m
  , MonadState (SyntaxState s) m
  , MonadIO m
  , IsSyntaxExtension ext
  , ?parserHooks :: ParserHooks ext
  ) =>
  m (Some (Atom s))
llvmAtomParser = Parse.cut
