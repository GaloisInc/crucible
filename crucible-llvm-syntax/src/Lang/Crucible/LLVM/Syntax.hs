{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Lang.Crucible.LLVM.Syntax where

import Control.Applicative (empty)
import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State.Strict (MonadState(..))
import Control.Monad.Writer.Strict (MonadWriter(..))
import Data.Functor ((<&>))

import Data.BitVector.Sized qualified as BV

import Data.Parameterized.Some (Some(..))

import What4.ProgramLoc (Posd(..))

import Lang.Crucible.CFG.Expr qualified as Expr
import Lang.Crucible.CFG.Reg (Atom, GlobalVar, Stmt)
import Lang.Crucible.CFG.Reg qualified as Reg
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.Types (TypeRepr(..))

import Lang.Crucible.LLVM.Extension (LLVM)
import Lang.Crucible.LLVM.Extension qualified as Ext
import Lang.Crucible.LLVM.MemModel (Mem, pattern LLVMPointerRepr)
import Lang.Crucible.LLVM.MemModel qualified as Mem

import Lang.Crucible.Syntax.Atoms (Atomic)
import Lang.Crucible.Syntax.Atoms qualified as Atom
import Lang.Crucible.Syntax.Concrete (ParserHooks(..), SyntaxState)
import Lang.Crucible.Syntax.Concrete qualified as Parse
import Lang.Crucible.Syntax.ExprParse (MonadSyntax)
import Lang.Crucible.Syntax.ExprParse qualified as Parse

unary :: MonadSyntax Atomic m => m b -> m a -> m a
unary p0 p = Parse.followedBy p0 (Parse.commit *> Parse.cons p Parse.emptyList) <&> fst

llvmParserHooks :: 
  Mem.HasPtrWidth w =>
  GlobalVar Mem ->
  ParserHooks LLVM
llvmParserHooks mvar =
  ParserHooks
  { extensionTypeParser = llvmTypeParser
  , extensionParser = llvmAtomParser mvar
  }

llvmTypeParser :: MonadSyntax Atomic m => m (Some TypeRepr)
llvmTypeParser = Parse.describe "LLVM type" $ Parse.call ptrType
  where
    ptrType :: MonadSyntax Atomic m => m (Some TypeRepr)
    ptrType = do
      let ptrName = do
            s <- Parse.atomName
            unless (s == Atom.AtomName "Ptr") Parse.cut
      let ptrWidth = do
            Parse.BoundedNat n <- Parse.posNat
            pure (Some (LLVMPointerRepr n))
      unary ptrName ptrWidth

llvmAtomParser ::
  ( MonadSyntax Atomic m
  , MonadWriter [Posd (Stmt LLVM s)] m
  , MonadState (SyntaxState s) m
  , MonadIO m
  , IsSyntaxExtension LLVM
  , ?parserHooks :: ParserHooks LLVM
  , Mem.HasPtrWidth w
  ) =>
  GlobalVar Mem -> 
  m (Some (Atom s))
llvmAtomParser _mvar =
  Parse.depCons Parse.atomName $
    \case
      Atom.AtomName "null" -> do
        loc <- Parse.position
        blkAtom <- Parse.freshAtom loc (Reg.EvalApp (Expr.NatLit 0))
        offAtom <- Parse.freshAtom loc (Reg.EvalApp (Expr.BVLit ?ptrWidth (BV.zero ?ptrWidth)))
        ptrAtom <- Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp (Ext.LLVM_PointerExpr ?ptrWidth blkAtom offAtom)))
        return (Some ptrAtom)
      _ -> empty
