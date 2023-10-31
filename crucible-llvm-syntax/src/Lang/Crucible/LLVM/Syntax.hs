{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Lang.Crucible.LLVM.Syntax (llvmParserHooks) where

import Control.Applicative (empty)
import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State.Strict (MonadState(..))
import Control.Monad.Writer.Strict (MonadWriter(..))
import Data.Functor ((<&>))

import Prettyprinter (pretty)

import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(..))

import What4.ProgramLoc (Posd(..))

import Lang.Crucible.CFG.Expr qualified as Expr
import Lang.Crucible.CFG.Reg (Atom, GlobalVar, Stmt)
import Lang.Crucible.CFG.Reg qualified as Reg
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.Types (TypeRepr(..))

import Lang.Crucible.LLVM.DataLayout (Alignment)
import Lang.Crucible.LLVM.DataLayout qualified as DataLayout
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
llvmAtomParser mvar =
  Parse.depCons Parse.atomName $
    \case
      Atom.AtomName "ptr" -> do
        loc <- Parse.position
        Parse.depCons Parse.posNat $ \(Parse.BoundedNat w) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> NatRepr Ctx.:> BVRepr w)
          let (rest, off) = Ctx.decompose assign
          let (Ctx.Empty, blk) = Ctx.decompose rest
          let expr = Ext.LLVM_PointerExpr w blk off
          ptrAtom <- Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp expr))
          return (Some ptrAtom)

      Atom.AtomName "ptr-block" -> do
        loc <- Parse.position
        Parse.depCons Parse.posNat $ \(Parse.BoundedNat w) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> LLVMPointerRepr w)
          let (Ctx.Empty, ptr) = Ctx.decompose assign
          let expr = Ext.LLVM_PointerBlock w ptr
          Some <$> Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp expr))

      Atom.AtomName "ptr-offset" -> do
        loc <- Parse.position
        Parse.depCons Parse.posNat $ \(Parse.BoundedNat w) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> LLVMPointerRepr w)
          let (Ctx.Empty, ptr) = Ctx.decompose assign
          let expr = Ext.LLVM_PointerOffset w ptr
          Some <$> Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp expr))

      Atom.AtomName "ptr-ite" -> do
        loc <- Parse.position
        Parse.depCons Parse.posNat $ \(Parse.BoundedNat w) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> BoolRepr Ctx.:> LLVMPointerRepr w Ctx.:> LLVMPointerRepr w)
          let (rest, p2) = Ctx.decompose assign
          let (rest', p1) = Ctx.decompose rest
          let (Ctx.Empty, b) = Ctx.decompose rest'
          let expr = Ext.LLVM_PointerIte w b p1 p2
          Some <$> Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp expr))

      Atom.AtomName "alloca" -> do
        loc <- Parse.position
        (align, assign) <- 
          Parse.cons
            parseAlign
            (Parse.operands (Ctx.Empty Ctx.:> BVRepr ?ptrWidth))
        let (Ctx.Empty, sz) = Ctx.decompose assign
        let stmt = Ext.LLVM_Alloca ?ptrWidth mvar sz align (show (pretty loc))
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      _ -> empty
  where
    parseAlign :: MonadSyntax Atomic m => m Alignment
    parseAlign = do
      s <- Parse.atomName
      unless (s == Atom.AtomName "none") Parse.cut
      pure DataLayout.noAlignment
