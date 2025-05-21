{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Lang.Crucible.LLVM.Syntax
  ( emptyParserHooks
  , llvmParserHooks
  , pointerTypeParser
  ) where

import Control.Applicative ((<|>), empty)
import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State.Strict (MonadState(..))
import Control.Monad.Writer.Strict (MonadWriter(..))
import Data.Functor ((<&>))
import qualified Data.Text as Text

import Prettyprinter (pretty)

-- Optimally, this library wouldn't depend on llvm-pretty...
import Text.LLVM.AST as L (Symbol(Symbol))

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
import Lang.Crucible.LLVM.MemModel (Mem, pattern LLVMPointerRepr, pattern PtrRepr)
import Lang.Crucible.LLVM.MemModel qualified as Mem
import Lang.Crucible.LLVM.MemType (MemType)
import Lang.Crucible.LLVM.MemType qualified as MemType
import Lang.Crucible.LLVM.Translation (llvmTypeAsRepr)

import Lang.Crucible.Syntax.Atoms (Atomic)
import Lang.Crucible.Syntax.Atoms qualified as Atom
import Lang.Crucible.Syntax.Concrete (ParserHooks(..), SyntaxState)
import Lang.Crucible.Syntax.Concrete qualified as Parse
import Lang.Crucible.Syntax.Monad (MonadSyntax)
import Lang.Crucible.Syntax.Monad qualified as Parse

-- | A 'ParserHooks' instance that adds no further extensions to the language.
emptyParserHooks :: ParserHooks ext
emptyParserHooks = ParserHooks empty empty

llvmParserHooks ::
  Mem.HasPtrWidth w =>
  -- | Hooks with which to further extend this parser
  ParserHooks LLVM ->
  GlobalVar Mem ->
  ParserHooks LLVM
llvmParserHooks hooks mvar =
  ParserHooks
  { extensionTypeParser =
      Parse.describe "LLVM type" $
        Parse.call (llvmTypeParser <|> extensionTypeParser hooks)
  , extensionParser =
      Parse.describe "LLVM operation" $
        Parse.call (llvmAtomParser mvar <|> extensionParser hooks)
  }

---------------------------------------------------------------------
-- Types

llvmTypeParser :: MonadSyntax Atomic m => m (Some TypeRepr)
llvmTypeParser = Parse.describe "LLVM type" $ do
  Parse.BoundedNat n <- pointerTypeParser
  pure (Some (LLVMPointerRepr n))

-- | Like 'Lang.Crucible.Syntax.Concrete.Unary', but takes an arbitrary parser
-- for its first argument.
unary :: MonadSyntax Atomic m => m b -> m a -> m a
unary p0 p = Parse.followedBy p0 (Parse.commit *> Parse.cons p Parse.emptyList) <&> fst

pointerTypeParser :: MonadSyntax Atomic m => m Parse.PosNat
pointerTypeParser = Parse.describe "LLVM pointer type" $ do
  let ptrName = do
        s <- Parse.atomName
        unless (s == Atom.AtomName "Ptr") Parse.cut
  unary ptrName Parse.posNat

---------------------------------------------------------------------
-- Operations

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
      Atom.AtomName "ptr" -> Parse.describe "LLVM ptr arguments" $ do
        loc <- Parse.position
        Parse.depCons Parse.posNat $ \(Parse.BoundedNat w) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> NatRepr Ctx.:> BVRepr w)
          let (rest, off) = Ctx.decompose assign
          let (Ctx.Empty, blk) = Ctx.decompose rest
          let expr = Ext.LLVM_PointerExpr w blk off
          ptrAtom <- Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp expr))
          return (Some ptrAtom)

      Atom.AtomName "ptr-add-offset" -> Parse.describe "LLVM ptr-add-offset arguments" $ do
        loc <- Parse.position
        assign <- Parse.operands (Ctx.Empty Ctx.:> PtrRepr Ctx.:> BVRepr ?ptrWidth)
        let (rest, bv) = Ctx.decompose assign
        let (Ctx.Empty, ptr) = Ctx.decompose rest
        let stmt = Ext.LLVM_PtrAddOffset ?ptrWidth mvar ptr bv
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "ptr-block" -> Parse.describe "LLVM ptr-block arguments" $ do
        loc <- Parse.position
        Parse.depCons Parse.posNat $ \(Parse.BoundedNat w) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> LLVMPointerRepr w)
          let (Ctx.Empty, ptr) = Ctx.decompose assign
          let expr = Ext.LLVM_PointerBlock w ptr
          Some <$> Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp expr))

      Atom.AtomName "ptr-offset" -> Parse.describe "LLVM ptr-offset arguments" $ do
        loc <- Parse.position
        Parse.depCons Parse.posNat $ \(Parse.BoundedNat w) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> LLVMPointerRepr w)
          let (Ctx.Empty, ptr) = Ctx.decompose assign
          let expr = Ext.LLVM_PointerOffset w ptr
          Some <$> Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp expr))

      Atom.AtomName "ptr-ite" -> Parse.describe "LLVM ptr-ite arguments" $ do
        loc <- Parse.position
        Parse.depCons Parse.posNat $ \(Parse.BoundedNat w) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> BoolRepr Ctx.:> LLVMPointerRepr w Ctx.:> LLVMPointerRepr w)
          let (rest, p2) = Ctx.decompose assign
          let (rest', p1) = Ctx.decompose rest
          let (Ctx.Empty, b) = Ctx.decompose rest'
          let expr = Ext.LLVM_PointerIte w b p1 p2
          Some <$> Parse.freshAtom loc (Reg.EvalApp (Expr.ExtensionApp expr))

      Atom.AtomName "ptr-sub" -> Parse.describe "LLVM ptr-sub arguments" $ do
        loc <- Parse.position
        assign <- Parse.operands (Ctx.Empty Ctx.:> PtrRepr Ctx.:> PtrRepr)
        let (rest, subtrahend) = Ctx.decompose assign
        let (Ctx.Empty, minuend) = Ctx.decompose rest
        let stmt = Ext.LLVM_PtrSubtract ?ptrWidth mvar minuend subtrahend
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "alloca" -> Parse.describe "LLVM alloca arguments" $ do
        loc <- Parse.position
        (align, assign) <-
          Parse.cons
            parseAlign
            (Parse.operands (Ctx.Empty Ctx.:> BVRepr ?ptrWidth))
        let (Ctx.Empty, sz) = Ctx.decompose assign
        let stmt = Ext.LLVM_Alloca ?ptrWidth mvar sz align (show (pretty loc))
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "load" -> Parse.describe "LLVM load arguments" $ do
        loc <- Parse.position
        (align, (memTy, assign)) <-
          Parse.cons
            parseAlign
            (Parse.cons
              parseMemType
              (Parse.operands (Ctx.Empty Ctx.:> PtrRepr)))
        llvmTypeAsRepr memTy $ \tyRep -> do
          case Mem.toStorableType memTy of
            Nothing -> empty
            Just storTy -> do
              let (Ctx.Empty, ptr) = Ctx.decompose assign
              let stmt = Ext.LLVM_Load mvar ptr tyRep storTy align
              Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "load-handle" -> Parse.describe "LLVM load-handle arguments" $ do
        loc <- Parse.position
        (Some ret, (Some args, assign)) <-
          Parse.cons
            Parse.isType
            (Parse.cons
              (Parse.someAssign "list of argument types" Parse.isType)
              (Parse.operands (Ctx.Empty Ctx.:> PtrRepr)))
        let (Ctx.Empty, ptr) = Ctx.decompose assign
        let stmt = Ext.LLVM_LoadHandle mvar Nothing ptr args ret
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "resolve-global" -> Parse.describe "LLVM resolve-global arguments" $ do
        loc <- Parse.position
        let parseSymb = Mem.GlobalSymbol . L.Symbol . Text.unpack <$> Parse.string
        (symb, ()) <- Parse.cons parseSymb Parse.emptyList
        let stmt = Ext.LLVM_ResolveGlobal ?ptrWidth mvar symb
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "store" -> Parse.describe "LLVM store arguments" $ do
        loc <- Parse.position
        Parse.depCons parseAlign $ \align ->
          Parse.depCons parseMemType $ \memTy ->
            llvmTypeAsRepr memTy $ \tyRep -> do
              assign <- Parse.operands (Ctx.Empty Ctx.:> PtrRepr Ctx.:> tyRep)
              case Mem.toStorableType memTy of
                Nothing -> empty
                Just storTy -> do
                  let (rest, val) = Ctx.decompose assign
                  let (Ctx.Empty, ptr) = Ctx.decompose rest
                  let stmt = Ext.LLVM_Store mvar ptr tyRep storTy align val
                  Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "pop-frame" -> Parse.describe "LLVM pop-frame arguments" $ do
        loc <- Parse.position
        () <- Parse.emptyList
        let stmt = Ext.LLVM_PopFrame mvar
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "push-frame" -> Parse.describe "LLVM push-frame arguments" $ do
        loc <- Parse.position
        (name, ()) <- Parse.cons Parse.string Parse.emptyList
        let stmt = Ext.LLVM_PushFrame name mvar
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "ptr-eq" -> Parse.describe "LLVM ptr-eq arguments" $ do
        loc <- Parse.position
        assign <- Parse.operands (Ctx.Empty Ctx.:> PtrRepr Ctx.:> PtrRepr)
        let (rest, l) = Ctx.decompose assign
        let (Ctx.Empty, r) = Ctx.decompose rest
        let stmt = Ext.LLVM_PtrEq mvar l r
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "ptr-le" -> Parse.describe "LLVM ptr-le arguments" $ do
        loc <- Parse.position
        assign <- Parse.operands (Ctx.Empty Ctx.:> PtrRepr Ctx.:> PtrRepr)
        let (rest, l) = Ctx.decompose assign
        let (Ctx.Empty, r) = Ctx.decompose rest
        let stmt = Ext.LLVM_PtrLe mvar l r
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      _ -> empty
  where
    parseAlign :: MonadSyntax Atomic m => m Alignment
    parseAlign = Parse.describe "alignment" $ do
      s <- Parse.atomName
      unless (s == Atom.AtomName "none") Parse.cut
      pure DataLayout.noAlignment

    parseMemType :: MonadSyntax Atomic m => m MemType
    parseMemType = Parse.describe "LLVM type" $ do
      nm <- Parse.atomName
      case nm of
        Atom.AtomName "i8" -> pure (MemType.IntType 8)
        Atom.AtomName "i16" -> pure (MemType.IntType 16)
        Atom.AtomName "i32" -> pure (MemType.IntType 32)
        Atom.AtomName "i64" -> pure (MemType.IntType 64)
        Atom.AtomName "ptr" -> pure MemType.PtrOpaqueType
        _ -> empty
