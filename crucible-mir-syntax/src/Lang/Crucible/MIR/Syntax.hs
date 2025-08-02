{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

module Lang.Crucible.MIR.Syntax
  ( emptyParserHooks
  , mirParserHooks
  , referenceTypeParser
  ) where

import Control.Applicative ((<|>), empty)
import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State.Strict (MonadState(..))
import Control.Monad.Writer.Strict (MonadWriter(..))

import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(..))

import What4.ProgramLoc (Posd(..))

import Lang.Crucible.CFG.Reg (Atom, Stmt)
import Lang.Crucible.CFG.Reg qualified as Reg
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.Types (TypeRepr(..))

import Lang.Crucible.Syntax.Atoms (Atomic)
import Lang.Crucible.Syntax.Atoms qualified as Atom
import Lang.Crucible.Syntax.Concrete (ParserHooks(..), SyntaxState)
import Lang.Crucible.Syntax.Concrete qualified as Parse
import Lang.Crucible.Syntax.Monad (MonadSyntax)
import Lang.Crucible.Syntax.Monad qualified as Parse

import Mir.Intrinsics (MIR)
import Mir.Intrinsics qualified as Mir

-- | A 'ParserHooks' instance that adds no further extensions to the language.
emptyParserHooks :: ParserHooks ext
emptyParserHooks = ParserHooks empty empty

mirParserHooks ::
  -- | Hooks with which to further extend this parser
  ParserHooks MIR ->
  ParserHooks MIR
mirParserHooks hooks =
  ParserHooks
  { extensionTypeParser =
      Parse.describe "MIR type" $
        Parse.call (mirTypeParser <|> extensionTypeParser hooks)
  , extensionParser =
      Parse.describe "MIR operation" $
        Parse.call (mirAtomParser <|> extensionParser hooks)
  }

---------------------------------------------------------------------
-- Types

mirTypeParser :: MonadSyntax Atomic m => m (Some TypeRepr)
mirTypeParser = Parse.describe "MIR type" $ do
  _ <- referenceTypeParser
  pure (Some Mir.MirReferenceRepr)

referenceTypeParser :: MonadSyntax Atomic m => m ()
referenceTypeParser = Parse.describe "MIR reference type" $ do
  name <- Parse.atomName
  unless (name == Atom.AtomName "MirReference") Parse.cut

---------------------------------------------------------------------
-- Operations

mirAtomParser ::
  ( MonadSyntax Atomic m
  , MonadWriter [Posd (Stmt MIR s)] m
  , MonadState (SyntaxState s) m
  , MonadIO m
  , IsSyntaxExtension MIR
  , ?parserHooks :: ParserHooks MIR
  ) =>
  m (Some (Atom s))
mirAtomParser =
  Parse.depCons Parse.atomName $
    \case
      Atom.AtomName "ref-new" -> Parse.describe "MIR ref-new arguments" $ do
        loc <- Parse.position
        (Some tpr, ()) <- Parse.cons Parse.isType Parse.emptyList
        let stmt = Mir.MirNewRef tpr
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "ref-read" -> Parse.describe "MIR ref-read arguments" $ do
        loc <- Parse.position
        (Some tpr, assign) <-
          Parse.cons
            Parse.isType
            (Parse.operands (Ctx.Empty Ctx.:> Mir.MirReferenceRepr))
        let (Ctx.Empty, ref) = Ctx.decompose assign
        let stmt = Mir.MirReadRef tpr ref
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "ref-write" -> Parse.describe "MIR ref-write arguments" $ do
        loc <- Parse.position
        Parse.depCons Parse.isType $ \(Some tpr) -> do
          assign <- Parse.operands (Ctx.Empty Ctx.:> Mir.MirReferenceRepr Ctx.:> tpr)
          let (rest, val) = Ctx.decompose assign
          let (Ctx.Empty, ref) = Ctx.decompose rest
          let stmt = Mir.MirWriteRef tpr ref val
          Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      Atom.AtomName "ref-drop" -> Parse.describe "MIR ref-drop arguments" $ do
        loc <- Parse.position
        assign <- Parse.operands (Ctx.Empty Ctx.:> Mir.MirReferenceRepr)
        let (Ctx.Empty, ref) = Ctx.decompose assign
        let stmt = Mir.MirDropRef ref
        Some <$> Parse.freshAtom loc (Reg.EvalExt stmt)

      _ -> empty
