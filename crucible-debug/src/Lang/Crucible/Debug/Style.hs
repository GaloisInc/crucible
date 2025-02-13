{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

module Lang.Crucible.Debug.Style
  ( StyleEnv(..)
  , StyleT(..)
  , runStyle
  , runStyleM
  , Style(..)
  , Valid(..)
  , Styled(..)
  , style
  , highlighter
  ) where

import Control.Lens qualified as Lens
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader, ReaderT)
import Control.Monad.Reader qualified as Reader
import Control.Monad.Trans (MonadTrans)
import Data.Foldable (toList)
import Data.Foldable qualified as Foldable
import Data.Functor.Identity (Identity, runIdentity)
import Data.List qualified as List
import Data.Parameterized.Some (Some(Some), viewSome)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Text qualified as Text
import Data.Text (Text)
import Lang.Crucible.Debug.Arg (Arg)
import Lang.Crucible.Debug.Arg qualified as Arg
import Lang.Crucible.Debug.Arg.Type (ArgTypeRepr)
import Lang.Crucible.Debug.Breakpoint (Breakpoint)
import Lang.Crucible.Debug.Command (CommandExt)
import Lang.Crucible.Debug.Command qualified as Cmd
import Lang.Crucible.Debug.Regex qualified as Rgx
import Lang.Crucible.FunctionHandle qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Prettyprinter qualified as PP
import System.Console.Isocline qualified as Isocline

data StyleEnv cExt
  = forall p sym ext r.
    StyleEnv
  { envBreakpoints :: Set Breakpoint
  , envCommandExt :: CommandExt cExt
  , envState :: C.ExecState p sym ext r
  }

newtype StyleT cExt m a
  = StyleT
    { runStyleT :: ReaderT (StyleEnv cExt) m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO, MonadReader (StyleEnv cExt), MonadTrans)

-- | Run 'StyleT' over 'Identity'
runStyle :: StyleEnv cExt -> StyleT cExt Identity a -> a
runStyle env s = runIdentity (Reader.runReaderT (runStyleT s) env)

-- | Run 'StyleT' over another monad
--
-- This is kind of poorly named, but I can\'t think of a better name...
runStyleM :: StyleEnv cExt -> StyleT cExt m a -> m a
runStyleM env s = Reader.runReaderT (runStyleT s) env

data Style
  = SBreakpoint
  | SCommand
  | SExactly
  | SFunction
  | SNumber
  | SPath
  | SText
  | SUnknown
  deriving (Eq, Show)

instance PP.Pretty Style where
  pretty =
    \case
      SBreakpoint -> "breakpoint"
      SCommand -> "command"
      SExactly -> "exactly"
      SFunction -> "function"
      SNumber -> "number"
      SPath -> "path"
      SText -> "text"
      SUnknown -> "unknown"

styleFor :: Arg cExt t -> Style
styleFor =
  \case
    Arg.ABreakpoint {} -> SBreakpoint
    Arg.ACommand {} -> SCommand
    Arg.AExactly {} -> SExactly
    Arg.AFunction {} -> SFunction
    Arg.AInt {} -> SNumber
    Arg.APath {} -> SPath
    Arg.AText {} -> SText

data Valid
  = Invalid
  | Valid
  | Unknown
  deriving (Eq, Show)

instance PP.Pretty Valid where
  pretty =
    \case
      Invalid -> "invalid"
      Valid -> "valid"
      Unknown -> "unknown"

boolToValid :: Bool -> Valid
boolToValid False = Invalid
boolToValid True = Valid

validate ::
  Monad m =>
  Arg cExt t ->
  StyleT cExt m Valid
validate =
  \case
    Arg.ACommand {} -> pure Valid
    Arg.ABreakpoint b ->
      boolToValid <$> Reader.asks (Set.member b . envBreakpoints)
    Arg.AExactly {} -> pure Valid
    Arg.AFunction fNm -> do
      StyleEnv { envState = execState } <- Reader.ask
      let binds = execState Lens.^. Lens.to C.execStateContext . C.functionBindings
      let hdls = C.handleMapToHandles (C.fnBindings binds)
      case List.find (\(C.SomeHandle hdl) -> C.handleName hdl == fNm) hdls of
        Nothing ->
          -- May just not yet be loaded/discovered
          pure Unknown
        Just {} -> pure Valid
    Arg.AInt {} -> pure Valid
    Arg.APath {} -> pure Valid
    Arg.AText {} -> pure Valid

data Styled
  = Styled
    { styledStyle :: Style
    , styledValid :: Valid
    }
  deriving (Eq, Show)

instance PP.Pretty Styled where
  pretty s =
    PP.pretty (styledStyle s) PP.<+> PP.parens (PP.pretty (styledValid s))

styled ::
  Monad m =>
  Arg cExt t ->
  StyleT cExt m Styled
styled a = Styled (styleFor a) <$> validate a

style ::
  Monad m =>
  Rgx.RegexRepr ArgTypeRepr r ->
  [Text] ->
  StyleT cExt m [Styled]
style r =
  \case
    [] -> pure []
    (word : ws) -> do
      cExt <- Reader.asks envCommandExt
      let bad = List.replicate (1 + length ws) (Styled SUnknown Invalid)
      case Arg.derivative cExt word r of
        Rgx.DerivativeResult (Some Rgx.Fail) _ -> pure bad
        Rgx.DerivativeResult (Some _) Seq.Empty -> pure bad
        Rgx.DerivativeResult (Some r') (Some m Seq.:<| Seq.Empty) -> do
          s <- styled m
          ss <- style r' ws
          pure (s : ss)
        Rgx.DerivativeResult (Some r') (Some m Seq.:<| ms) -> do
          s <- styled m
          ss <- mapM (viewSome styled) (toList ms)
          let combined = Foldable.foldl' combineStyled s ss
          rest <- style r' ws
          pure (combined : rest)
  where
    combineStyles :: Style -> Style -> Style
    combineStyles s0 s = if s == s0 then s0 else SUnknown

    combineValid :: Valid -> Valid -> Valid
    combineValid v0 v = if v == v0 then v0 else Unknown

    combineStyled :: Styled -> Styled -> Styled
    combineStyled s0 s =
      Styled
      (combineStyles (styledStyle s0) (styledStyle s))
      (combineValid (styledValid s0) (styledValid s))

-- | Helper, not exported
badStyle :: String -> Isocline.Fmt
badStyle = Isocline.style "red"

-- | Helper, not exported
cmdStyle :: String -> Isocline.Fmt
cmdStyle = Isocline.style "bold"

highlightWithRegex ::
  Monad m =>
  Rgx.RegexRepr ArgTypeRepr r ->
  String ->
  StyleT cExt m Isocline.Fmt
highlightWithRegex r line = do
  let (initSpaces, rest) = splitOnSpaces line
  let wds = List.map fst rest
  styles <- style r (List.map Text.pack wds)
  let styledWords = zipWith ($) (map doStyle styles) wds
  let wordsWithSpaces =
        foldMap (uncurry (++)) (zip styledWords (List.map snd rest))
  pure (initSpaces ++ wordsWithSpaces)
  where
    splitOnSpaces :: String -> (String, [(String, String)])
    splitOnSpaces s =
      let (initSpaces, rest) = List.span (== ' ') s in
      (initSpaces, go rest)
      where
        go "" = []
        go x =
          let (word, rest) = List.span (/= ' ') x in
          let (spaces, rest') = List.span (== ' ') rest in
          (word, spaces) : go rest'

    -- Fairly arbitrary choices
    doStyle :: Styled -> String -> Isocline.Fmt
    doStyle s =
      case styledValid s of
        Invalid -> badStyle
        _ ->
          case styledStyle s of
            SBreakpoint -> Isocline.style "green"
            SCommand -> cmdStyle
            SExactly -> Isocline.style "keyword"
            SFunction -> Isocline.style "blue"
            SNumber -> Isocline.style "number"
            SPath -> Isocline.style "italic"
            SText -> id
            SUnknown -> id

highlighter :: Monad m => String -> StyleT cExt m Isocline.Fmt
highlighter input = do
  cExt <- Reader.asks envCommandExt
  let (initSpaces, rest) = List.span (== ' ') input
  let (cmdStr, rest') = List.span (/= ' ') rest
  case Cmd.parse cExt (Text.pack cmdStr) of
    Just cmd ->
      case Cmd.regex cExt cmd of
        Some rx -> do
          styledRest <- highlightWithRegex rx rest'
          pure $ List.concat [initSpaces , cmdStyle cmdStr, styledRest]
    Nothing -> pure $ List.concat [initSpaces, badStyle cmdStr, rest']

