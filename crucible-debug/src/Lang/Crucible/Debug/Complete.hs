{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Debug.Complete
  ( CompletionEnv(..)
  , CompletionT
  , runCompletionT
  , runCompletion
  , runCompletionM
  , CompletionType(..)
  , Completions(..)
  , complete
  ) where

import Control.Lens qualified as Lens
import Control.Monad qualified as Monad
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader, ReaderT)
import Control.Monad.Reader qualified as Reader
import Control.Monad.Trans (MonadTrans)
import Control.Exception qualified as X
import Data.Foldable (toList)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity, runIdentity)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Data.Parameterized.Some (Some(Some), viewSome)
import Data.Parameterized.SymbolRepr (symbolRepr)
import Data.Set (Set)
import Data.Text qualified as Text
import Data.Text (Text)
import Lang.Crucible.Debug.Arg qualified as Arg
import Lang.Crucible.Debug.Arg.Type (ArgTypeRepr)
import Lang.Crucible.Debug.Arg.Type qualified as AType
import Lang.Crucible.Debug.Breakpoint qualified as Break
import Lang.Crucible.Debug.Breakpoint (Breakpoint)
import Lang.Crucible.Debug.Command (CommandExt)
import Lang.Crucible.Debug.Command qualified as Cmd
import Lang.Crucible.FunctionHandle qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Prettyprinter qualified as PP
import System.Directory qualified as Dir
import System.FilePath qualified as FilePath
import What4.FunctionName qualified as W4

data CompletionEnv cExt
  = forall p sym ext r.
    CompletionEnv
  { envBreakpoints :: Set Breakpoint
  , envCommandExt :: CommandExt cExt
  , envState :: C.ExecState p sym ext r
  }

newtype CompletionT cExt m a
  = CompletionT { runCompletionT :: ReaderT (CompletionEnv cExt) m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO, MonadReader (CompletionEnv cExt), MonadTrans)

-- | Run 'CompletionT' over 'Identity'
runCompletion :: CompletionEnv cExt -> CompletionT cExt Identity a -> a
runCompletion env s = runIdentity (Reader.runReaderT (runCompletionT s) env)

-- | Run 'CompletionT' over another monad
--
-- This is kind of poorly named, but I can\'t think of a better name...
runCompletionM :: CompletionEnv cExt -> CompletionT cExt m a -> m a
runCompletionM env s = Reader.runReaderT (runCompletionT s) env

data CompletionType
  = CBreakpoint
  | CCommand
  | CExactly Text
  | CFunction
  | CPath
  deriving (Eq, Show)

instance PP.Pretty CompletionType where
  pretty =
    \case
      CBreakpoint -> "breakpoint"
      CCommand -> "command"
      CExactly t -> PP.pretty t
      CFunction -> "function"
      CPath -> "path"

completionType :: ArgTypeRepr t -> Maybe CompletionType
completionType =
  \case
    AType.TBreakpointRepr -> Just CBreakpoint
    AType.TCommandRepr -> Just CCommand
    AType.TExactlyRepr s -> Just (CExactly (symbolRepr s))
    AType.TFunctionRepr -> Just CFunction
    AType.TIntRepr -> Nothing
    AType.TPathRepr -> Just CPath
    AType.TTextRepr -> Nothing

commandsWithPrefix ::
  CompletionEnv cExt ->
  -- | Prefix
  String ->
  [String]
commandsWithPrefix cEnv pfx = filter (pfx `List.isPrefixOf`) allCmdNames
  where
    allCmdNames :: [String]
    allCmdNames =
      let cExts = envCommandExt cEnv in
      map (Text.unpack . Cmd.name cExts) (Cmd.allCmds cExts)

completePath :: FilePath -> IO [String]
completePath path =
  if List.null path
  then Dir.listDirectory =<< Dir.getCurrentDirectory
  else do
    isDir <- Dir.doesDirectoryExist path
    if isDir && not (FilePath.hasTrailingPathSeparator path)
      then pure [FilePath.addTrailingPathSeparator path]
      else do
        let dir = FilePath.addTrailingPathSeparator (FilePath.takeDirectory path)
        contents <- Dir.listDirectory dir
        let file = FilePath.takeFileName path
        if List.null file
        then pure (map (dir ++) contents)
        else pure (map (dir ++) (filter (file `List.isPrefixOf`) contents))

completionsForType ::
  CompletionEnv cExt ->
  -- | Prefix
  String ->
  CompletionType ->
  IO [String]
completionsForType cEnv pfx =
  \case
    CBreakpoint ->
      pure $
        toList (envBreakpoints cEnv) &
          map Break.toText &
          filter (Text.pack pfx `Text.isPrefixOf`) &
          map Text.unpack
    CCommand -> pure (commandsWithPrefix cEnv pfx)
    CExactly s ->
      let s' = Text.unpack s in
      pure (if pfx `List.isPrefixOf` s' then [s'] else [])
    CFunction -> do
      CompletionEnv { envState = execState } <- pure cEnv
      let binds = execState Lens.^. Lens.to C.execStateContext . C.functionBindings
      let hdls = C.handleMapToHandles (C.fnBindings binds)
      pure (map (\(C.SomeHandle hdl) -> Text.unpack (W4.functionName (C.handleName hdl))) hdls)
    CPath ->
      X.try @X.IOException (completePath pfx) <&>
        \case
          Left _ -> []
          Right cs -> cs

data Completions
  = Completions
    { completionsType :: CompletionType
    , completions :: [String]
    }

-- | Used in the test suite with @. complete@
instance PP.Pretty Completions where
  pretty (Completions ty cs) = do
    let def =
          if null cs
          then PP.pretty ty
          else
            PP.pretty ty PP.<> ":" PP.<+> PP.hsep (PP.punctuate "," (map PP.pretty cs))
    case ty of
      CBreakpoint -> def
      CCommand -> PP.pretty ty
      CExactly {} ->
        if null cs
        then PP.pretty ty PP.<+> "(x)"
        else PP.pretty ty
      CFunction {} -> def
      CPath -> def

complete ::
  CompletionEnv cExt ->
  -- | Whole line
  String ->
  -- | Word being completed
  String ->
  IO [Completions]
complete cEnv input word =
  case words input of
    [] -> pure [Completions CCommand allCmdNames]
    [_] | not (null word) ->
      pure [Completions CCommand (commandsWithPrefix cEnv word)]
    (c : args) -> do
      case Cmd.parse cExts (Text.pack c) of
        Just cmd ->
          case Cmd.regex cExts cmd of
            Some rx -> do
              let (allTypes, next) = Arg.types cExts rx (map Text.pack args)
              let types =
                    case Map.lookup (Text.pack word) allTypes of
                      Nothing -> next
                      Just ts -> ts
              let cTypes = Maybe.mapMaybe (viewSome completionType) (toList types)
              Monad.mapM (\t -> Completions t <$> completionsForType cEnv word t) cTypes
        Nothing -> pure []
  where
    cExts = envCommandExt cEnv

    allCmdNames :: [String]
    allCmdNames = map (Text.unpack . Cmd.name cExts) (Cmd.allCmds cExts)
