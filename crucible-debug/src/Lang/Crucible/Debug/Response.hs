{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.Debug.Response
  ( NotApplicable(..)
  , UserError(..)
  , ResponseExt
  , ProofResult(..)
  , Response(..)
  ) where

import Control.Exception (IOException)
import Data.Foldable qualified as Foldable
import Data.Kind (Type)
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Data.Text (Text)
import Data.Void (Void, absurd)
import Lang.Crucible.Debug.Arg (ArgParseError)
import Lang.Crucible.Debug.Command.Base qualified as BCmd
import Lang.Crucible.Debug.Command (Command)
import Lang.Crucible.Debug.Command qualified as Cmd
import Lang.Crucible.Debug.Regex (MatchError)
import Lang.Crucible.Debug.Statement (ParseError)
import Lang.Crucible.Debug.Statement qualified as Stmt
import Lang.Crucible.Debug.Style (Styled)
import Prettyprinter qualified as PP
import Text.Megaparsec.Error qualified as MP
import What4.FunctionName (FunctionName)
import What4.FunctionName qualified as W4
import What4.ProgramLoc qualified as W4

-- | The command was not applicable in this state
data NotApplicable
  = DoneSimulating
  | NoCfg
  | NoFrame
  | NotDone
  | NotYetSimulating
  deriving Show

instance PP.Pretty NotApplicable where
  pretty =
    \case
      DoneSimulating -> "The simulator is no longer running"
      NoCfg -> "Not executing a CFG"
      NoFrame -> "Not in a call frame"
      NotDone -> "Execution is not finished"
      NotYetSimulating -> "The simulator is not yet running"

-- | The command could not be completed successfully for some reason the user
-- should have anticipated.
data UserError cExt
  = ArgError (Command cExt) (MatchError Text ArgParseError)
  | BadArgNumber Text
  | FnNotFound FunctionName [FunctionName]
  | LoadParseError (MP.ParseErrorBundle Text Void)
  | LoadSyntaxError (PP.Doc Void)
  | NoHelp [Text]
  | NoSuchArgument Int
  | NotACfg W4.FunctionName
  | NotApplicable NotApplicable
  | SourceParseError ParseError
  deriving Show

instance PP.Pretty cExt => PP.Pretty (UserError cExt) where
  pretty =
    \case
      ArgError cmd e ->
        PP.vsep
        [ "Bad arguments for command" PP.<+> PP.pretty cmd PP.<> ":"
        , PP.pretty e
        ]
      BadArgNumber txt ->
        "Bad argument number:" PP.<+> PP.pretty txt
      FnNotFound nm nms ->
        PP.vcat
        [ "No such function:" PP.<+> PP.pretty nm
        , if null nms
          then mempty
          else
            PP.vcat
            [ "Known functions:"
            , PP.vcat (map (PP.pretty . W4.functionName) nms)
            ]
        ]
      LoadParseError err -> PP.pretty (MP.errorBundlePretty err)
      LoadSyntaxError err -> fmap absurd err
      NoHelp args -> "Can't help with" PP.<+> PP.pretty (Text.intercalate " " args)
      NoSuchArgument i -> "No such argument:" PP.<+> PP.pretty i
      NotACfg fNm -> "Not a CFG:" PP.<+> PP.pretty (W4.functionName fNm)
      NotApplicable err -> PP.pretty err
      SourceParseError err ->
        "Parse error during" PP.<+>
        PP.pretty (Cmd.Base @Void BCmd.Source) PP.<>
        ":" PP.<+>
        PP.pretty (Stmt.renderParseError err)

type ResponseExt :: Type -> Type
type family ResponseExt cExt :: Type
type instance ResponseExt Void = Void

data ProofResult
  = Proved
  | Disproved
  | Unknown
  deriving Show

instance PP.Pretty ProofResult where
  pretty =
    \case
      Proved -> "proved"
      Disproved -> "disproved"
      Unknown -> "unknown"

data Response cExt
  = Arg (PP.Doc Void)
  | Backend (PP.Doc Void)
  | Backtrace (PP.Doc Void)
  | Block (PP.Doc Void)
  | Cfg (PP.Doc Void)
  | Clear Int
  | Complete (PP.Doc Void)
  | Delete W4.FunctionName Bool
  | Frame (PP.Doc Void)
  | Help (PP.Doc Void)
  | IOError IOException
  | Load FilePath Int
  | Location W4.ProgramLoc
  | Obligation [PP.Doc Void]
  | PathCondition (PP.Doc Void)
  | Prove (Seq.Seq (PP.Doc Void, ProofResult))
  | ProveTimeout
  | Ok
  | Style [Styled]
  | Trace [PP.Doc Void]
  | Usage (PP.Doc Void)
  | UserError (UserError cExt)
  | XResponse (ResponseExt cExt)

deriving instance (Show (ResponseExt cExt), Show cExt) => Show (Response cExt)

instance (PP.Pretty (ResponseExt cExt), PP.Pretty cExt) => PP.Pretty (Response cExt) where
  pretty =
    \case
      Arg a -> fmap absurd a
      Backend b -> fmap absurd b
      Backtrace bt -> fmap absurd bt
      Block b -> fmap absurd b
      Cfg c -> fmap absurd c
      Complete c -> fmap absurd c
      Clear 0 -> "No proof obligations to clear"
      Clear 1 -> "Cleared 1 proof obligation"
      Clear n -> "Cleared" PP.<+> PP.pretty n PP.<+> "proof obligations"
      Delete nm True -> "Deleted breakpoint at" PP.<+> PP.pretty (W4.functionName nm)
      Delete nm False -> "No breakpoint at" PP.<+> PP.pretty (W4.functionName nm)
      Frame f -> fmap absurd f
      Help h -> fmap absurd h
      Style styles -> PP.hsep (map PP.pretty styles)
      Load p i -> PP.hsep ["Loaded", PP.pretty i, "CFGs from", PP.pretty p]
      IOError e -> PP.viaShow e
      Location l -> PP.pretty (W4.plFunction l) PP.<> PP.viaShow (W4.plSourceLoc l)
      Obligation obls ->
        if null obls
        then "No proof obligations"
        else PP.vsep (map (fmap absurd) obls)
      PathCondition p -> fmap absurd p
      Prove results ->
        if Seq.null results
        then "No obligations to prove"
        else
          PP.vcat $
            map
              (\(goal, result) -> PP.vcat [fmap absurd goal, PP.pretty result])
              (Foldable.toList results)
      ProveTimeout -> "Proof timed out!"
      Ok -> "Ok"
      Trace t -> PP.vcat (PP.punctuate PP.line (map (fmap absurd) t))
      Usage u -> fmap absurd u
      UserError e -> PP.pretty e
      XResponse rExt -> PP.pretty rExt
