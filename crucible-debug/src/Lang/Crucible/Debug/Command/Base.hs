{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Debug.Command.Base
  ( BaseCommand(..)
  , name
  , abbrev
  , detail
  , help
  , regex
  -- * Regular expressions
  , rBacktrace
  , rBlock
  , rBreak
  , rCall
  , rCfg
  , rClear
  , rComment
  , rDelete
  , rDone
  , rFinish
  , rFrame
  , rHelp
  , rLoad
  , rLocation
  , rObligation
  , rPathCondition
  , rProve
  , rQuit
  , rRegister
  , rRun
  , SecretRegex
  , rSecret
  , rSource
  , rStep
  , rTrace
  , rUsage
  ) where

import Data.Parameterized.Classes (knownRepr)
import Data.Parameterized.Some (Some(Some))
import Data.Text (Text)
import Lang.Crucible.Debug.Arg.Type (ArgTypeRepr)
import Lang.Crucible.Debug.Arg.Type qualified as AType
import Lang.Crucible.Debug.Regex qualified as Rgx
import Prettyprinter qualified as PP

data BaseCommand
  = Backtrace
  | Block
  | Break
  | Call
  | Cfg
  | Clear
  | Comment
  | Delete
  | Done
  | Finish
  | Frame
  | Help
  | Load
  | Location
  | Obligation
  | PathCondition
  | Prove
  | Quit
  | Register
  | Run
  | Secret
  | Source
  | Step
  | Trace
  | Usage
  deriving (Bounded, Enum, Show)

instance PP.Pretty BaseCommand where
  pretty = PP.pretty . name

name :: BaseCommand -> Text
name =
  \case
    Backtrace -> "backtrace"
    Block -> "block"
    Break -> "break"
    Call -> "call"
    Cfg -> "cfg"
    Clear -> "clear"
    Comment -> "#"
    Delete -> "delete"
    Done -> "done"
    Finish -> "finish"
    Frame -> "frame"
    Help -> "help"
    Load -> "load"
    Location -> "location"
    Obligation -> "obligation"
    PathCondition -> "path-condition"
    Prove -> "prove"
    Quit -> "quit"
    Register -> "register"
    Run -> "run"
    Secret -> "secret"
    Step -> "step"
    Source -> "source"
    Trace -> "trace"
    Usage -> "usage"

abbrev :: BaseCommand -> Text
abbrev =
  \case
    Backtrace -> "bt"
    Block -> "blk"
    Break -> "b"
    Call -> "cl"
    Cfg -> "cg"
    Clear -> "cr"
    Comment -> "#"
    Delete -> "d"
    Done -> "done"
    Finish -> "fh"
    Frame -> "fr"
    Help -> "h"
    Load -> "l"
    Location -> "loc"
    Obligation -> "o"
    PathCondition -> "pcond"
    Prove -> "p"
    Quit -> "q"
    Register -> "reg"
    Run -> "r"
    Secret -> "."
    Step -> "s"
    Source -> "src"
    Trace -> "trace"
    Usage -> "u"

-- | See 'Lang.Crucible.Debug.Command.extDetail'
detail :: BaseCommand -> Maybe Text
detail =
  \case
    Backtrace -> Nothing
    Block -> Nothing
    Break -> Nothing
    Call -> Nothing
    Cfg -> Nothing
    Clear -> Nothing
    Comment -> Nothing
    Delete -> Nothing
    Done -> Nothing
    Finish -> Nothing
    Frame -> Nothing
    Help -> Nothing
    Load -> Nothing
    Location -> Nothing
    Obligation -> Nothing
    PathCondition -> Nothing
    Prove -> Nothing
    Quit -> Nothing
    Register -> Just "\
      \When given no arguments, prints all values in scope. \
      \Otherwise, prints the values with the given numbers, one per line.\
      \\n\n\

      \The value numbering scheme is based on the structure of Crucible CFGs. \
      \A Crucible CFG (function) is made up of *basic blocks*. \
      \Each basic block takes a list of arguments. \
      \The first block in the function is the *entry* block; \
      \the entry block takes the same arguments as the function. \
      \Each block contains a number of *statements*, which may define values. \
      \The value defined by a statement is in scope for the rest of the block.\
      \\n\n\

      \Values are then numbered as follows: \
      \The first argument to the current block is numbered 0. \
      \Increasing numbers refer to later arguments. \
      \After arguments, higher numbers refer to values defined by statements.\
      \"
    Run -> Nothing
    Secret -> Nothing
    Step -> Nothing
    Source -> Nothing
    Trace -> Nothing
    Usage -> Nothing

-- | See 'Lang.Crucible.Debug.Command.extHelp'
help :: BaseCommand -> Text
help =
  \case
    Backtrace -> "Print the backtrace (AKA stack trace)"
    Block -> "Print the statements in the current block"
    Break -> "Set a breakpoint at the entry to a function"
    Call -> "Call a function (must take no arguments and return the unit type)"
    Cfg -> "Print the CFG of a function (the current function if none is provided)"
    Clear -> "Drop the current proof obligations"
    Comment -> "Ignore all arguments and do nothing"
    Delete -> "Remove a breakpoint"
    Done -> "Like `quit`, but only applies when symbolic execution has finished"
    Finish -> "Execute to the end of the current function"
    Frame -> "Print information about the active stack frame"
    Help -> "Display help text"
    Load -> "Load a Crucible S-expression program from a file"
    Location -> "Print the current program location"
    Obligation -> "Print the current proof obligations"
    PathCondition -> "Print the current path condition"
    Prove -> "Prove the current goals"
    Quit -> "Exit the debugger"
    Register -> "Print registers (including block/function arguments)"
    Run -> "Continue to the next breakpoint or the end of execution"
    Secret -> "Maintenance commands, used for testing"
    Step -> "Continue one step of execution"
    Source -> "Execute a file containing debugger commands"
    Trace -> "Print the N most recently executed basic blocks (default: 2)"
    Usage -> "Display command usage hint"

regex :: BaseCommand -> Some (Rgx.RegexRepr ArgTypeRepr)
regex =
  \case
    Backtrace -> Some rBacktrace
    Block -> Some rBlock
    Break -> Some rBreak
    Call -> Some rCall
    Cfg -> Some rCfg
    Clear -> Some rClear
    Comment -> Some rComment
    Delete -> Some rDelete
    Done -> Some rDone
    Finish -> Some rFinish
    Frame -> Some rFrame
    Help -> Some rHelp
    Load -> Some rLoad
    Location -> Some rLocation
    Obligation -> Some rObligation
    PathCondition -> Some rPathCondition
    Prove -> Some rProve
    Quit -> Some rQuit
    Register -> Some rRegister
    Run -> Some rRun
    Secret -> Some rSecret
    Step -> Some rStep
    Source -> Some rSource
    Trace -> Some rTrace
    Usage -> Some rUsage

rBacktrace :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rBacktrace = knownRepr

rBlock :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rBlock = knownRepr

rBreak :: Rgx.RegexRepr ArgTypeRepr AType.Function
rBreak = knownRepr

rCall :: Rgx.RegexRepr ArgTypeRepr AType.Function
rCall = knownRepr

rCfg :: Rgx.RegexRepr ArgTypeRepr (Rgx.Empty Rgx.:| AType.Function)
rCfg = knownRepr

rClear :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rClear = knownRepr

rComment :: Rgx.RegexRepr ArgTypeRepr (Rgx.Star AType.Text)
rComment = knownRepr

rDelete :: Rgx.RegexRepr ArgTypeRepr AType.Breakpoint
rDelete = knownRepr

rDone :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rDone = knownRepr

rFinish :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rFinish = knownRepr

rFrame :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rFrame = knownRepr

rHelp :: Rgx.RegexRepr ArgTypeRepr (Rgx.Empty Rgx.:| AType.Command)
rHelp = knownRepr

rLoad :: Rgx.RegexRepr ArgTypeRepr AType.Path
rLoad = knownRepr

rLocation :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rLocation = knownRepr

rObligation :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rObligation = knownRepr

rPathCondition :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rPathCondition = knownRepr

rProve :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rProve = knownRepr

rQuit :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rQuit = knownRepr

rRegister :: Rgx.RegexRepr ArgTypeRepr (Rgx.Star AType.Int)
rRegister = knownRepr

rRun :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rRun = knownRepr

type CompleteRegex
  = Rgx.Then (AType.Exactly "complete") (Rgx.Then AType.Command (Rgx.Star AType.Text))

type StyleRegex
  = Rgx.Then (AType.Exactly "style") (Rgx.Then AType.Command (Rgx.Star AType.Text))

type SecretRegex
  = CompleteRegex Rgx.:| StyleRegex

rSecret :: Rgx.RegexRepr ArgTypeRepr SecretRegex
rSecret = knownRepr

rSource :: Rgx.RegexRepr ArgTypeRepr AType.Path
rSource = knownRepr

rStep :: Rgx.RegexRepr ArgTypeRepr Rgx.Empty
rStep = knownRepr

rTrace :: Rgx.RegexRepr ArgTypeRepr (Rgx.Empty Rgx.:| AType.Int)
rTrace = knownRepr

rUsage :: Rgx.RegexRepr ArgTypeRepr AType.Command
rUsage = knownRepr
