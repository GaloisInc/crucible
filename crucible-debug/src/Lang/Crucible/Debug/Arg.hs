{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>

For the sake of correctness, consistency, and concision, it is desirable to
declaratively specify the types of arguments expected by 'Cmd.Command's. These
specifications are used to:

* Parse said arguments (see 'match')
* Generate usage hints for @usage@ (see 'usage')
* Perform syntax highlighting (see "Lang.Crucible.Debug.Style")
* Provide tab-completions (see 'complete')

Perhaps the simplest workable argument specification would be a list of basic
types (e.g., integer, string). However, the purpose of the command language
is to be convenient for interactive use. In particular, users should not have
to remember the names of several variants of a command that do fundamentally
similar tasks. To provide sufficient flexibilty to unite such variants under
a single command, the specification should allow (in increasing order of
sophistication):

* sequencing (i.e., arity higher than 1),
* disjunction (at the very least, in a limited form), and
* quantification (optionality, repetition, and in particular, variable arity).

To justify the necessity of such features, consider the following examples of
each, taken from the bread-and-butter commands of the @gdb@ command language:

* sequencing: @break@ takes several (optional) arguments
* optionality: @step@ takes an optional integer argument
* quantification: @delete@ takes a variable number of breakpoint numbers

The basic list-of-types specification clearly lacks such features. Luckily,
there is a well-understood specification language that allows all of the above,
namely, regular expressions. Thus, the debugger\'s commands are specified
using the facilities provided by "Lang.Crucible.Debug.Regex". The tokens of
the regular expression are basic types (see 'ArgTypeRepr'). Operations like
'derivative' are used internally to provide the high-level functionality
described at the beginning of this documentation.

Commands that are not well-suited to this kind of argument validation can simply
accept @TEXT*@ and perform their own parsing (or not) at the cost of lacking
helpful documentation and completion. This is exactly the specification of the
comment (@#@) command, for example.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Debug.Arg
  ( Arg(..)
  -- * Parsers
  , ArgParseError(..)
  , ArgParser(..)
  , convert
  -- * Operations
  , match
  , derivative
  , types
  , usage
  ) where

import Data.Coerce (coerce)
import Data.Foldable qualified as Foldable
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Parameterized.Some (Some(Some))
import Data.Parameterized.SymbolRepr (SymbolRepr, symbolRepr)
import Data.Parameterized.TraversableFC (fmapFC)
import Data.Sequence (Seq)
import Data.Text qualified as Text
import Lang.Crucible.Debug.Arg.Type (type ArgType(..), ArgTypeRepr(..))
import Lang.Crucible.Debug.Breakpoint (Breakpoint(BreakFunction))
import Lang.Crucible.Debug.Command qualified as Cmd
import Lang.Crucible.Debug.Regex qualified as Rgx
import Prelude hiding (Int)
import Prelude qualified as Prelude
import Prettyprinter qualified as PP
import Text.Read (readMaybe)
import What4.FunctionName qualified as W4

type Arg :: Type -> ArgType -> Type
data Arg cExt i where
  ABreakpoint :: Breakpoint -> Arg cExt 'TBreakpoint
  ACommand :: Cmd.Command cExt -> Arg cExt 'TCommand
  AExactly :: SymbolRepr s -> Arg cExt ('TExactly s)
  AFunction :: W4.FunctionName -> Arg cExt 'TFunction
  AInt :: Prelude.Int -> Arg cExt 'TInt
  APath :: Text.Text -> Arg cExt 'TPath
  AText :: Text.Text -> Arg cExt 'TText

data ArgParseError
  = NotACommand Text.Text
  | NotAnInt Text.Text
  | NotExactly Text.Text Text.Text
  deriving Show

instance PP.Pretty ArgParseError where
  pretty =
    \case
      NotACommand t -> PP.squotes (PP.pretty t) PP.<+> "is not a command"
      NotAnInt t -> PP.squotes (PP.pretty t) PP.<+> "is not an integer"
      NotExactly e t -> PP.squotes (PP.pretty t) PP.<+> "is not" PP.<+> PP.squotes (PP.pretty e)

newtype ArgParser cExt t
  = ArgParser { _runArgParser :: Rgx.TokenParser Text.Text ArgParseError (Arg cExt) t }

argParser :: (Text.Text -> Either ArgParseError (Arg cExt t)) -> ArgParser cExt t
argParser = ArgParser . Rgx.TokenParser

-- | Helper, not exported
maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e =
  \case
    Nothing -> Left e
    Just a -> Right a

breakpoint :: ArgParser cExt 'TBreakpoint
breakpoint =
  argParser (Right . ABreakpoint . BreakFunction . W4.functionNameFromText)

function :: ArgParser cExt 'TFunction
function =
  argParser (Right . AFunction .  W4.functionNameFromText)

command :: Cmd.CommandExt cExt -> ArgParser cExt 'TCommand
command cExt = argParser (\t -> ACommand <$> maybeToEither (NotACommand t) (Cmd.parse cExt t))

exactly :: SymbolRepr s -> ArgParser cExt ('TExactly s)
exactly s =
  argParser $ \t ->
    if t == symbolRepr s
    then Right (AExactly s)
    else Left (NotExactly (symbolRepr s) t)

int :: ArgParser cExt 'TInt
int = argParser (\t -> AInt <$> maybeToEither (NotAnInt t) (readMaybe (Text.unpack t)))

path :: ArgParser cExt 'TPath
path = argParser (Right . APath)

text :: ArgParser cExt 'TText
text = argParser (Right . AText)

parser :: Cmd.CommandExt cExt -> ArgTypeRepr t -> ArgParser cExt t
parser cExt =
  \case
    TBreakpointRepr -> breakpoint
    TCommandRepr -> command cExt
    TExactlyRepr s -> exactly s
    TFunctionRepr -> function
    TIntRepr -> int
    TPathRepr -> path
    TTextRepr -> text

convert ::
  Cmd.CommandExt cExt ->
  Rgx.RegexRepr ArgTypeRepr r ->
  Rgx.RegexRepr (ArgParser cExt) r
convert cExt = fmapFC (parser cExt)

match ::
  forall r cExt.
  Rgx.RegexRepr (ArgParser cExt) r ->
  [Text.Text] ->
  Either (Rgx.MatchError Text.Text ArgParseError) (Rgx.Match (Arg cExt) r)
match r toks =
  case Rgx.match @_ @_ @(Arg cExt) (coerce r) toks of
    Left e -> Left e
    Right (m, []) -> Right m
    Right (_, as) -> Left (Rgx.NotEmpty as)

derivative ::
  forall cExt r.
  Cmd.CommandExt cExt ->
  Text.Text ->
  Rgx.RegexRepr ArgTypeRepr r ->
  Rgx.DerivativeResult ArgTypeRepr (Arg cExt)
derivative cExt =
  Rgx.derivative
    (coerce @_ @(Rgx.TokenParser _ ArgParseError (Arg cExt) _) . parser cExt)

-- | Get the potential types that the regex assigns each argument, plus what it
-- would assign to the next one.
types ::
  forall r cExt.
  Cmd.CommandExt cExt ->
  Rgx.RegexRepr ArgTypeRepr r ->
  [Text.Text] ->
  (Map Text.Text (Seq (Some ArgTypeRepr)), Seq (Some ArgTypeRepr))
types cExt r =
  \case
    [] -> (Map.empty, Rgx.nextLits r)
    (t : ts) ->
      case derivative cExt t r of
        Rgx.DerivativeResult (Some r') _ ->
          let (m, final) = types cExt r' ts in
          (Map.insertWith (<>) t (Rgx.nextLits r) m, final)

usage :: Rgx.RegexRepr ArgTypeRepr r -> [PP.Doc ann]
usage r =
  Foldable.toList $
    fmap (\(Some r') -> Rgx.prettySugar " " PP.pretty r') (Rgx.liftOrs (Rgx.sugar r))
