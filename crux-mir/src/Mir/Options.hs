module Mir.Options
  ( MIROptions(..)
  , defaultMirOptions
  , mirConfig
  ) where

import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import           Data.Text (Text)
import qualified SimpleGetOpt as GetOpt

import           Crux.Config (Config(..))

data MIROptions = MIROptions
    { onlyPP       :: Bool
    , printCrucible :: Bool
    , showModel    :: Bool
    , assertFalse  :: Bool
    -- | Print only the result of evaluation, with no additional text.  On
    -- concrete programs, this should normally produce the exact same output as
    -- `rustc prog.rs && ./prog`.
    , printResultOnly :: Bool
    -- | Generate test overrides that recognize concurrency primitives
    -- and attempt to explore all interleaving executions
    , concurrency :: Bool
    , testFilter   :: Maybe Text
    , testSkipFilter :: Maybe Text
    , cargoTestFile :: Maybe FilePath
    , defaultRlibsDir :: FilePath
    -- ^ Directory to search for builds of `crux-mir`'s custom standard
    -- library, if `$CRUX_RUST_LIBRARY_PATH` is unset.  This option exists for
    -- the purposes of the `crux-mir-comp` test suite; there's no user-facing
    -- flag to set it.
    , mirJsonArgs     :: Seq String
    }

defaultMirOptions :: MIROptions
defaultMirOptions = MIROptions
    { onlyPP = False
    , printCrucible = False
    , showModel = False
    , assertFalse = False
    , concurrency = False
    , printResultOnly = False
    , testFilter = Nothing
    , testSkipFilter = Nothing
    , cargoTestFile = Nothing
    , defaultRlibsDir = "rlibs"
    , mirJsonArgs = Seq.empty
    }

mirConfig :: Config MIROptions
mirConfig = Config
    { cfgFile = pure defaultMirOptions
    , cfgEnv = []
    , cfgCmdLineFlag =
        [ GetOpt.Option []    ["print-mir"]
            "pretty-print mir and exit"
            (GetOpt.NoArg (\opts -> Right opts { onlyPP = True }))

        , GetOpt.Option []    ["print-crucible"]
            "pretty-print crucible after translation"
            (GetOpt.NoArg (\opts -> Right opts { printCrucible = True }))

        , GetOpt.Option []    ["print-result-only"]
            "print the result of evaluation and nothing else (used for concrete tests)"
            (GetOpt.NoArg (\opts -> Right opts { printResultOnly = True }))

        , GetOpt.Option ['m']  ["show-model"]
            "show model on counter-example"
            (GetOpt.NoArg (\opts -> Right opts { showModel = True }))

        , GetOpt.Option [] ["assert-false-on-error"]
            "when translation fails, assert false in output and keep going"
            (GetOpt.NoArg (\opts -> Right opts { assertFalse = True }))

        , GetOpt.Option [] ["concurrency"]
            "run with support for concurrency primitives"
            (GetOpt.NoArg (\opts -> Right opts { concurrency = True }))

        , GetOpt.Option []  ["test-filter"]
            "run only tests whose names contain this string"
            (GetOpt.ReqArg "string" (\v opts -> Right opts { testFilter = Just $ Text.pack v }))

        , GetOpt.Option []  ["test-skip-filter"]
            "run only tests whose names do not contain this string"
            (GetOpt.ReqArg "string" (\v opts -> Right opts { testSkipFilter = Just $ Text.pack v }))

        , GetOpt.Option []  ["cargo-test-file"]
            "treat trailing args as --test-filter instead of FILES, like `cargo test`; load program from this file instead (used by `cargo crux test`)"
            (GetOpt.ReqArg "file" (\v opts -> Right opts { cargoTestFile = Just v }))

        , GetOpt.Option [] ["mir-json-arg"]
            "pass an argument to mir-json (can be repeated)"
            (GetOpt.ReqArg "ARG" $ \v opts ->
                Right opts { mirJsonArgs = mirJsonArgs opts Seq.|> v })
        ]
    }
