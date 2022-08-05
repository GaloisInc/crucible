{-
Module       : UCCrux.LLVM.Context.App
Description  : Application read-only global context/configuration.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Context.App
  ( AppContext,
    makeAppContext,
    log,
    soundness
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens (Lens', lens)
import           Data.Text (Text)

import           UCCrux.LLVM.Logging (Verbosity)
import qualified UCCrux.LLVM.Logging as Log (verbosityToInt, log)
import           UCCrux.LLVM.Soundness (Soundness)
{- ORMOLU_ENABLE -}

data AppContext = AppContext
  { soundness :: Soundness,
    _log :: Verbosity -> Text -> IO ()
  }

doLog :: Verbosity -> Verbosity -> Text -> IO ()
doLog maxVerb msgVerb msg =
  if Log.verbosityToInt msgVerb <= Log.verbosityToInt maxVerb
    then Log.log msgVerb msg
    else pure ()

log :: Lens' AppContext (Verbosity -> Text -> IO ())
log = lens _log (\s v -> s {_log = v})

makeAppContext :: Soundness -> Verbosity -> AppContext
makeAppContext sound verb = AppContext sound (doLog verb)
