{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SAWScript.TopLevel (
    -- * TopLevel Monad
    TopLevel(..), RO(..), runTopLevel
  , io
  , getSharedContext
  , getJavaCodebase
  , getOptions
  ) where

import Control.Applicative (Applicative)
import Control.Monad.IO.Class
import Control.Monad.Reader

import Verifier.SAW.SharedTerm (SharedContext)
import qualified Verifier.Java.Codebase as JSS

import SAWScript.Options (Options)
import SAWScript.Utils (SAWCtx)


-- TopLevel Read-Only Environment.

data RO =
  RO
  { roSharedContext :: SharedContext SAWCtx
  , roJavaCodebase  :: JSS.Codebase
  , roOptions       :: Options
  }

newtype TopLevel a = TopLevel (ReaderT RO IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

runTopLevel :: TopLevel a -> RO -> IO a
runTopLevel (TopLevel m) = runReaderT m

io :: IO a -> TopLevel a
io = liftIO

getSharedContext :: TopLevel (SharedContext SAWCtx)
getSharedContext = TopLevel (asks roSharedContext)

getJavaCodebase :: TopLevel JSS.Codebase
getJavaCodebase = TopLevel (asks roJavaCodebase)

getOptions :: TopLevel Options
getOptions = TopLevel (asks roOptions)
