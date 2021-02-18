{-# LANGUAGE TemplateHaskell #-}
module Lang.Crucible.Wasm.Utils where

import Control.Monad.IO.Class
import Control.Exception (Exception, throwIO)
import GHC.Stack

import Panic hiding (panic)
import qualified Panic

data CrucibleWasm = CrucibleWasm

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic CrucibleWasm

instance PanicComponent CrucibleWasm where
  panicComponentName _ = "Crucible-wasm"
  panicComponentIssues _ = "https://github.com/GaloisInc/crucible/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision


data Unimplemented = Unimplemented CallStack String
instance Show Unimplemented where
  show (Unimplemented stk msg) = "Unimplmenented! " ++ msg ++ "\n" ++ prettyCallStack stk
instance Exception Unimplemented

unimplemented :: (HasCallStack, MonadIO m) => String -> m a
unimplemented msg = liftIO (throwIO (Unimplemented callStack msg))

-- | Print debugging information
debug :: MonadIO m  => String -> m ()
debug msg = liftIO (putStrLn msg)
