{-# LANGUAGE Trustworthy, TemplateHaskell #-}
module Lang.Crucible.Panic
  (HasCallStack, Crucible, Panic, panic) where

import Panic hiding (panic)
import qualified Panic

data Crucible = Crucible

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic Crucible

instance PanicComponent Crucible where
  panicComponentName _ = "Crucible"
  panicComponentIssues _ = "https://github.com/GaloisInc/crucible/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision
