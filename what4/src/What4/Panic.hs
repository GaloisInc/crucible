{-# LANGUAGE Trustworthy, TemplateHaskell #-}
module What4.Panic
  (HasCallStack, What4, Panic, panic) where

import Panic hiding (panic)
import qualified Panic

data What4 = What4

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic What4

instance PanicComponent What4 where
  panicComponentName _ = "What4"
  panicComponentIssues _ = "https://github.com/GaloisInc/crucible/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision
