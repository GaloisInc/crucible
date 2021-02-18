{- |
Module      : Lang.JVM.ProcessUtils
Description : Miscellaneous @process@-related utilities.
Copyright   : (c) Galois, Inc 2021
License     : BSD3
Maintainer  : rscott@galois.com
Stability   : provisional
-}

module Lang.JVM.ProcessUtils (readProcessExitIfFailure) where

import Control.Monad (when)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

-- | Invokes @readProcessWithExitCode@ with no standard input, and returns the
-- resulting standard output and standard error. If the exit code of the
-- process is not 'ExitSuccess', throw an exception with some information that
-- may be helpful to debug what went wrong.
readProcessExitIfFailure :: FilePath -> [String] -> IO (String, String)
readProcessExitIfFailure cmd args = do
  (ec, out, err) <- readProcessWithExitCode cmd args ""
  when (ec /= ExitSuccess) $
     fail $ unlines [ cmd ++ " returned non-zero exit code: " ++ show ec
                    , "Standard output:"
                    , out
                    , "Standard error:"
                    , err
                    ]
  pure (out, err)
