{- |
Module      : Lang.JVM.JavaTools
Description : Functionality for finding a Java executable and its properties.
Copyright   : (c) Galois, Inc 2021
License     : BSD3
Maintainer  : rscott@galois.com
Stability   : provisional
-}

module Lang.JVM.JavaTools
  ( findJavaIn, findJimageIn, findJavaToolIn
  , findJavaProperty
  , findJavaMajorVersion
  ) where

import Control.Monad (when)
import Data.List.Extra (dropPrefix, firstJust, stripInfix)
import Data.Maybe
import System.Directory
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

-- | @'findJavaIn' searchPaths@ searches for an executable named @java@ among
-- the directories in @searchPaths@. If @searchPaths@ is empty, then the @PATH@
-- is searched.
--
-- If the search finds at least one executable, then @Just@ the first result is
-- returned. If no executables are found, then @Nothing@ is returned.
findJavaIn :: [FilePath] -> IO (Maybe FilePath)
findJavaIn = findJavaToolIn "java"

-- | @'findJavaIn' searchPaths@ searches for an executable named @java@ among
-- the directories in @searchPaths@. If @searchPaths@ is empty, then the @PATH@
-- is searched.
--
-- If the search finds at least one executable, then @Just@ the first result is
-- returned. If no executables are found, then @Nothing@ is returned.
findJimageIn :: [FilePath] -> IO (Maybe FilePath)
findJimageIn = findJavaToolIn "jimage"

-- | @'findJavaToolIn' toolName searchPaths@ searches for an executable named
-- @toolName@ among the directories in @searchPaths@. If @searchPaths@ is
-- empty, then the @PATH@ is searched.
--
-- If the search finds at least one executable, then @Just@ the first result is
-- returned. If no executables are found, then @Nothing@ is returned.
findJavaToolIn :: FilePath -> [FilePath] -> IO (Maybe FilePath)
findJavaToolIn toolName searchPaths
  | null searchPaths = findExecutable toolName
  | otherwise        = listToMaybe <$> findExecutablesInDirectories searchPaths toolName

-- | @'findJavaProperty' javaPath prop@ invokes @javaPath@ to dump its system
-- properties (see <https://docs.oracle.com/javase/tutorial/essential/environment/sysprop.html>)
-- and attempts to find the value associated with the property named @prop@.
-- If such a value is found, then @Just@ that value is returned.
-- If no property named @prop@ exists, then @Nothing@ is returned.
--
-- This will throw an exception if @javaPath@'s system properties cannot be
-- determined.
findJavaProperty :: FilePath -> String -> IO (Maybe String)
findJavaProperty javaPath propertyNeedle = do
  (_stdOut, stdErr) <- readProcessExitIfFailure javaPath ["-XshowSettings:properties", "-version"]
  let propertyHaystacks = lines stdErr
  pure $ firstJust getProperty_maybe propertyHaystacks
  where
    -- Each Java system property, as reported by
    -- @java -XshowSettings:properties@, adheres to this template:
    --
    -- "  <prop> = <value>"
    --
    -- Note the leading whitespace. As a result, stripInfix is used to detect
    -- "<prop> = " in the middle of the string and obtain the <value> after it.
    getProperty_maybe :: String -> Maybe String
    getProperty_maybe propertyHaystack =
      snd <$> stripInfix (propertyNeedle ++ " = ") propertyHaystack

-- | @'findJavaMajorVersion' javaPath@ will consult @javaPath@ to find the
-- major version number corresponding to that Java release.
findJavaMajorVersion :: FilePath -> IO Int
findJavaMajorVersion javaPath = do
  mbVersionStr <- findJavaProperty javaPath "java.version"
  case mbVersionStr of
    Nothing         -> fail $ "Could not detect the version of Java at " ++ javaPath
    Just versionStr -> pure $ read $ takeMajorVersionStr $ dropOldJavaVersionPrefix versionStr
  where
    -- e.g., if the version number is "11.0.9.1", then just take the "11" part.
    takeMajorVersionStr :: String -> String
    takeMajorVersionStr = takeWhile (/= '.')

    -- Prior to Java 9, the leading version number was always 1. For example,
    -- Java 8 would use 1.8.<...>. We only care about the 8 part, so drop the
    -- leading 1. bit.
    dropOldJavaVersionPrefix :: String -> String
    dropOldJavaVersionPrefix = dropPrefix "1."

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
