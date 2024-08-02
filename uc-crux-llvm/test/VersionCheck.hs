{-
Copyright        : (c) Galois, Inc 2023
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

Utilities for checking the version of Clang being used.
-}

{-# LANGUAGE ScopedTypeVariables #-}

module VersionCheck
  ( getClangVersion

  , VersionCheck(..)
  , showVC
  , vcTag
  , vcMajor
  , vcVersioning
  , mkVC
  , vcGE
  ) where

import           Control.Exception (SomeException, catches, Handler(..), IOException)
import           Control.Lens ((^.), (^?), _Right, to)
import           Data.Bifunctor (first)
import           Data.Char (isLetter)
import           Data.List (isInfixOf)
import qualified Data.Text as Text
import           Data.Text (Text)
import           Data.Versions (Versioning, versioning, prettyV, major)
import qualified GHC.IO.Exception as GE
import           System.Process (readProcess)

import           UCCrux.LLVM.Errors.Panic (panic)

-- lack of decipherable version is not fatal to running the tests
data VersionCheck = VC String (Either Text Versioning)

showVC :: VersionCheck -> String
showVC (VC nm v) = nm <> " " <> Text.unpack (either id prettyV v)

vcTag :: VersionCheck -> String
vcTag v@(VC nm _) = nm <> vcMajor v

vcMajor :: VersionCheck -> String
vcMajor (VC _ v) = either Text.unpack (^. major . to show) v

vcVersioning :: VersionCheck -> Either Text Versioning
vcVersioning (VC _ v) = v

mkVC :: String -> String -> VersionCheck
mkVC nm raw = let r = Text.pack raw in VC nm $ first (const r) $ versioning r

-- Check if a VersionCheck version is greater than or equal to the numeric
-- value of another version (represented as a Word).
vcGE :: VersionCheck -> Word -> Bool
vcGE vc verNum = (vcVersioning vc ^? (_Right . major)) >= Just verNum

getClangVersion :: FilePath -> IO VersionCheck
getClangVersion clangBin = do
  -- Determine which version of clang will be used for these tests.
  -- An exception (E.g. in the readProcess if clang is not found) will
  -- result in termination (test failure).  Uses partiality, but
  -- this is just tests, and failure is captured.
  let isVerLine = isInfixOf "clang version"
      dropLetter = dropWhile (all isLetter)
      -- Remove any characters that give `versions` parsers a hard time, such
      -- as tildes (cf. https://github.com/fosskers/versions/issues/62).
      -- These have been observed in the wild (e.g., 12.0.0-3ubuntu1~20.04.5).
      scrubProblemChars = filter (/= '~')

      headVersionLine :: [String] -> String
      headVersionLine ls =
        case ls of
          l:_ -> l
          [] -> panic
                  "getClangVersion"
                  ["`clang --version` output does not contain line with version"]

      headVersionWord :: [String] -> String
      headVersionWord ws =
        case ws of
          w:_ -> w
          [] -> panic
                  "getClangVersion"
                  ["`clang --version` output does not contain numeric version"]

      getVer (Right inp) =
        -- example inp: "clang version 10.0.1"
        scrubProblemChars $ headVersionWord $ dropLetter $ words $
        headVersionLine $ filter isVerLine $ lines inp
      getVer (Left full) = full
  mkVC "clang" . getVer <$> readProcessVersion clangBin

readProcessVersion :: String -> IO (Either String String)
readProcessVersion forTool =
  catches (Right <$> readProcess forTool [ "--version" ] "")
  [ Handler $ \(e :: IOException) ->
      if GE.ioe_type e == GE.NoSuchThing
      then return $ Left "[missing]" -- tool executable not found
      else do putStrLn $ "Warning: IO error attempting to determine " <> forTool <> " version:"
              print e
              return $ Left "unknown"
  , Handler $ \(e :: SomeException) -> do
      putStrLn $ "Warning: error attempting to determine " <> forTool <> " version:"
      print e
      return $ Left "??"
  ]
