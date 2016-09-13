------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Utils.Environemnt
-- Description      : Provides functions for finding an executable, and
--                    expanding a path with referenced to environment
--                    variables.
-- Copyright        : (c) Galois, Inc 2013
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- Provides functions for finding an executable, and expanding a path
-- with referenced to environment variables.
------------------------------------------------------------------------
module Lang.Crucible.Simulator.Utils.Environment
  ( findExecutable
  , expandEnvironmentPath
  ) where

import Control.Monad.IO.Class
import Data.Char
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import qualified System.Directory as Sys
import System.Environment
import System.FilePath

-- | Given a mapping of variables to values, this replaces
-- substrings of the form $VAR with the associated value
-- in a string.
expandVars :: Monad m => Map String String -> String -> m String
expandVars m = outsideVar id
  where -- Parse characters not part of a var.
        outsideVar :: Monad m => ShowS -> String -> m String
        outsideVar res s =
          case s of
            [] -> return (res [])
            '$' : '{' : r -> matchBracketedVar res id r
            '$' : c : r | isNumber c -> expandVar res (showChar c) r
            '$' : r -> matchVarName res id r
            c   : r -> outsideVar (res . showChar c) r

        -- Return true if this is a character.
        isVarChar :: Char -> Bool
        isVarChar '_' = True
        isVarChar c = isAlphaNum c

        matchVarName :: Monad m => ShowS -> ShowS -> String -> m String
        matchVarName res rnm s =
          case s of
            [] -> expandVar res rnm s
            c:r | isVarChar c -> matchVarName res (rnm . showChar c) r
                | otherwise -> expandVar res rnm s

        matchBracketedVar res rnm s =
          case s of
            [] -> fail "Missing '}' to close variable name."
            '}':r -> expandVar res rnm r
            c  :r -> matchBracketedVar res (rnm . showChar c) r
        expandVar res rnm r = do
          let nm = rnm []
          case Map.lookup nm m of
            Just v -> outsideVar (res . showString v) r
            Nothing -> fail $ "Could not find variable " ++ show nm
                              ++ " in environment."

expandEnvironmentPath :: Map String String
                      -> String
                      -> IO String
expandEnvironmentPath base_map path = do
  -- Get program name.
  prog_name <- getExecutablePath
  let prog_path = dropTrailingPathSeparator (dropFileName prog_name)
  let init_map = Map.fromList [ ("MSS_BINPATH", prog_path) ]
  -- Extend init_map with environment variables.
  env <- getEnvironment
  let expanded_map = foldl' (\m (k,v) -> Map.insert k v m) init_map env
  -- Return expanded path.
  expandVars (Map.union base_map expanded_map) path

-- | Find an executable from a string.
findExecutable :: MonadIO m
               => FilePath
                  -- ^ Path to expand
               -> m FilePath
findExecutable expanded_path = do
  -- Look for variable in expanded_path.
  mr <- liftIO $ Sys.findExecutable expanded_path
  case mr of
    Nothing -> fail $ "Could not find: " ++ expanded_path
    Just r -> return r
