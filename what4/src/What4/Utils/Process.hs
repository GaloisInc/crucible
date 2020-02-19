{-
Module           : What4.Utils.Process
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Rob Dockins <rdockins@galois.com>

Common utilities for running solvers and getting back results.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.Utils.Process
  ( withProcessHandles
  , resolveSolverPath
  , findSolverPath
  , filterAsync
  , startProcess
  , cleanupProcess
  ) where

import           Control.Exception
import           Control.Monad (void)
import qualified Data.Map as Map
import qualified Data.Text as T
import           System.IO
import           System.Exit (ExitCode)
import           System.Process hiding (cleanupProcess)

import           What4.BaseTypes
import           What4.Config
import qualified What4.Utils.Environment as Env
import           What4.Panic

-- | Utility function that runs a solver specified by the given
-- config setting within a context.  Errors can then be attributed
-- to the solver.
resolveSolverPath :: FilePath
               -> IO FilePath
resolveSolverPath path = do
  Env.findExecutable =<< Env.expandEnvironmentPath Map.empty path

findSolverPath :: ConfigOption (BaseStringType Unicode) -> Config -> IO FilePath
findSolverPath o cfg =
  do v <- getOpt =<< getOptionSetting o cfg
     resolveSolverPath (T.unpack v)

-- | This runs a given external binary, providing the process handle and handles to
-- input and output to the action.  It takes care to terminate the process if any
-- exception is thrown by the action.
withProcessHandles :: FilePath -- ^ Path to process
                   -> [String] -- ^ Arguments to process
                   -> Maybe FilePath -- ^ Working directory if any.
                   -> ((Handle, Handle, Handle, ProcessHandle) -> IO a)
                      -- ^ Action to run with process; should wait for process to terminate
                      -- before returning.
                   -> IO a
withProcessHandles path args mcwd action = do
  let onError (_,_,_,ph) = do
        -- Interrupt process; suppress any exceptions that occur.
        catchJust filterAsync (terminateProcess ph) (\(ex :: SomeException) ->
          hPutStrLn stderr $ displayException ex)

  bracket (startProcess path args mcwd)
          (void . cleanupProcess)
          (\hs -> onException (action hs) (onError hs))


-- | Close the connected process pipes and wait for the process to exit
cleanupProcess :: (Handle, Handle, Handle, ProcessHandle) -> IO ExitCode
cleanupProcess (h_in, h_out, h_err, ph) =
 do catchJust filterAsync
         (hClose h_in >> hClose h_out >> hClose h_err)
         (\(ex :: SomeException) -> hPutStrLn stderr $ displayException ex)
    waitForProcess ph

-- | Start a process connected to this one via pipes.
startProcess ::
  FilePath {-^ Path to executable -} ->
  [String] {-^ Command-line arguments -} ->
  Maybe FilePath {-^ Optional working directory -} ->
  IO (Handle, Handle, Handle, ProcessHandle)
  {-^ process stdin, process stdout, process stderr, process handle -}
startProcess path args mcwd =
  do let create_proc
            = (proc path args)
              { std_in  = CreatePipe
              , std_out = CreatePipe
              , std_err = CreatePipe
              , create_group = False
              , cwd = mcwd
              }
     createProcess create_proc >>= \case
       (Just in_h, Just out_h, Just err_h, ph) -> return (in_h, out_h, err_h, ph)
       _ -> panic "startProcess" $
               [ "Failed to exec: " ++ show path
               , "With the following arguments:"
               ] ++ args

-- | Filtering function for use with `catchJust` or `tryJust`
--   that filters out asynch exceptions so they are rethrown
--   instead of captured
filterAsync :: SomeException -> Maybe SomeException
filterAsync e
  | Just (_ :: AsyncException) <- fromException e = Nothing
  | otherwise = Just e
