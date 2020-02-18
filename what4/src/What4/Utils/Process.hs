{-
Module           : What4.Utils.Process
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Rob Dockins <rdockins@galois.com>

Common utilities for running solvers and getting back results.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module What4.Utils.Process
  ( withProcessHandles
  , resolveSolverPath
  , findSolverPath
  ) where

import           Control.Exception
import           Control.Monad (void)
import qualified Data.Map as Map
import qualified Data.Text as T
import           System.IO
import           System.Process

import           What4.BaseTypes
import           What4.Config
import qualified What4.Utils.Environment as Env

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
  let create_proc
        = (proc path args)
          { std_in  = CreatePipe
          , std_out = CreatePipe
          , std_err = CreatePipe
          , create_group = False
          , delegate_ctlc = True
          , cwd = mcwd
          }
  let startProcess = do
        x <- createProcess create_proc
        case x of
          (Just in_h, Just out_h, Just err_h, ph) -> return (in_h,out_h,err_h,ph)
          _ -> fail "Internal error in withProcessHandles: Failed to create handle."
  let cleanup (in_h,out_h,err_h,ph) = do
        catch (do hClose in_h
                  hClose out_h
                  hClose err_h
                  void $ waitForProcess ph)
              (\(_ :: SomeException) -> return ())
  let onError (_,_,_,ph) = do
        -- Interrupt process; suppress any exceptions that occur.
        catch (terminateProcess ph) (\(_ :: SomeException) -> return ())

  bracket startProcess cleanup (\hs -> onException (action hs) (onError hs))
