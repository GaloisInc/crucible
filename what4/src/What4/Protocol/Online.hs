{- |
Module      : What4.Protocol.Online
Copyright   : (c) Galois, Inc 2018
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

This module defines an API for interacting with
solvers that support online interaction modes.

-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module What4.Protocol.Online
  ( OnlineSolver(..)
  , SolverProcess(..)
  , killSolver
  , push
  , pop
  , reset
  , inNewFrame
  , check
  , getModel
  , checkAndGetModel
  , getSatResult
  , checkSatisfiable
  , checkSatisfiableWithModel
  ) where

import           Control.Exception
                   ( SomeException(..), bracket_, catch, try, displayException )
import           Control.Monad (void)
import qualified Data.Text.Lazy as LazyText
import           Data.ByteString(ByteString)
import           System.Exit
import           System.IO
import           System.Process
                   (ProcessHandle, interruptProcessGroupOf, waitForProcess)
import qualified System.IO.Streams as Streams

import What4.Expr
import What4.Interface (SolverEvent(..))
import What4.Protocol.SMTWriter
import What4.SatResult
import What4.Utils.HandleReader

-- | This class provides an API for starting and shutting down
--   connections to various different solvers that support
--   online interaction modes.
class SMTReadWriter solver => OnlineSolver scope solver where
  -- | Start a new solver process attached to the given `ExprBuilder`.
  startSolverProcess    :: ExprBuilder scope st fs -> IO (SolverProcess scope solver)
  -- | Shut down a solver process.  The process will be asked to shut down in
  --   a "polite" way, e.g., by sending an `(exit)` message, or by closing
  --   the process's `stdin`.  Use `killProcess` instead to shutdown a process
  --   via a signal.
  shutdownSolverProcess :: SolverProcess scope solver -> IO ()

-- | A live connection to a running solver process.
data SolverProcess scope solver = SolverProcess
  { solverConn  :: !(WriterConn scope solver)
    -- ^ Writer for sending commands to the solver

  , solverHandle :: !ProcessHandle
    -- ^ Handle to the solver process

  , solverStdin :: !Handle
    -- ^ Standard in for the solver process.

  , solverResponse :: !(Streams.InputStream ByteString)
    -- ^ Wrap the solver's stdout, for easier parsing of responses.

  , solverStderr :: !HandleReader
    -- ^ Standard error for the solver process

  , solverEvalFuns :: !(SMTEvalFunctions solver)
    -- ^ The functions used to parse values out of models.

  , solverLogFn :: SolverEvent -> IO ()

  , solverName :: String
  }


-- | An impolite way to shut down a solver.  Prefer to use
--   `shutdownSolverProcess`, unless the solver is unresponsive
--   or in some unrecoverable error state.
killSolver :: SolverProcess t solver -> IO ()
killSolver p =
  do catch (interruptProcessGroupOf (solverHandle p)) (\(_ :: SomeException) -> return ())
     void $ waitForProcess (solverHandle p)

-- | Check if the given formula is satisfiable in the current
--   solver state, without requesting a model.
checkSatisfiable ::
  SMTReadWriter solver =>
  SolverProcess scope solver ->
  String ->
  BoolExpr scope ->
  IO (SatResult ())
checkSatisfiable proc rsn p =
  do let c = solverConn proc
     p_smtexpr <- mkFormula c p
     inNewFrame c $
       do assumeFormula c p_smtexpr
          check proc rsn

-- | Check if the formula is satisifiable in the current
--   solver state.
--   The evaluation funciton can be used to query the model.
--   The model is valid only in the given continuation.
checkSatisfiableWithModel ::
  SMTReadWriter solver =>
  SolverProcess scope solver ->
  BoolExpr scope ->
  String ->
  (SatResult (GroundEvalFn scope) -> IO a) ->
  IO a
checkSatisfiableWithModel proc p rsn k =
  do let c = solverConn proc
     p_smtexpr <- mkFormula c p
     inNewFrame c $
       do assumeFormula c p_smtexpr
          res <- check proc rsn
          case res of
            Sat _ -> do f <- smtExprGroundEvalFn c (solverEvalFuns proc)
                        k (Sat f)
            Unsat -> k Unsat
            Unknown -> k Unknown

--------------------------------------------------------------------------------
-- Basic solver interaction.

reset :: SMTReadWriter s => WriterConn t s -> IO ()
reset c = do resetEntryStack c
             addCommand c (resetCommand c)

-- | Push a new solver assumption frame.
push :: SMTReadWriter s => WriterConn t s -> IO ()
push c = do pushEntryStack c
            addCommand c (pushCommand c)

-- | Pop a previous solver assumption frame.
pop :: SMTReadWriter s => WriterConn t s -> IO ()
pop c = do popEntryStack c
           addCommand c (popCommand c)

-- | Perform an action in the scope of a solver assumption frame.
inNewFrame :: SMTReadWriter s => WriterConn t s -> IO a -> IO a
inNewFrame c m = bracket_ (push c) (pop c) m

-- | Send a check command to the solver, and get the SatResult without asking
--   a model.
check :: SMTReadWriter solver => SolverProcess scope solver -> String -> IO (SatResult ())
check p rsn =
  do let c = solverConn p
     solverLogFn p
       SolverStartSATQuery
       { satQuerySolverName = solverName p
       , satQueryReason = rsn
       }
     addCommand c (checkCommand c)
     sat_result <- getSatResult p
     solverLogFn p
       SolverEndSATQuery
       { satQueryResult = sat_result
       , satQueryError = Nothing
       }
     return sat_result

-- | Send a check command to the solver and get the model in the case of a SAT result.
--
-- This may fail if the solver terminates.
checkAndGetModel :: SMTReadWriter solver => SolverProcess scope solver -> String -> IO (SatResult (GroundEvalFn scope))
checkAndGetModel yp rsn = do
  sat_result <- check yp rsn
  case sat_result of
    Unsat   -> return $! Unsat
    Unknown -> return $! Unknown
    Sat () -> Sat <$> getModel yp

-- | Following a successful check-sat command, build a ground evaulation function
--   that will evaluate terms in the context of the current model.
getModel :: SMTReadWriter solver => SolverProcess scope solver -> IO (GroundEvalFn scope)
getModel p = smtExprGroundEvalFn (solverConn p)
             $ smtEvalFuns (solverConn p) (solverResponse p)

-- | Get the sat result from a previous SAT command.
getSatResult :: SMTReadWriter s => SolverProcess t s -> IO (SatResult ())
getSatResult yp = do
  let ph = solverHandle yp
  let err_reader = solverStderr yp
  sat_result <- try (smtSatResult yp (solverResponse yp))
  case sat_result of
    Right ok -> return ok

    Left (SomeException e) ->
       do txt <- readAllLines err_reader
          -- Interrupt process; suppress any exceptions that occur.
          catch (interruptProcessGroupOf ph) (\(_ :: IOError) -> return ())
          -- Wait for process to end
          ec <- waitForProcess ph
          let ec_code = case ec of
                          ExitSuccess -> 0
                          ExitFailure code -> code
          fail $ unlines
                  [ "The solver terminated with exit code "++
                                              show ec_code ++ ".\n"
                  , "*** exception: " ++ displayException e
                  , "*** standard error:"
                  , LazyText.unpack txt
                  ]
