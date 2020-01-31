------------------------------------------------------------------------
-- |
-- module           : What4.Solver.DReal
-- Description      : Interface for running dReal
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides an interface for running dReal and parsing
-- the results back.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
module What4.Solver.DReal
  ( DReal
  , DRealBindings
  , ExprRangeBindings
  , getAvgBindings
  , getBoundBindings
  , drealPath
  , drealOptions
  , drealAdapter
  , writeDRealSMT2File
  , runDRealInOverride
  ) where

import           Control.Concurrent
import           Control.Exception
import           Control.Lens(folded)
import           Control.Monad
import           Data.Attoparsec.ByteString.Char8 hiding (try)
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import           Data.Char hiding (isSpace)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import           Numeric
import           System.Directory (doesFileExist)
import           System.Exit
import           System.FilePath
import           System.IO
import           System.IO.Error
import qualified System.IO.Streams as Streams
import qualified System.IO.Streams.Attoparsec as Streams
import           System.IO.Temp
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.BaseTypes
import           What4.Config
import           What4.Solver.Adapter
import           What4.Concrete
import           What4.Interface
import           What4.ProblemFeatures
import           What4.SatResult
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Protocol.SMTWriter as SMTWriter
import           What4.Utils.Process
import           What4.Utils.Streams (logErrorStream)
import           What4.Utils.HandleReader

data DReal = DReal deriving Show

-- | Path to dReal
drealPath :: ConfigOption (BaseStringType Unicode)
drealPath = configOption knownRepr "dreal_path"

drealOptions :: [ConfigDesc]
drealOptions =
  [ mkOpt
      drealPath
      executablePathOptSty
      (Just (PP.text "Path to dReal executable"))
      (Just (ConcreteString "dreal"))
  ]

drealAdapter :: SolverAdapter st
drealAdapter =
  SolverAdapter
  { solver_adapter_name = "dreal"
  , solver_adapter_config_options = drealOptions
  , solver_adapter_check_sat = \sym logData ps cont ->
      runDRealInOverride sym logData ps $ \res ->
         case res of
           Sat (c,m) -> do
             evalFn <- getAvgBindings c m
             rangeFn <- getBoundBindings c m
             cont (Sat (evalFn, Just rangeFn))
           Unsat x -> cont (Unsat x)
           Unknown -> cont Unknown

  , solver_adapter_write_smt2 = writeDRealSMT2File
  }

instance SMT2.SMTLib2Tweaks DReal where
  smtlib2tweaks = DReal

writeDRealSMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t fs]
   -> IO ()
writeDRealSMT2File sym h ps = do
  bindings <- getSymbolVarBimap sym
  in_str <- Streams.encodeUtf8 =<< Streams.handleToOutputStream h
  c <- SMT2.newWriter DReal in_str SMTWriter.nullAcknowledgementAction "dReal"
          False useComputableReals False bindings
  SMT2.setProduceModels c True
  SMT2.setLogic c (SMT2.Logic "QF_NRA")
  forM_ ps (SMT2.assume c)
  SMT2.writeCheckSat c
  SMT2.writeExit c

type DRealBindings = Map Text (Maybe Rational, Maybe Rational)

parseDRealModel
   :: Handle
   -> IO DRealBindings
parseDRealModel h = do
   str <- BS.hGetContents h
   let ls = drop 1 $ UTF8.lines str
   Map.fromList <$> mapM parseDRealBinding ls

getAvgBindings :: SMT2.WriterConn t fs (SMT2.Writer DReal)
               -> DRealBindings
               -> IO (GroundEvalFn t fs)
getAvgBindings c m = do
  let evalBool _ = fail "dReal does not support Boolean vars"
      evalBV _ _ = fail "dReal does not support bitvectors."
      evalStr _ = fail "dReal does not support strings."
      evalReal tm = do
        return $ maybe 0 drealAvgBinding $ Map.lookup (Builder.toLazyText (SMT2.renderTerm tm)) m
      evalFloat _ = fail "dReal does not support floats."
  let evalFns = SMTWriter.SMTEvalFunctions { SMTWriter.smtEvalBool = evalBool
                                           , SMTWriter.smtEvalBV = evalBV
                                           , SMTWriter.smtEvalReal = evalReal
                                           , SMTWriter.smtEvalFloat = evalFloat
                                           , SMTWriter.smtEvalBvArray = Nothing
                                           , SMTWriter.smtEvalString = evalStr
                                           }
  SMTWriter.smtExprGroundEvalFn c evalFns

getMaybeEval :: ((Maybe Rational, Maybe Rational) -> Maybe Rational)
             -> SMT2.WriterConn t fs (SMT2.Writer DReal)
             -> DRealBindings
             -> IO (RealExpr t fs -> IO (Maybe Rational))
getMaybeEval proj c m = do
  let evalBool _ = fail "dReal does not return Boolean value"
      evalBV _ _ = fail "dReal does not return Bitvector values."
      evalStr _ = fail "dReal does not return string values."
      evalReal tm = do
        case proj =<< Map.lookup (Builder.toLazyText (SMT2.renderTerm tm)) m of
          Just v -> return v
          Nothing -> throwIO (userError "unbound")
      evalFloat _ = fail "dReal does not support floats."
  let evalFns = SMTWriter.SMTEvalFunctions { SMTWriter.smtEvalBool = evalBool
                                           , SMTWriter.smtEvalBV = evalBV
                                           , SMTWriter.smtEvalReal = evalReal
                                           , SMTWriter.smtEvalFloat = evalFloat
                                           , SMTWriter.smtEvalBvArray = Nothing
                                           , SMTWriter.smtEvalString = evalStr
                                           }
  GroundEvalFn evalFn <- SMTWriter.smtExprGroundEvalFn c evalFns
  let handler e | isUserError e
                , ioeGetErrorString e == "unbound" = do
        return Nothing
      handler e = throwIO e
  return $ \elt -> (Just <$> evalFn elt) `catch` handler

getBoundBindings :: SMT2.WriterConn t fs (SMT2.Writer DReal)
                 -> DRealBindings
                 -> IO (ExprRangeBindings t fs)
getBoundBindings c m = do
  l_evalFn <- getMaybeEval fst c m
  h_evalFn <- getMaybeEval snd c m
  return $ \e -> (,) <$> l_evalFn e <*> h_evalFn e

drealAvgBinding :: (Maybe Rational, Maybe Rational) -> Rational
drealAvgBinding (Nothing, Nothing) = 0
drealAvgBinding (Nothing, Just r)  = r
drealAvgBinding (Just r, Nothing)  = r
drealAvgBinding (Just r1, Just r2) = (r1+r2)/2

parseDRealBinding :: UTF8.ByteString -> IO (Text, (Maybe Rational, Maybe Rational))
parseDRealBinding str =
 case parseOnly dRealBinding str of
   Left e -> fail $ unlines ["unable to parse dReal model output line:", "  "++UTF8.toString str, e]
   Right (x,lo,hi) -> return (Text.pack (UTF8.toString x), (lo,hi))

dRealBinding :: Parser (UTF8.ByteString, Maybe Rational, Maybe Rational)
dRealBinding = do
    skipSpace

    nm <- takeWhile1 (not . isSpace)

    skipSpace
    _ <- char ':'
    skipSpace

    lo <- dRealLoBound

    skipSpace
    _ <- char ','
    skipSpace

    hi <- dRealHiBound

    skipSpace
    _ <- option ' ' (char ';')
    skipSpace
    endOfInput

    return (nm,lo,hi)

dRealLoBound :: Parser (Maybe Rational)
dRealLoBound = choice
   [ string "(-inf" >> return Nothing
   , do _ <- char '['
        sign <- option 1 (char '-' >> return (-1))
        num <- takeWhile1 (\c -> c `elem` ("0123456789+-eE." :: String))
        case readFloat (UTF8.toString num) of
          (x,""):_ -> return $ Just (sign * x)
          _ -> fail "expected rational bound"
   ]

dRealHiBound :: Parser (Maybe Rational)
dRealHiBound = choice
   [ string "inf)" >> return Nothing
   , do sign <- option 1 (char '-' >> return (-1))
        num <- takeWhile1 (\c -> c `elem` ("0123456789+-eE." :: String))
        _ <- char ']'
        case readFloat (UTF8.toString num) of
          (x,""):_ -> return $ Just (sign * x)
          _ -> fail "expected rational bound"
   ]


-- | Read next contiguous sequence or numbers or letters.
parseNextWord :: Parser String
parseNextWord = do
  skipSpace
  UTF8.toString <$> takeWhile1 (\c -> isAlphaNum c || c == '-')

runDRealInOverride
   :: ExprBuilder t st fs
   -> LogData
   -> [BoolExpr t fs]   -- ^ propositions to check
   -> (SatResult (SMT2.WriterConn t fs (SMT2.Writer DReal), DRealBindings) () -> IO a)
   -> IO a
runDRealInOverride sym logData ps modelFn = do
  p <- andAllOf sym folded ps
  solver_path <- findSolverPath drealPath (getConfiguration sym)
  logSolverEvent sym
    SolverStartSATQuery
    { satQuerySolverName = "dReal"
    , satQueryReason = logReason logData
    }
  withSystemTempDirectory "dReal.tmp" $ \tmpdir ->
      withProcessHandles solver_path ["--model", "--in", "--format", "smt2"] (Just tmpdir) $ \(in_h, out_h, err_h, ph) -> do

      -- Log stderr to output.
      err_stream <- Streams.handleToInputStream err_h
      void $ forkIO $ logErrorStream err_stream (logCallbackVerbose logData 2)

      -- Write SMTLIB to standard input.
      logCallbackVerbose logData 2 "Sending Satisfiability problem to dReal"
      -- dReal does not support (define-fun ...)
      bindings <- getSymbolVarBimap sym

      in_str  <-
        case logHandle logData of
          Nothing -> Streams.encodeUtf8 =<< Streams.handleToOutputStream in_h
          Just aux_h ->
            do aux_str <- Streams.handleToOutputStream aux_h
               Streams.encodeUtf8 =<< teeOutputStream aux_str =<< Streams.handleToOutputStream in_h

      c <- SMT2.newWriter DReal in_str SMTWriter.nullAcknowledgementAction "dReal"
             False useComputableReals False bindings

      -- Set the dReal default logic
      SMT2.setLogic c (SMT2.Logic "QF_NRA")
      SMT2.assume c p

      -- Create stream for output from solver.
      out_stream <- Streams.handleToInputStream out_h

      -- dReal wants to parse its entire input, all the way through <EOF> before it does anything
      -- Also (apparently) you _must_ include the exit command to get any response at all...
      SMT2.writeCheckSat c
      SMT2.writeExit c
      hClose in_h

      logCallbackVerbose logData 2 "Parsing result from solver"

      msat_result <- try $ Streams.parseFromStream parseNextWord out_stream

      -- dReal currently just dumps its model information into "output.model" in its
      -- working directory, so that is where we look for it
      let modelfile = tmpdir </> "output.model"

      res <-
        case msat_result of
          Left Streams.ParseException{} -> fail "Could not parse sat result."
          Right "unsat" -> return (Unsat ())
          Right "delta-sat" -> do
              ex <- doesFileExist modelfile
              m <- if ex
                      then withFile modelfile ReadMode parseDRealModel
                      -- if the model file does not exist, treat it as an empty file
                      -- containing no bindings
                      else return Map.empty
              return (Sat (c, m))
          Right sat_result -> do
            fail $ unlines ["Could not interpret result from solver:", sat_result]

      r <- modelFn res

      -- Check error code.
      logCallbackVerbose logData 2 "Waiting for dReal to exit"

      ec <- waitForProcess ph
      case ec of
        ExitSuccess -> do
          -- Return result.
          logCallbackVerbose logData 2 "dReal terminated."

          logSolverEvent sym
             SolverEndSATQuery
             { satQueryResult = forgetModelAndCore res
             , satQueryError  = Nothing
             }

          return r
        ExitFailure exit_code ->
          fail $ "dReal exited with unexpected code: " ++ show exit_code
