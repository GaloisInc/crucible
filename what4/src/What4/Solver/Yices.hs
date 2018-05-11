------------------------------------------------------------------------
-- |
-- Module      : What4.Solver.Yices
-- Description : Solver adapter code for Yices
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- SMTWriter interface for Yices, using the Yices-specific input language.
-- This language shares many features with SMTLib2, but is not quite
-- compatible.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.Solver.Yices
  ( -- * Low-level interface
    Connection
  , newConnection
  , SMTWriter.assume
  , sendCheck
  , sendCheckExistsForall
  , eval
  , push
  , pop
  , inFreshFrame
  , setParam
  , setYicesParams
  , HandleReader
  , startHandleReader

  , yicesType
  , assertForall
  , efSolveCommand

    -- * Live connection
  , YicesProcess(..)
  , yicesEvalBool
  , check
  , checkAndGetModel

  , SMTWriter.addCommand
    -- * Solver adapter interface
  , yicesAdapter
  , runYicesInOverride
  , writeYicesFile
  , yicesPath
  , yicesOptions
  ) where

import           Control.Concurrent (ThreadId, forkIO, killThread)
import           Control.Concurrent.Chan
import           Control.Exception (assert, bracket, bracket_, catch, throwIO, try)
import           Control.Lens ((^.))
import           Control.Monad
import           Data.Bits
import           Data.Foldable (toList)
import           Data.Monoid
import           Data.Parameterized.NatRepr
import           Data.Ratio
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String (fromString)
import           Data.Text (Text)
import qualified Data.Text.IO as Text
import qualified Data.Text.Lazy as LazyText
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import           Data.Text.Lazy.Builder.Int (decimal)
import           System.Exit
import           System.IO
import           System.IO.Error
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.BaseTypes
import           What4.Config
import           What4.Solver.Adapter
import           What4.Concrete
import           What4.Interface
import           What4.ProblemFeatures
import           What4.SatResult
import qualified What4.Expr.Builder as B
import           What4.Expr.GroundEval
import           What4.Expr.VarIdentification
import           What4.Protocol.SMTLib2 (writeDefaultSMT2)
import           What4.Protocol.SMTWriter as SMTWriter
import qualified What4.Protocol.PolyRoot as Root
import           What4.Utils.Process

-- | This is a tag used to indicate that a 'WriterConn' is a connection
-- to a specific Yices process.
newtype Connection s = Connection ()

-- | Attempt to interpret a Config value as a Yices value.
asYicesConfigValue :: ConcreteVal tp -> Maybe Builder
asYicesConfigValue v = case v of
  ConcreteBool x ->
      return (if x then "true" else "false")
  ConcreteReal x -> 
      return $ decimal (numerator x) <> "/" <> decimal (denominator x)
  ConcreteInteger x ->
      return $ decimal x
  ConcreteString x ->
      return $ Builder.fromText x
  _ ->
      Nothing

------------------------------------------------------------------------
-- Expr

type Expr s = Term (Connection s)

instance Num (Term (Connection s)) where
  (+) = bin_app "+"
  (-) = bin_app "-"
  (*) = bin_app "*"
  negate x = term_app "-" [x]
  abs x    = ite (bin_app ">=" x 0) x (negate x)
  signum x = ite (bin_app "=" x 0) 0 $ ite (bin_app ">" x 0) 1 (negate 1)
  fromInteger i = T (decimal i)

decimal_term :: Integral a => a -> Term h
decimal_term i = T (decimal i)

width_term :: NatRepr n -> Term h
width_term w = decimal_term (widthVal w)

varBinding :: Text -> SMT_Type -> Builder
varBinding nm tp = Builder.fromText nm <> "::" <> unType (yicesType tp)

letBinding :: Text -> Term h -> Builder
letBinding nm t = app (Builder.fromText nm) [renderTerm t]

binder_app :: Builder -> [Builder] -> Term h -> Term h
binder_app _  []    t = t
binder_app nm (h:r) t = T (app nm [app_list h r, renderTerm t])

yicesLambda :: [(Text, SMT_Type)] -> Term h -> Term h
yicesLambda []   t = t
yicesLambda args t = T $ app "lambda" [ builder_list (renderArg <$> args), renderTerm t ]
  where renderArg :: (Text, SMT_Type) -> Builder
        renderArg (u,  tp) = Builder.fromText u <> "::" <> unType (yicesType tp)

instance SupportTermOps (Term (Connection s)) where
  boolExpr b = T $ if b then "true" else "false"
  notExpr x = term_app "not" [x]

  andAll [] = T "true"
  andAll [x] = x
  andAll xs = term_app "and" xs

  orAll [] = T "false"
  orAll [x] = x
  orAll xs = term_app "or" xs

  (.==) = bin_app "="
  (./=) = bin_app "/="
  ite c x y = term_app "if" [c, x, y]

  forallExpr vars t = binder_app "forall" (uncurry varBinding <$> vars) t
  existsExpr vars t = binder_app "exists" (uncurry varBinding <$> vars) t
  letExpr    vars t = binder_app "let"    (uncurry letBinding <$> vars) t

  sumExpr [] = 0
  sumExpr [e] = e
  sumExpr l = term_app "+" l

  termIntegerToReal = id
  termRealToInteger = id

  integerTerm i = T $ decimal i

  rationalTerm r | d == 1    = T $ decimal n
                 | otherwise = T $ app "/" [decimal n, decimal d]
    where n = numerator r
          d = denominator r

  (.<)  = bin_app "<"
  (.<=) = bin_app "<="
  (.>)  = bin_app ">"
  (.>=) = bin_app ">="

  bvTerm w u = term_app "mk-bv" [width_term w, decimal_term d]
    where d = toUnsigned w u

  bvNeg x = term_app "bv-neg" [x]
  bvAdd = bin_app "bv-add"
  bvSub = bin_app "bv-sub"
  bvMul = bin_app "bv-mul"

  bvSLe = bin_app "bv-sle"
  bvULe = bin_app "bv-le"

  bvSLt = bin_app "bv-slt"
  bvULt = bin_app "bv-lt"

  bvUDiv = bin_app "bv-div"
  bvURem = bin_app "bv-rem"
  bvSDiv = bin_app "bv-sdiv"
  bvSRem = bin_app "bv-srem"

  bvAnd  = bin_app "bv-and"
  bvOr   = bin_app "bv-or"
  bvXor  = bin_app "bv-xor"

  bvNot x = term_app "bv-not" [x]

  bvShl  = bin_app "bv-shl"
  bvLshr = bin_app "bv-lshr"
  bvAshr = bin_app "bv-ashr"

  -- Yices concatenates with least significant bit first.
  bvConcat x y = bin_app "bv-concat" x y

  bvExtract _ b n x = assert (n > 0) $
    let -- Get index of bit to end at (least-significant bit has index 0)
        end = decimal_term (b+n-1)
        -- Get index of bit to start at (least-significant bit has index 0)
        begin = decimal_term b
     in term_app "bv-extract"  [end, begin, x]

  arraySelect = smtFnApp
  arrayUpdate a i v =
    T $ app "update" [ renderTerm a, builder_list (renderTerm <$> i), renderTerm v ]

  structCtor args = term_app "mk-tuple" args
  structFieldSelect _ s i = term_app "select" [s, fromIntegral (i + 1)]

  realIsInteger x = term_app "is-int" [x]

  realSin = errorComputableUnsupported
  realCos = errorComputableUnsupported
  realATan2 = errorComputableUnsupported
  realSinh = errorComputableUnsupported
  realCosh = errorComputableUnsupported
  realExp = errorComputableUnsupported
  realLog = errorComputableUnsupported

  smtFnApp nm args = term_app (renderTerm nm) args
  smtFnUpdate = Nothing

  lambdaTerm = Just yicesLambda

errorComputableUnsupported :: a
errorComputableUnsupported = error "computable functions are not supported."

------------------------------------------------------------------------
-- YicesType

newtype YicesType = YicesType { unType :: Builder }

fnType :: [SMT_Type] -> SMT_Type -> YicesType
fnType [] tp = yicesType tp
fnType args tp = YicesType $ app "->" ((unType . yicesType) `fmap` (args ++ [tp]))

yicesType :: SMT_Type -> YicesType
yicesType tp =
  case tp of
    SMT_BoolType        -> YicesType "bool"
    SMT_BVType w        -> YicesType (app "bitvector" [fromString (show w)])
    SMT_IntegerType     -> YicesType "int"
    SMT_RealType        -> YicesType "real"
    SMT_ArrayType i e   -> fnType i e
    SMT_StructType flds -> YicesType (app "tuple" ((unType . yicesType <$> flds)))
    SMT_FnType flds res -> fnType flds res

------------------------------------------------------------------------
-- Command

assertForallCommand :: [(Text,YicesType)] -> Expr s -> Command (Connection s)
assertForallCommand vars e = Cmd $ app "assert" [renderTerm res]
 where res = binder_app "forall" (uncurry mkBinding <$> vars) e
       mkBinding nm tp = Builder.fromText nm <> "::" <> unType tp

checkCommand :: Command (Connection s)
checkCommand = Cmd "(check)"

efSolveCommand :: Command (Connection s)
efSolveCommand = Cmd "(ef-solve)"

evalCommand :: Term (Connection s)-> Command (Connection s)
evalCommand v = Cmd $ app "eval" [renderTerm v]

-- | Push a new assertion frame
pushCommand :: Command (Connection s)
pushCommand = Cmd "(push)"

-- | Pop the most recent assertion frame
popCommand :: Command (Connection s)
popCommand = Cmd "(pop)"

-- | Tell yices to show a model
showModelCommand :: Command (Connection s)
showModelCommand = Cmd "(show-model)"

checkExistsForallCommand :: Command (Connection s)
checkExistsForallCommand = Cmd "(ef-solve)"

-- | Create yices set command value.
setParamCommand :: Text -> Builder -> Command (Connection s)
setParamCommand nm v = Cmd $ app "set-param" [ Builder.fromText nm, v ]

------------------------------------------------------------------------
-- Connection

newConnection :: Handle
              -> ProblemFeatures -- ^ Indicates the problem features to support.
              -> B.SymbolVarBimap t
              -> IO (WriterConn t (Connection s))
newConnection h reqFeatures bindings = do
  let efSolver = reqFeatures `hasProblemFeature` useExistForall
  let nlSolver = reqFeatures `hasProblemFeature` useNonlinearArithmetic
  let features | efSolver  = useLinearArithmetic
               | nlSolver  = useNonlinearArithmetic
               | otherwise = useIntegerArithmetic
  let nm | efSolver  = "Yices ef-solver"
         | nlSolver  = "Yices nl-solver"
         | otherwise = "Yices"
  let featureIf True f = f
      featureIf False _ = noFeatures
  let features' = features
                  .|. featureIf efSolver useExistForall
                  .|. useStructs
                  .|. useSymbolicArrays
  conn <- newWriterConn h nm features' bindings (Connection ())
  return $! conn { supportFunctionDefs = True
                 , supportFunctionArguments = True
                 , supportQuantifiers = efSolver
                 }

instance SMTWriter (Connection s) where
  commentCommand _ b = Cmd (";; " <> b)

  assertCommand _ (T nm) = Cmd $ app "assert" [nm]

  declareCommand _ v args tp =
    Cmd $ app "define" [Builder.fromText v <> "::" <> unType (fnType args tp)]

  defineCommand v args tp t =
    Cmd $ app "define" [Builder.fromText v <> "::" <> unType (fnType (snd <$> args) tp)
                       , renderTerm (yicesLambda args t)
                       ]

  declareStructDatatype _ _ = return ()

------------------------------------------------------------------------
-- Translation code

-- | Send a check command to Yices.
sendCheck :: WriterConn t (Connection s) -> IO ()
sendCheck c = addCommand c checkCommand

sendCheckExistsForall :: WriterConn t (Connection s) -> IO ()
sendCheckExistsForall c = addCommand c checkExistsForallCommand

assertForall :: WriterConn t (Connection s) -> [(Text, YicesType)] -> Expr s -> IO ()
assertForall c vars e = addCommand c (assertForallCommand vars e)

setParam :: WriterConn t (Connection s) -> ConfigValue -> IO ()
setParam c (ConfigValue o val) =
  case configOptionNameParts o of
    [yicesName, nm] | yicesName == "yices" ->
      case asYicesConfigValue val of
        Just v ->
          addCommand c (setParamCommand nm v)
        Nothing ->
          fail $ unwords ["Unknown Yices parameter type:", show nm]
    _ -> fail $ unwords ["not a Yices parameter", configOptionName o]

setYicesParams :: WriterConn t (Connection s) -> Config -> IO ()
setYicesParams conn cfg = do
   params <- getConfigValues "yices" cfg
   forM_ params $ setParam conn

eval :: WriterConn t (Connection s) -> Term (Connection s) -> IO ()
eval c e = addCommand c (evalCommand e)

inFreshFrame :: WriterConn t (Connection s) -> IO a -> IO a
inFreshFrame c m = bracket_ (push c) (pop c) m

push :: WriterConn t (Connection s) -> IO ()
push c = do
  pushEntryStack c
  addCommand c pushCommand

pop :: WriterConn t (Connection s) -> IO ()
pop c = do
  popEntryStack c
  addCommand c popCommand

-- | Print a command to show the model.
sendShowModel :: WriterConn t (Connection s) -> IO ()
sendShowModel c = addCommand c showModelCommand

-- | A live connection to a running Yices process.
data YicesProcess t s =
  YicesProcess { yicesConn  :: !(WriterConn t (Connection s))
                   -- ^ Writer for sending commands to Yices
                 , yicesHandle :: !ProcessHandle
                   -- ^ Handle to Yices process
                 , yicesStdin :: !Handle
                   -- ^ Standard in for Yices process.
                 , yicesStdout :: !Handle
                   -- ^ Standard out for Yices process.
                 , yicesStderr :: !HandleReader
                   -- ^ Standard error for Yices process
                 }

-- | Get the sat result from a previous SAT command
getSatResult :: YicesProcess t s -> IO (SatResult ())
getSatResult yp = do
  let ph = yicesHandle yp
  let out_h = yicesStdout yp
  let err_reader = yicesStderr yp
  sat_result <- try $ hGetLine out_h
  case sat_result of
    Left e
      | isEOFError e -> do
          txt <- readAllLines err_reader
          -- Interrupt process; suppress any exceptions that occur.
          catch (interruptProcessGroupOf ph) (\(_ :: IOError) -> return ())
          -- Wait for process to end
          ec <- waitForProcess ph
          let ec_code = case ec of
                          ExitSuccess -> 0
                          ExitFailure code -> code
          fail $ "yices terminated with exit code "++ show ec_code ++ ".\n"
              ++ LazyText.unpack txt
      | otherwise ->  do
          throwIO e
    Right "unsat" ->
      return $! Unsat
    Right "sat" -> do
      return $! Sat ()
    Right "unknown" ->
      return $! Unknown
    Right kword ->
      fail $ "Unexpected result value from yices check: " ++ kword

-- | Send a check command to Yices and get the status.
--
-- This may fail if Yices terminates.
check :: YicesProcess t s -> IO (SatResult ())
check yp = do
  sendCheck (yicesConn yp)
  getSatResult yp

getModel :: YicesProcess t s -> IO (GroundEvalFn t)
getModel yp = do
  let evalReal tm = do
        eval (yicesConn yp) tm
        l <- Text.hGetLine (yicesStdout yp)
        case Root.fromYicesText l of
          Nothing -> do
            fail $ "Could not parse real value returned by yices:\n  " ++ show l
          Just r -> pure $ Root.approximate r
  let evalFns = SMTEvalFunctions { smtEvalBool = yicesEvalBool yp
                                 , smtEvalBV   = yicesEvalBV yp
                                 , smtEvalReal = evalReal
                                 , smtEvalBvArray = Nothing
                                 }
  smtExprGroundEvalFn (yicesConn yp) evalFns

-- | Send a check command to Yices and get the model.
--
-- This may fail if Yices terminates.
checkAndGetModel :: YicesProcess t s -> IO (SatResult (GroundEvalFn t))
checkAndGetModel yp = do
  sat_result <- check yp
  case sat_result of
    Unsat   -> return $! Unsat
    Unknown -> return $! Unknown
    Sat () -> Sat <$> getModel yp

-- | Call eval to get a Boolean term.
yicesEvalBool :: YicesProcess t s -> Term (Connection s) -> IO Bool
yicesEvalBool yp tm = do
  eval (yicesConn yp) tm
  l <- Text.hGetLine (yicesStdout yp)
  case l of
    "true"  -> return $! True
    "false" -> return $! False
    _ -> do
      fail $ "Could not parse yices value " ++ show l ++ " as a Boolean."

-- | Send eval command and get result back.
yicesEvalBV :: YicesProcess t s
               -> Int -- ^ Width of  expression
               -> Term (Connection s)  -- ^ Term to get value of
               -> IO Integer
yicesEvalBV yp w tm = do
  eval (yicesConn yp) tm
  l <- hGetLine (yicesStdout yp)
  case l of
    '0' : 'b' : nm -> readBit w nm
    _ -> fail "Could not parse value returned by yices as bitvector."

readBit :: Monad m => Int -> String -> m Integer
readBit w0 = go 0 0
  where go n v "" = do
          when (n /= w0) $ fail "Value has a different number of bits than we expected."
          return v
        go n v (c:r) = do
          case c of
            '0' -> go (n+1) (v `shiftL` 1)       r
            '1' -> go (n+1) ((v `shiftL` 1) + 1) r
            _ -> fail "Not a bitvector."

{-
-- | Parse a Yices Real value
yicesRealValue :: Monad m => Text -> m Rational
yicesRealValue (
    -- Read an integer
  | [(r,"")] <- readDecimal v =
    return r
    -- Divison case means we have a rational.
  | (f,(_:t)) <- break (\c -> c == '/') v
  , [(n,"")] <- reads f
  , [(d,"")] <- reads t =
    return (n % d)
  | otherwise =
  fail $ "Could not parse solver value " ++ v ++ " as a real."
yicesRealValue _ =
  fail "Could not parse solver value as a real."
-}

------------------------------------------------------------------
-- SolverAdapter interface

yicesSMT2Features :: ProblemFeatures
yicesSMT2Features
  =   useComputableReals
  .|. useIntegerArithmetic
  .|. useBitvectors
  .|. useQuantifiers
  .|. useSymbolicArrays

yicesAdapter :: SolverAdapter t
yicesAdapter =
   SolverAdapter
   { solver_adapter_name = "yices"
   , solver_adapter_config_options = yicesOptions
   , solver_adapter_check_sat = \sym logLn p cont ->
       runYicesInOverride sym logLn p (cont . fmap (\x -> (x,Nothing)))
   , solver_adapter_write_smt2 =
       writeDefaultSMT2 () "YICES"  yicesSMT2Features
   }

-- | Path to yices
yicesPath :: ConfigOption BaseStringType
yicesPath = configOption knownRepr "yices_path"

-- | Path to yices
yicesEfSolver :: ConfigOption BaseBoolType
yicesEfSolver = configOption knownRepr "yices_ef-solver"

yicesOptions :: [ConfigDesc]
yicesOptions =
  [ mkOpt
      yicesPath
      executablePathOptSty
      (Just (PP.text "Yices executable path"))
      (Just (ConcreteString "yices"))
  , booleanOpt' yicesEfSolver
  ]
  ++ yicesInternalOptions

yicesBranchingChoices :: Set Text
yicesBranchingChoices = Set.fromList
  [ "default"
  , "negative"
  , "positive"
  , "theory"
  , "th-pos"
  , "th-neg"
  ]

yicesEFGenModes :: Set Text
yicesEFGenModes = Set.fromList
  [ "auto"
  , "none"
  , "substitution"
  , "projection"
  ]

booleanOpt :: String -> ConfigDesc
booleanOpt nm = booleanOpt' (configOption BaseBoolRepr ("yices."++nm))

booleanOpt' :: ConfigOption BaseBoolType -> ConfigDesc
booleanOpt' o =
  mkOpt o
        boolOptSty
        Nothing
        Nothing

floatWithRangeOpt :: String -> Rational -> Rational -> ConfigDesc
floatWithRangeOpt nm lo hi =
  mkOpt (configOption BaseRealRepr $ "yices."++nm)
        (realWithRangeOptSty (Inclusive lo) (Inclusive hi))
        Nothing
        Nothing

floatWithMinOpt :: String -> Bound Rational -> ConfigDesc
floatWithMinOpt nm lo =
  mkOpt (configOption BaseRealRepr $ "yices."++nm)
        (realWithMinOptSty lo)
        Nothing
        Nothing

intWithRangeOpt :: String -> Integer -> Integer -> ConfigDesc
intWithRangeOpt nm lo hi =
  mkOpt (configOption BaseIntegerRepr $ "yices."++nm)
        (integerWithRangeOptSty (Inclusive lo) (Inclusive hi))
        Nothing
        Nothing

enumOpt :: String -> Set Text -> ConfigDesc
enumOpt nm xs =
  mkOpt (configOption BaseStringRepr $ "yices."++nm)
        (enumOptSty xs)
        Nothing
        Nothing

yicesInternalOptions :: [ConfigDesc]
yicesInternalOptions =
  [ booleanOpt "var-elim"
  , booleanOpt "arith-elim"
  , booleanOpt "flatten"
  , booleanOpt "learn-eq"
  , booleanOpt "keep-ite"
  , booleanOpt "fast-restarts"

  , intWithRangeOpt   "c-threshold" 1 (2^(30::Int)-1)
  , floatWithMinOpt   "c-factor"    (Inclusive 1)
  , intWithRangeOpt   "d-threshold" 1 (2^(30::Int)-1)
  , floatWithRangeOpt "d-factor"    1 1.5
  , intWithRangeOpt   "r-threshold" 1 (2^(30::Int)-1)
  , floatWithRangeOpt "r-fraction"  0 1
  , floatWithMinOpt   "r-factor"    (Inclusive 1)

  , floatWithRangeOpt "var-decay"  0 1
  , floatWithRangeOpt "randomness" 0 1
  , intWithRangeOpt   "random-seed" (negate (2^(30::Int)-1)) (2^(30::Int)-1)
  , enumOpt           "branching"   yicesBranchingChoices
  , floatWithRangeOpt "clause-decay" 0 1
  , booleanOpt        "cache-tclauses"
  , intWithRangeOpt   "tclause-size" 1 (2^(30::Int)-1)
  , booleanOpt        "dyn-ack"
  , booleanOpt        "dyn-bool-ack"

  , intWithRangeOpt   "max-ack"                1 (2^(30::Int)-1)
  , intWithRangeOpt   "max-bool-ack"           1 (2^(30::Int)-1)
  , intWithRangeOpt   "aux-eq-quota"           1 (2^(30::Int)-1)
  , floatWithMinOpt   "aux-eq-ratio"           (Exclusive 0)
  , intWithRangeOpt   "dyn-ack-threshold"      1 (2^(16::Int)-1)
  , intWithRangeOpt   "dyn-bool-ack-threshold" 1 (2^(16::Int)-1)
  , intWithRangeOpt   "max-interface-eqs"      1 (2^(30::Int)-1)
  , booleanOpt        "eager-lemmas"
  , booleanOpt        "simplex-prop"
  , intWithRangeOpt   "prop-threshold"         1 (2^(30::Int)-1)
  , booleanOpt        "simplex-adjust"
  , intWithRangeOpt   "bland-threshold"        1 (2^(30::Int)-1)
  , booleanOpt        "icheck"
  , intWithRangeOpt   "icheck-period"          1 (2^(30::Int)-1)
  , intWithRangeOpt   "max-update-conflicts"   1 (2^(30::Int)-1)
  , intWithRangeOpt   "max-extensionality"     1 (2^(30::Int)-1)
  , booleanOpt        "bvarith-elim"
  , booleanOpt        "optimistic-fcheck"

  , booleanOpt        "ef-flatten-iff"
  , booleanOpt        "ef-flatten-ite"
  , enumOpt           "ef-gen-mode"  yicesEFGenModes
  , intWithRangeOpt   "ef-max-iters"           1 (2^(30::Int)-1)
  , intWithRangeOpt   "ef-max-samples"         0 (2^(30::Int)-1)
  ]

-- | This checks that the element is in a logic fragment supported by Yices,
-- and returns whether the exists-forall solver should be used.
checkSupportedByYices :: B.BoolExpr t -> IO ProblemFeatures
checkSupportedByYices p = do
  let varInfo = predicateVarInfo p

  -- Check no errors where reported in result.
  let errors = toList (varInfo^.varErrors)
  when (not (null errors)) $ do
    fail $ show $ PP.text "This formula is not supported by yices:" PP.<$$>
           PP.indent 2 (PP.vcat errors)

  return $! varInfo^.problemFeatures

-- | Write a yices file that checks the satisfiability of the given predicate.
writeYicesFile :: B.ExprBuilder t st -- ^ Builder for getting current bindings.
               -> FilePath           -- ^ Path to file
               -> B.BoolExpr t       -- ^ Predicate to check
               -> IO ()
writeYicesFile sym path p = do
  withFile path WriteMode $ \h -> do
    let cfg = getConfiguration sym
    let varInfo = predicateVarInfo p
    -- check whether to use ef-solve
    let features = varInfo^.problemFeatures
    let efSolver = features `hasProblemFeature` useExistForall

    bindings <- B.getSymbolVarBimap sym

    c <- newConnection h features bindings
    setYicesParams c cfg
    assume c p
    if efSolver then
      addCommand c efSolveCommand
    else
      sendCheck c
    sendShowModel c

-- | Wrapper to help with reading from another process's standard out and stderr.
--
-- We want to be able to read from another process's stderr and stdout without
-- causing the process to stall because 'stdout' or 'stderr' becomes full.  This
-- data type will read from either of the handles, and buffer as much data as needed
-- in the queue.  It then provides a line-based method for reading that data as
-- strict bytestrings.
data HandleReader = HandleReader { hrChan :: !(Chan (Maybe Text))
                                 , hrHandle :: !Handle
                                 , hrThreadId :: !ThreadId
                                 }

streamLines :: Chan (Maybe Text) -> Handle -> IO ()
streamLines c h = do
  ln <- Text.hGetLine h
  writeChan c (Just ln)
  streamLines c h

-- | Create a new handle reader for reading the given handle.
startHandleReader :: Handle -> IO HandleReader
startHandleReader h = do
  c <- newChan
  let handle_err e
        | isEOFError e = do
            writeChan c Nothing
        | otherwise = do
            hPutStrLn stderr $ show (ioeGetErrorType e)
            hPutStrLn stderr $ show e
  tid <- forkIO $ streamLines c h `catch` handle_err

  return $! HandleReader { hrChan     = c
                         , hrHandle   = h
                         , hrThreadId = tid
                         }


-- | Stop the handle reader; cannot be used afterwards.
stopHandleReader :: HandleReader -> IO ()
stopHandleReader hr = do
  killThread (hrThreadId hr)
  hClose (hrHandle hr)

-- | Run an execution with a handle reader and stop it wheen down
withHandleReader :: Handle -> (HandleReader -> IO a) -> IO a
withHandleReader h = bracket (startHandleReader h) stopHandleReader

readNextLine :: HandleReader -> IO (Maybe Text)
readNextLine hr = do
  mr <- readChan (hrChan hr)
  case mr of
    -- Write back 'Nothing' because thread should have terminated.
    Nothing -> writeChan (hrChan hr) Nothing
    Just{} -> return()
  return mr

readAllLines :: HandleReader -> IO LazyText.Text
readAllLines hr = go LazyText.empty
  where go :: LazyText.Text -> IO LazyText.Text
        go prev = do
          mr <- readNextLine hr
          case mr of
            Nothing -> return prev
            Just e -> go $! prev `LazyText.append` (LazyText.fromStrict e)
                                 `LazyText.snoc` '\n'

-- | Run writer and get a yices result.
runYicesInOverride :: B.ExprBuilder t st
                   -> (Int -> String -> IO ())
                   -> B.BoolExpr t
                   -> (SatResult (GroundEvalFn t) -> IO a)
                   -> IO a
runYicesInOverride sym logLn condition resultFn = do
  let cfg = getConfiguration sym
  yices_path <- findSolverPath yicesPath cfg
  logLn 2 "Calling Yices to check sat"
  -- Check Problem features
  features <- checkSupportedByYices condition
  let efSolver = features `hasProblemFeature` useExistForall
  let nlSolver = features `hasProblemFeature` useNonlinearArithmetic
  let args | efSolver  = ["--mode=ef"]
           | nlSolver  = ["--logic=QF_NRA"]
           | otherwise = ["--mode=one-shot"]
  withProcessHandles yices_path args Nothing $ \(in_h, out_h, err_h, ph) -> do
    -- Log stderr to output.
    withHandleReader err_h $ \err_reader -> do

      -- Create new connection for sending commands to yices.
      bindings <- B.getSymbolVarBimap sym
      c <- newConnection in_h features bindings
      -- Write yices parameters.
      setYicesParams c cfg
      -- Assert condition
      assume c condition

      logLn 2 "Running check sat"
      if efSolver then
        addCommand c efSolveCommand
      else
        sendCheck c
      let yp = YicesProcess { yicesConn = c
                            , yicesHandle = ph
                            , yicesStdin  = in_h
                            , yicesStdout = out_h
                            , yicesStderr = err_reader
                            }
      sat_result <- getSatResult yp
      r <-
         case sat_result of
           Unsat -> resultFn Unsat
           Unknown -> resultFn Unknown
           Sat () -> resultFn . Sat =<< getModel yp
      -- Close input stream.
      hClose in_h

      logLn 2 "Waiting for yices to terminate"
      txt <- readAllLines err_reader

      ec <- waitForProcess ph
      case ec of
        ExitSuccess -> do
          logLn 2 "Yices terminated."
          return r
        ExitFailure exit_code -> do
          fail $ "yices exited with unexpected code " ++ show exit_code ++ "\n"
              ++ LazyText.unpack txt
