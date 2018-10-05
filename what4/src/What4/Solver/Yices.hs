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
  , inNewFrame
  , setParam
  , setYicesParams
  , HandleReader
  , startHandleReader

  , yicesType
  , assertForall
  , efSolveCommand

    -- * Live connection
  , yicesEvalBool

  , SMTWriter.addCommand
    -- * Solver adapter interface
  , yicesAdapter
  , runYicesInOverride
  , writeYicesFile
  , yicesPath
  , yicesOptions
  ) where

import           Control.Exception (assert)
import           Control.Lens ((^.))
import           Control.Monad
import           Data.Bits
import           Data.ByteString (ByteString)
import           Data.Foldable (toList)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Data.Semigroup ( (<>) )
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String (fromString)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Text.Encoding (decodeUtf8',decodeUtf8)
import qualified Data.Text.Lazy as LazyText
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import           Data.Text.Lazy.Builder.Int (decimal)
import qualified Data.Text.Lazy.IO as Lazy
import           System.Exit
import           System.IO
import qualified System.IO.Streams as Streams
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
import           What4.Protocol.Online
import qualified What4.Protocol.PolyRoot as Root
import           What4.Utils.HandleReader
import           What4.Utils.Process

import Prelude


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

newtype YicesTerm s = T { renderTerm :: Builder }

term_app :: Builder -> [YicesTerm s] -> YicesTerm s
term_app o args = T (app o (renderTerm <$> args))

bin_app :: Builder -> YicesTerm s -> YicesTerm s -> YicesTerm s
bin_app o x y = term_app o [x,y]

type Expr s = YicesTerm s

instance Num (YicesTerm s) where
  (+) = bin_app "+"
  (-) = bin_app "-"
  (*) = bin_app "*"
  negate x = term_app "-" [x]
  abs x    = ite (bin_app ">=" x 0) x (negate x)
  signum x = ite (bin_app "=" x 0) 0 $ ite (bin_app ">" x 0) 1 (negate 1)
  fromInteger i = T (decimal i)

decimal_term :: Integral a => a -> YicesTerm s
decimal_term i = T (decimal i)

width_term :: NatRepr n -> YicesTerm s
width_term w = decimal_term (widthVal w)

varBinding :: Text -> Some TypeMap -> Builder
varBinding nm tp = Builder.fromText nm <> "::" <> unType (viewSome yicesType tp)

letBinding :: Text -> YicesTerm s -> Builder
letBinding nm t = app (Builder.fromText nm) [renderTerm t]

binder_app :: Builder -> [Builder] -> YicesTerm s -> YicesTerm s
binder_app _  []    t = t
binder_app nm (h:r) t = T (app nm [app_list h r, renderTerm t])

yicesLambda :: [(Text, Some TypeMap)] -> YicesTerm s -> YicesTerm s
yicesLambda []   t = t
yicesLambda args t = T $ app "lambda" [ builder_list (uncurry varBinding <$> args), renderTerm t ]

instance SupportTermOps (YicesTerm s) where
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

  letExpr    vars t = binder_app "let"    (uncurry letBinding <$> vars) t

  sumExpr [] = 0
  sumExpr [e] = e
  sumExpr l = term_app "+" l

  termIntegerToReal = id
  termRealToInteger = id

  integerTerm i = T $ decimal i

  intDiv x y = term_app "div" [x,y]
  intMod x y = term_app "mod" [x,y]
  intAbs x   = term_app "abs" [x]

  intDivisible x 0 = x .== integerTerm 0
  intDivisible x k = term_app "divides" [integerTerm (toInteger k), x]

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


  floatPZero _ = floatFail
  floatNZero _ = floatFail
  floatNaN   _ = floatFail
  floatPInf  _ = floatFail
  floatNInf  _ = floatFail

  floatNeg  _   = floatFail
  floatAbs  _   = floatFail
  floatSqrt _ _ = floatFail

  floatAdd _ _ _ = floatFail
  floatSub _ _ _ = floatFail
  floatMul _ _ _ = floatFail
  floatDiv _ _ _ = floatFail
  floatRem _ _   = floatFail
  floatMin _ _   = floatFail
  floatMax _ _   = floatFail

  floatFMA _ _ _ _ = floatFail

  floatEq   _ _ = floatFail
  floatFpEq _ _ = floatFail
  floatLe   _ _ = floatFail
  floatLt   _ _ = floatFail

  floatIsNaN     _ = floatFail
  floatIsInf     _ = floatFail
  floatIsZero    _ = floatFail
  floatIsPos     _ = floatFail
  floatIsNeg     _ = floatFail
  floatIsSubnorm _ = floatFail
  floatIsNorm    _ = floatFail

  floatCast       _ _ _ = floatFail
  floatRound      _ _   = floatFail
  floatFromBinary _ _   = floatFail
  bvToFloat       _ _ _ = floatFail
  sbvToFloat      _ _ _ = floatFail
  realToFloat     _ _ _ = floatFail
  floatToBV       _ _ _ = floatFail
  floatToSBV      _ _ _ = floatFail
  floatToReal     _ = floatFail

  fromText t = T (Builder.fromText t)

floatFail :: a
floatFail = error "Yices does not support IEEE-754 floating-point numbers"

errorComputableUnsupported :: a
errorComputableUnsupported = error "computable functions are not supported."

------------------------------------------------------------------------
-- YicesType

-- | Denotes a type in yices.
newtype YicesType = YicesType { unType :: Builder }

tupleType :: [YicesType] -> YicesType
tupleType flds = YicesType (app "tuple" (unType <$> flds))

boolType :: YicesType
boolType = YicesType "bool"

intType :: YicesType
intType = YicesType "int"

realType :: YicesType
realType = YicesType "real"

fnType :: [YicesType] -> YicesType -> YicesType
fnType [] tp = tp
fnType args tp = YicesType $ app "->" (unType `fmap` (args ++ [tp]))

yicesType :: TypeMap tp -> YicesType
yicesType BoolTypeMap    = boolType
yicesType NatTypeMap     = intType
yicesType IntegerTypeMap = intType
yicesType RealTypeMap    = realType
yicesType (BVTypeMap w)  = YicesType (app "bitvector" [fromString (show w)])
yicesType (FloatTypeMap _) = floatFail
yicesType ComplexToStructTypeMap = tupleType [realType, realType]
yicesType ComplexToArrayTypeMap  = fnType [boolType] realType
yicesType (PrimArrayTypeMap i r) = fnType (toListFC yicesType i) (yicesType r)
yicesType (FnArrayTypeMap i r)   = fnType (toListFC yicesType i) (yicesType r)
yicesType (StructTypeMap f)      = tupleType (toListFC yicesType f)

------------------------------------------------------------------------
-- Command

assertForallCommand :: [(Text,YicesType)] -> Expr s -> Command (Connection s)
assertForallCommand vars e = Cmd $ app "assert" [renderTerm res]
 where res = binder_app "forall" (uncurry mkBinding <$> vars) e
       mkBinding nm tp = Builder.fromText nm <> "::" <> unType tp


efSolveCommand :: Command (Connection s)
efSolveCommand = Cmd "(ef-solve)"

evalCommand :: Term (Connection s)-> Command (Connection s)
evalCommand v = Cmd $ app "eval" [renderTerm v]

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

newtype YicesCommand = Cmd Builder

type instance Term (Connection s) = YicesTerm s
type instance Command (Connection s) = YicesCommand

instance SMTWriter (Connection s) where
  forallExpr vars t = binder_app "forall" (uncurry varBinding <$> vars) t
  existsExpr vars t = binder_app "exists" (uncurry varBinding <$> vars) t

  arraySelect = smtFnApp
  arrayUpdate a i v =
    T $ app "update" [ renderTerm a, builder_list (renderTerm <$> i), renderTerm v ]

  commentCommand _ b = Cmd (";; " <> b)

  pushCommand _   = Cmd "(push)"
  popCommand _    = Cmd "(pop)"
  resetCommand _  = Cmd "(reset)"
  checkCommand _  = Cmd "(check)"
  setOptCommand _ x o = setParamCommand x o
  assertCommand _ (T nm) = Cmd $ app "assert" [nm]

  declareCommand _ v args rtp =
    Cmd $ app "define" [Builder.fromText v <> "::"
                        <> unType (fnType (toListFC yicesType args) (yicesType rtp))
                       ]

  defineCommand _ v args rtp t =
    Cmd $ app "define" [Builder.fromText v <> "::"
                         <> unType (fnType ((\(_,tp) -> viewSome yicesType tp) <$> args) (yicesType rtp))
                       , renderTerm (yicesLambda args t)
                       ]

  declareStructDatatype _ _ = return ()

  writeCommand conn (Cmd cmd) =
    Lazy.hPutStrLn (connHandle conn) (Builder.toLazyText cmd)

instance SMTReadWriter (Connection s) where
  smtEvalFuns conn resp =
    SMTEvalFunctions { smtEvalBool    = yicesEvalBool conn resp
                     , smtEvalBV      = \w -> yicesEvalBV w conn resp
                     , smtEvalReal    = yicesEvalReal conn resp
                     , smtEvalFloat   = fail "Yices does not support floats."
                     , smtEvalBvArray = Nothing
                     }

  smtSatResult _ = getSatResponse

instance OnlineSolver s (Connection s) where
  startSolverProcess = yicesStartSolver
  shutdownSolverProcess = yicesShutdownSolver

yicesShutdownSolver :: SolverProcess s (Connection s) -> IO ()
yicesShutdownSolver p =
   do hClose (solverStdin p)

      --logLn 2 "Waiting for yices to terminate"
      txt <- readAllLines (solverStderr p)

      ec <- waitForProcess (solverHandle p)
      case ec of
        ExitSuccess -> do
          return ()
          --logLn 2 "Yices terminated."
        ExitFailure exit_code -> do
          fail $ "yices exited with unexpected code " ++ show exit_code ++ "\n"
              ++ LazyText.unpack txt

yicesStartSolver :: B.ExprBuilder s st fs -> IO (SolverProcess s (Connection s))
yicesStartSolver sym = do
  let cfg = getConfiguration sym
  yices_path <- findSolverPath yicesPath cfg
  let args = ["--mode=push-pop"]

  let create_proc
        = (proc yices_path args)
          { std_in  = CreatePipe
          , std_out = CreatePipe
          , std_err = CreatePipe
          , create_group = True
          , cwd = Nothing
          }

  let startProcess = do
        x <- createProcess create_proc
        case x of
          (Just in_h, Just out_h, Just err_h, ph) -> return (in_h,out_h,err_h,ph)
          _ -> fail "Internal error in yicesStartServer: Failed to create handle."

  (in_h,out_h,err_h,ph) <- startProcess

  --void $ forkIO $ logErrorStream err_stream (logLn 2)
  -- Create new connection for sending commands to yices.
  let features = useLinearArithmetic
             .|. useBitvectors
             .|. useSymbolicArrays
             .|. useComplexArithmetic
             .|. useStructs
  conn <- newConnection in_h features B.emptySymbolVarBimap
  setYicesParams conn cfg

  err_reader <- startHandleReader err_h
  out_stream <- Streams.lines =<< Streams.handleToInputStream out_h
  return $! SolverProcess { solverConn   = conn
                          , solverStdin  = in_h
                          , solverStderr = err_reader
                          , solverHandle = ph
                          , solverResponse = out_stream
                          , solverEvalFuns = smtEvalFuns conn out_stream
                          , solverLogFn = logSolverEvent sym
                          , solverName = "Yices"
                          }

------------------------------------------------------------------------
-- Translation code

-- | Send a check command to Yices.
sendCheck :: WriterConn t (Connection s) -> IO ()
sendCheck c = addCommand c (checkCommand c)

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

-- | Print a command to show the model.
sendShowModel :: WriterConn t (Connection s) -> IO ()
sendShowModel c = addCommand c showModelCommand



-- | Get a line of output from Yices, if any.
yicesGetLine :: Streams.InputStream ByteString -> IO (Maybe Text)
yicesGetLine resp =
  do mbBytes <- Streams.read resp
     case mbBytes of
       Nothing -> return Nothing
       Just bytes ->
         case decodeUtf8' bytes of
           Left err -> fail (show err)
           Right a  -> return (Just a)

-- | Get a line of output from Yices.  Throws an exception at EOF.
yicesDoGetLine :: Streams.InputStream ByteString -> IO Text
yicesDoGetLine resp =
  do mb <- yicesGetLine resp
     case mb of
       Nothing -> fail "Missing response from the solver."
       Just b  -> return b


-- | Get the sat result from a previous SAT command.
-- Throws an exception if something goes wrong.
getSatResponse :: Streams.InputStream ByteString -> IO (SatResult ())
getSatResponse resps =
  do res <- Streams.read resps
     case res of
       Nothing -> fail $ unlines [ "Unexpected end of input."
                                 , "*** Expecting: sat result"
                                 ]
       Just txt ->
         case txt of
           "unsat"    -> return Unsat
           "sat"      -> return (Sat ())
           "unknown"  -> return Unknown
           _  -> fail $ unlines
              [ "Unexpected sat result:"
              , "*** Result: " ++ Text.unpack (decodeUtf8 txt)
              , "*** Expecting: unsat/sat/unknown"
              ]

type Eval scope solver ty =
  WriterConn scope (Connection solver) ->
  Streams.InputStream ByteString ->
  Term (Connection solver) ->
  IO ty

-- | Call eval to get a Rational term
yicesEvalReal :: Eval s t Rational
yicesEvalReal conn resp tm =
    do eval conn tm
       l <- yicesDoGetLine resp
       case Root.fromYicesText l of
         Nothing -> do
           fail $ "Could not parse real value returned by yices:\n  " ++ show l
         Just r -> pure $ Root.approximate r

-- | Call eval to get a Boolean term.
yicesEvalBool :: Eval s t Bool
yicesEvalBool conn resp tm = do
  eval conn tm
  l <- yicesDoGetLine resp
  case l of
    "true"  -> return $! True
    "false" -> return $! False
    _ -> do
      fail $ "Could not parse yices value " ++ show l ++ " as a Boolean."

-- | Send eval command and get result back.
yicesEvalBV :: Int -> Eval s t Integer
yicesEvalBV w conn resp tm = do
  eval conn tm
  l <- Text.unpack <$> yicesDoGetLine resp
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
   , solver_adapter_check_sat = \sym logLn rsn p cont ->
       runYicesInOverride sym logLn rsn p (cont . fmap (\x -> (x,Nothing)))
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
writeYicesFile :: B.ExprBuilder t st fs -- ^ Builder for getting current bindings.
               -> FilePath              -- ^ Path to file
               -> B.BoolExpr t          -- ^ Predicate to check
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

-- | Run writer and get a yices result.
runYicesInOverride :: B.ExprBuilder t st fs
                   -> (Int -> String -> IO ())
                   -> String
                   -> B.BoolExpr t
                   -> (SatResult (GroundEvalFn t) -> IO a)
                   -> IO a
runYicesInOverride sym logLn rsn condition resultFn = do
  let cfg = getConfiguration sym
  yices_path <- findSolverPath yicesPath cfg
  logLn 2 "Calling Yices to check sat"
  -- Check Problem features
  logSolverEvent sym
    SolverStartSATQuery
    { satQuerySolverName = "Yices"
    , satQueryReason = rsn
    }
  features <- checkSupportedByYices condition
  let efSolver = features `hasProblemFeature` useExistForall
  let nlSolver = features `hasProblemFeature` useNonlinearArithmetic
  let args | efSolver  = ["--mode=ef"]
           | nlSolver  = ["--logic=QF_NRA"]
           | otherwise = ["--mode=one-shot"]
  withProcessHandles yices_path args Nothing $ \(in_h, out_h, err_h, ph) -> do
    -- Log stderr to output.
    withHandleReader err_h $ \err_reader -> do

      responses <- Streams.lines =<< Streams.handleToInputStream out_h

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

      let yp = SolverProcess { solverConn = c
                             , solverHandle = ph
                             , solverStdin  = in_h
                             , solverResponse = responses
                             , solverStderr = err_reader
                             , solverEvalFuns = smtEvalFuns c responses
                             , solverName = "Yices"
                             , solverLogFn = logSolverEvent sym
                             }
      sat_result <- getSatResult yp
      logSolverEvent sym
        SolverEndSATQuery
        { satQueryResult = sat_result
        , satQueryError  = Nothing
        }
      r <-
         case sat_result of
           Unsat -> resultFn Unsat
           Unknown -> resultFn Unknown
           Sat () -> resultFn . Sat =<< getModel yp

      yicesShutdownSolver yp
      return r
