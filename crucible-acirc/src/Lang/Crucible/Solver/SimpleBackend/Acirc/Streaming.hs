{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Lang.Crucible.Solver.SimpleBackend.Acirc.Streaming
( SimulationResult(..)
, Option(..)
, generateCircuit
) where

import           Data.List ( intercalate )
import           Data.Maybe
import qualified Data.Map.Strict as M
import           Data.Word  ( Word64 )
import           Data.Ratio ( denominator, numerator )
import           Data.IORef ( IORef, newIORef, readIORef, atomicModifyIORef )

import qualified System.IO as Sys
import qualified Text.Printf as Sys
import           Control.Exception ( assert )
import           Control.Monad ( void )
import           Control.Monad.ST ( RealWorld )
import qualified Data.Text as T

-- Crucible imports
import           Data.Parameterized.HashTable (HashTable)
import qualified Data.Parameterized.HashTable as H
import           Data.Parameterized.Nonce ( NonceGenerator, freshNonce, Nonce, indexValue )
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as Ctx
-- import qualified Data.Parameterized.Context.Safe as Ctx
import           Lang.Crucible.BaseTypes ( BaseType, BaseIntegerType, BaseTypeRepr(..)
                                         , BaseRealType )
import           Lang.Crucible.Utils.MonadST ( liftST )
import           Lang.Crucible.Solver.SimpleBuilder ( Elt(..), SimpleBoundVar(..), VarKind(..)
                                                    , App(..), AppElt(..)
                                                    , NonceApp(..)
                                                    , NonceAppElt(..)
                                                    , eltId, eltMaybeId, appEltApp, nonceEltId
                                                    , nonceEltApp, symFnName
                                                    , symFnReturnType )
import           Lang.Crucible.Solver.Symbol ( solverSymbolAsText )
import qualified Lang.Crucible.Solver.WeightedSum as WS

{- | Package up the state we need during `eval`. This includes
- the memoization table, `synthesisHash`, we use for keeping track
- of wires and gates. -}
data Synthesis t = Synthesis
  { synthesisHash      :: HashTable RealWorld (Nonce t) NameType -- ^ memo table from ids (`Nonce`) to evaluated
                                                             -- form (`NameType`)
  , synthesisConstants :: IORef (M.Map Integer (Nonce t BaseIntegerType)) -- maps constants to their wire id
  , synthesisOut       :: Sys.Handle
  , synthesisGen       :: NonceGenerator IO t
  , synthesisOptions   :: [Option]
  }

-- | This represents the simplified terms from crucible.
data NameType (tp :: BaseType) where
  IntToReal :: NameType BaseIntegerType -> NameType BaseRealType
  Ref       :: Word64   -> NameType BaseIntegerType

-- | Holds the results of a simulation run. This should be passed to
-- generateCircuit.
data SimulationResult a = SimulationResult
  { srInputs :: [a] -- ^ Tracks the expected inputs, in order, so that input wires can be
                    --   added correctly.
  , srTerms  :: [a] -- ^ The terms resulting from the simulation. The circuit is built from these.
  }

data Option = FlattenProducts
  deriving (Read, Show, Eq, Ord)
-- | memoization function.
--   * Takes the synthesis state
--   * id of the term (nonce)
--   * action to use in the case the term has not been
--     seen before
--   Returns the simplified term for the nonce.
memoEltNonce :: Synthesis t
             -> Nonce t tp
             -> IO (NameType tp)
             -> IO (NameType tp)
memoEltNonce synth n act = do
  let h = synthesisHash synth
  mn <- liftST $ H.lookup h n
  case mn of
    Just m  -> return m -- The id was found in the memo table
    Nothing -> do
      name <- act
      liftST $ H.insert h n name
      return name

memoConstNonce :: Synthesis t
               -> Integer
               -> (Nonce t BaseIntegerType -> IO (NameType BaseIntegerType))
               -> IO (NameType BaseIntegerType)
memoConstNonce synth val act = do
  m <- readIORef (synthesisConstants synth)
  case M.lookup val m of
    Just wireId -> return (Ref (indexValue wireId))
    Nothing     -> do
      n <- freshNonce (synthesisGen synth)
      atomicModifyIORef (synthesisConstants synth) $ \m' ->
        (M.insert val n m', ())
      memoEltNonce synth n (act n)

-- | A version of memoEltNonce that works for non-bound varables like an
-- concrete value. See 'addConstantValue' for more details.
memoElt :: Synthesis t
        -> IO (NameType tp)
        -> IO (NameType tp)
memoElt _synth act = do
  name <- act
  return name

generateCircuit :: NonceGenerator IO t -> FilePath -> [Option] -> SimulationResult (Elt t BaseIntegerType) -> IO ()
generateCircuit gen fp opts (SimulationResult { srInputs = is, srTerms = es }) =
  Sys.withFile fp Sys.WriteMode $ \h -> do
    -- First, we create empty data structures for the conversion
    table     <- liftST H.new
    constants <- newIORef M.empty
    let synth = Synthesis { synthesisOut       = h
                          , synthesisHash      = table
                          , synthesisGen       = gen
                          , synthesisConstants = constants
                          , synthesisOptions   = opts
                          }
    writeHeader synth
    recordInputs synth (filter isBoundVar is)
    names <- mapM (eval synth) es
    writeCircuit synth es
    writeOutputs synth names
  where
  isBoundVar BoundVarElt{} = True
  isBoundVar _             = False
  writeOutputs :: Synthesis t -> [NameType BaseIntegerType] -> IO ()
  writeOutputs synth names = writeOutputLine synth wireIds
    where
    wireIds = catMaybes (map wireId names)
  wireId :: NameType BaseIntegerType -> Maybe Word64
  wireId (Ref r) = Just r
  
writeHeader :: Synthesis t -> IO ()
writeHeader synth = Sys.hPutStrLn (synthesisOut synth) "v1.0"

recordInputs :: Synthesis t -> [Elt t BaseIntegerType] -> IO ()
recordInputs synth vars = do
  mapM_ (addInput synth) (zip vars [0..])

addInput :: Synthesis t -> (Elt t BaseIntegerType, Word64) -> IO ()
addInput synth (var, inputId) = do
  case var of
    BoundVarElt bvar  -> addBoundVar synth (Some bvar) inputId
    -- We used to add dummy parameters to the circuit for constants,
    -- but this is no longer necessary.
    IntElt _i _loc    -> {- addConstantInput synth inputId -} return ()
    t -> error $ "addInput: Unsupported representation: " ++ show t

addBoundVar :: Synthesis t -> Some (SimpleBoundVar t) -> Word64 -> IO ()
addBoundVar synth (Some bvar) inputId = do
  case bvarType bvar of
    BaseIntegerRepr -> void $ memoEltNonce synth (bvarId bvar) $ do
      writeInput synth (indexValue (bvarId bvar)) inputId
    t -> error $ "addBoundVar: Unsupported representation: " ++ show t

writeInput :: Synthesis t -> Word64 -> Word64 -> IO (NameType BaseIntegerType)
writeInput synth out inpId = do
  Sys.hPrintf (synthesisOut synth) "%d input %d @ ciphertext\n" out inpId
  return (Ref out)

-- | This is for handling a special case of inputs. Sometimes the parameters are
-- fixed and known, but we still want the function/circuit to take values in
-- those places as "inputs". In this case, we want the circuit to declare wires
-- for them but not connect them to the rest of the circuit. So we have a
-- special case where we put them in the memo table but otherwise throw away
-- their references.
addConstantInput :: Synthesis t -> Word64 -> IO ()
addConstantInput synth inpId = void $ memoElt synth $ do
  out <- freshNonce (synthesisGen synth)
  Sys.hPrintf (synthesisOut synth) "%d input %d @ ciphertext\n" (indexValue out) inpId
  return (Ref (indexValue out))

writeCircuit :: Synthesis t -> [Elt t tp] -> IO ()
writeCircuit synth es = mapM_ (eval synth) es

eval :: Synthesis t -> Elt t tp -> IO (NameType tp)
eval _ NatElt{}       = fail "Naturals not supported"
eval _ RatElt{}       = fail "Rationals not supported"
eval _ BVElt{}        = fail "BitVector not supported"
eval synth (NonceAppElt app)  = do
  memoEltNonce synth (nonceEltId app) $ do
    doNonceApp synth app
eval synth (BoundVarElt bvar) = do
  -- Bound variables should already be handled before
  -- calling eval. See `recordUninterpConstants`.
  memoEltNonce synth (bvarId bvar) $ do
    case bvarKind bvar of
      QuantifierVarKind ->
        error "Bound variable is not defined."
      LatchVarKind ->
        error "Latches are not supported in arithmetic circuits."
      UninterpVarKind ->
        error "Uninterpreted variable that was not defined."
eval synth (IntElt n _)   = Ref <$> writeConstant synth n
eval synth (AppElt a)     = do
  memoEltNonce synth (eltId a) $ do
    -- TODO: expose this through the front-end
    case any (==FlattenProducts) (synthesisOptions synth) of
      False -> doApp synth a
      True  -> do
        r <- doAppFlatten synth a
        case r of
          Left  nt   -> return nt
          Right elts -> case appEltApp a of
            RealMul{}         -> do
              ns <- traverse (\(Some x) -> doNameType synth x) elts
              IntToReal . Ref <$> writeMulN synth (indexValue (eltId a)) ns
            _ -> error "eval: improbable happened: doAppFlatten should have handle this case"
        where
        -- TODO: this probably needs to do a lot more. See the
        -- same function inside `evalForProd` for more.
        doNameType :: Synthesis t -> NameType tp -> IO Word64
        doNameType _synth (Ref n) = return $! n
        doNameType _synth (IntToReal r) = doNameType _synth r

evalForProd :: Synthesis t -> Elt t tp
            -> IO (Either (NameType tp) [Some NameType])
evalForProd _     NatElt{}           = fail "Naturals not supported"
evalForProd _     RatElt{}           = fail "Rationals not supported"
evalForProd _     BVElt{}            = fail "BitVector not supported"
evalForProd synth (NonceAppElt app)  = do
  nt <- memoEltNonce synth (nonceEltId app) $ do
    doNonceApp synth app
  return $! Left nt
evalForProd synth (BoundVarElt bvar) = do
  nt <- memoEltNonce synth (bvarId bvar) $ do
    case bvarKind bvar of
      QuantifierVarKind ->
        error "Bound variable is not defined."
      LatchVarKind ->
        error "Latches are not supported in arithmetic circuits."
      UninterpVarKind ->
        error "Uninterpreted variable that was not defined."
  return $! Left nt
evalForProd synth (IntElt n _)       = do
  -- TODO: should this really write the constant??
  n' <- writeConstant synth n
  return $! Left (Ref n')
evalForProd synth (AppElt a) = do
  r <- doAppFlatten synth a
  case r of
    Left  nt   -> return $! Left nt
    Right elts -> case appEltApp a of
      RealMul{} -> return $! Right elts
      _         -> do
        ns <- traverse (\(Some x) -> doNameType synth x) elts
        void $ writeMulN synth (indexValue (eltId a)) ns
        return $! r
  where
  -- TODO: this seems suspiciously simple, if you're debugging
  -- missing output in your circuit. Be suspicious of this function.
  doNameType :: Synthesis t -> NameType tp -> IO Word64
  doNameType _synth (Ref n) = return $! n
  doNameType _synth (IntToReal r) = doNameType _synth r

-- | Process an application term and returns the Acirc action that creates the
-- corresponding circuitry.
doAppFlatten :: Synthesis t -> AppElt t tp
             -> IO (Either (NameType tp) [Some NameType])
doAppFlatten synth ae = do
  case appEltApp ae of
    -- Internally crucible converts integers to reals. We need to
    -- undo that, as we only support integers.
    RealToInteger n -> do
      n' <- eval synth n
      return $! Left (intToReal n') -- TODO: rename `intToReal`
    IntegerToReal n -> do
      n' <- eval synth n
      return $! Left (IntToReal n')
    RealMul n m -> do
      -- Unlike the normal `doApp`, we need to return the intermediate
      -- terms and NOT write the gate yet. That needs to happen at a higher
      -- level.
      let extract (Left x)   = [Some x]
          extract (Right xs) = xs
      ns <- evalForProd synth n
      ms <- evalForProd synth m
      return $! Right $ extract ns ++ extract ms
    RealSum ws -> do
      -- This is by far the trickiest case.  Crucible stores sums as weighted
      -- sums. This representation is basically a set of coefficients that are
      -- meant to be multiplied with some sums.
      ws' <- WS.eval (\r1 r2 -> do
                     r1' <- r1
                     r2' <- r2
                     return $! r1' ++ r2')
                     -- coefficient case
                     (\c t -> do
                       IntToReal (Ref t') <- eval synth t
                       assert (denominator c == 1) $ do
                         -- simplify products to simple addition, when we can
                         case numerator c of
                           1  -> return [t']
                           -1 -> do
                             out <- freshNonce (synthesisGen synth)
                             Ref out' <- memoEltNonce synth out $ return (Ref (indexValue out))
                             (:[]) <$> writeNeg synth out' t'
                           -- Code below is for when we can support constants
                           _ -> do
--                              ts <- evalForProd synth t
--                              c' <- writeConstant synth (numerator c)
--                              let Just tId = eltMaybeId t
--                              (:[]) <$> writeMulN synth (indexValue tId) (c':ts)
                             c'    <- writeConstant synth (numerator c)
                             let Just tId = eltMaybeId t
                             (:[]) <$> writeMul synth (indexValue tId) c' t'
                         )
                     -- just a constant
                     -- TODO what's up with this error
                     (\_c -> error "We cannot support raw literals"
                       -- Code below is for when we can support constants
                       -- assert (denominator c == 1) $ do
                       --   B.constant (numerator c)
                     )
                     ws
      case ws' of
        -- Handle the degenerate sum case (eg., +x) by propagating
        -- the reference to x forward instead of the sum.
        [x] -> return $! Left $! IntToReal (Ref x)
        _   -> do
          let aeId = indexValue (eltId ae)
          s <- writeSumN synth aeId ws'
          return $! Left $! IntToReal (Ref s)
    x -> fail $ "Not supported: " ++ show x

  where
  intToReal :: NameType BaseRealType -> NameType BaseIntegerType
  intToReal (IntToReal m) = m

-- | Process an application term and returns the Acirc action that creates the
-- corresponding circuitry.
doApp :: Synthesis t -> AppElt t tp -> IO (NameType tp)
doApp synth ae = do
  case appEltApp ae of
    -- Internally crucible converts integers to reals. We need to
    -- undo that, as we only support integers.
    RealToInteger n -> do
      n' <- eval synth n
      return $! intToReal n' -- TODO: rename `intToReal`
    IntegerToReal n -> do
      n' <- eval synth n
      return $! IntToReal n'
    RealMul n m -> do
      -- Like the first case above, we know that for our purposes these are
      -- really computations on integers. So we do the necessary conversions
      -- here.
      IntToReal (Ref n') <- eval synth n
      IntToReal (Ref m') <- eval synth m
      let aeId = indexValue (eltId ae)
      IntToReal . Ref <$> writeMul synth aeId n' m'
    RealSum ws -> do
      -- This is by far the trickiest case.  Crucible stores sums as weighted
      -- sums. This representation is basically a set of coefficients that are
      -- meant to be multiplied with some sums.
      ws' <- WS.eval (\r1 r2 -> do
                     r1' <- r1
                     r2' <- r2
                     return $! r1' ++ r2')
                     -- coefficient case
                     (\c t -> do
                       IntToReal (Ref t') <- eval synth t
                       assert (denominator c == 1) $ do
                         -- simplify products to simple addition, when we can
                         case numerator c of
                           1  -> return [t']
                           -1 -> do
                             out <- freshNonce (synthesisGen synth)
                             Ref out' <- memoEltNonce synth out $ return (Ref (indexValue out))
                             (:[]) <$> writeNeg synth out' t'
                           -- Code below is for when we can support constants
                           _ -> do
                             c'    <- writeConstant synth (numerator c)
                             let Just tId = eltMaybeId t
                             (:[]) <$> writeMul synth (indexValue tId) c' t'
                         )
                     -- just a constant
                     -- TODO what's up with this error
                     (\_c -> error "We cannot support raw literals"
                       -- Code below is for when we can support constants
                       -- assert (denominator c == 1) $ do
                       --   B.constant (numerator c)
                     )
                     ws
      case ws' of
        -- Handle the degenerate sum case (eg., +x) by propagating
        -- the reference to x forward instead of the sum.
        [x] -> return (IntToReal (Ref x))
        _   -> do
          let aeId = indexValue (eltId ae)
          IntToReal . Ref <$> writeSumN synth aeId ws'
    x -> fail $ "Not supported: " ++ show x

  where
  intToReal :: NameType BaseRealType -> NameType BaseIntegerType
  intToReal (IntToReal m) = m

-- | Process an application term and returns the Acirc action that creates the
-- corresponding circuitry.
doNonceApp :: Synthesis t -> NonceAppElt t tp -> IO (NameType tp)
doNonceApp synth ae =
  case nonceEltApp ae of
    -- Right-shift uninterp function
    FnApp fn args -> case T.unpack (solverSymbolAsText (symFnName fn)) of
      "julia_shiftRight!" -> case symFnReturnType fn of
        BaseIntegerRepr -> do
          let sz = Ctx.size args
          case (Ctx.intIndex 0 sz, Ctx.intIndex 1 sz) of
            (Just (Some zero), Just (Some one)) -> do
              let baseArg = args Ctx.! zero
                  byArg   = args Ctx.! one
              Ref base <- eval synth baseArg
              Ref by   <- eval synth byArg
              Ref <$> writeRShift synth (indexValue (nonceEltId ae)) base by
            _ -> fail "The improbable happened: Wrong number of arguments to shift right"
        _ -> fail "The improbable happened: shift right should only return Integer type"
      -- dot-product uninterp function
      "julia_dotProd!" -> case symFnReturnType fn of
        BaseIntegerRepr -> do
          xs <- Ctx.traverseFC (eval synth) args
          let args' = Ctx.toListFC (\(Ref x) -> x) xs
          Ref <$> writeDotProd synth (indexValue (nonceEltId ae)) args'
        _ -> fail "The improbable happened: shift right should only return Integer type"
      x -> fail $ "Not supported: " ++ show x
    _ -> fail $ "Not supported"

-- Circuit generation functions

writeMul :: Synthesis t -> Word64 -> Word64 -> Word64 -> IO Word64
writeMul synth out in1 in2 = do
  Sys.hPrintf (synthesisOut synth) "%d * %d %d\n" out in1 in2
  return out

writeMulN :: Synthesis t -> Word64 -> [Word64] -> IO Word64
writeMulN synth out args = do
  let str = intercalate " " (show out : "*" : map show args)
  Sys.hPutStrLn (synthesisOut synth) str
  return out

writeNeg :: Synthesis t -> Word64 -> Word64 -> IO Word64
writeNeg synth out ref = do
  Sys.hPrintf (synthesisOut synth) "%d - %d\n" out ref
  return out

writeSumN :: Synthesis t -> Word64 -> [Word64] -> IO Word64
writeSumN synth out args = do
  let str = intercalate " " (show out : "+" : map show args)
  Sys.hPutStrLn (synthesisOut synth) str
  return out

writeRShift :: Synthesis t -> Word64 -> Word64 -> Word64 -> IO Word64
writeRShift synth out base by = do
  Sys.hPrintf (synthesisOut synth)
              "%d >> %d %d\n"
              out base by
  return out

writeConstant :: Synthesis t -> Integer -> IO Word64
writeConstant synth val = do
  Ref out <- memoConstNonce synth val $ \wireId -> do
    Sys.hPrintf (synthesisOut synth)
                "%d const @ Integer %d\n"
                (indexValue wireId) val
    return (Ref (indexValue wireId))
  return out

writeDotProd :: Synthesis t -> Word64 -> [Word64] -> IO Word64
writeDotProd synth out args = do
  let str = intercalate " " (show out:"o":map show args)
  Sys.hPutStrLn (synthesisOut synth) str
  return out

writeOutputLine :: Synthesis t -> [Word64] -> IO ()
writeOutputLine synth refs = do
  let str = intercalate " " (":outputs" : map show refs)
  Sys.hPutStrLn (synthesisOut synth) str
