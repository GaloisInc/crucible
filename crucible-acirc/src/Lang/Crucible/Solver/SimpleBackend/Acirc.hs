{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Lang.Crucible.Solver.SimpleBackend.Acirc
( SimulationResult(..)
, generateCircuit
) where

import           Data.Tuple ( swap )
import           Data.Ratio ( denominator, numerator )
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef, atomicModifyIORef )

import           Control.Exception ( assert )
import           Control.Monad ( void )
import           Control.Monad.ST ( RealWorld )
import           Control.Monad.State ( runState )
import qualified Data.Text as T

-- Crucible imports
import           Data.Parameterized.HashTable (HashTable)
import qualified Data.Parameterized.HashTable as H
import           Data.Parameterized.Nonce ( Nonce )
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Context as Ctx
-- import qualified Data.Parameterized.Context.Safe as Ctx
import           Lang.Crucible.BaseTypes ( BaseType, BaseIntegerType, BaseTypeRepr(..)
                                         , BaseRealType )
import           Lang.Crucible.Utils.MonadST ( liftST )
import           Lang.Crucible.Solver.SimpleBuilder ( Elt(..), SimpleBoundVar(..), VarKind(..)
                                                    , App(..), AppElt(..)
                                                    , NonceApp(..)
                                                    , NonceAppElt(..)
                                                    , eltId, appEltApp, nonceEltId
                                                    , nonceEltApp, symFnName
                                                    , symFnReturnType )
import           Lang.Crucible.Solver.Symbol ( solverSymbolAsText )
import qualified Lang.Crucible.Solver.WeightedSum as WS

-- Acirc imports
import qualified Circuit as B
import qualified Circuit.Builder as B
import qualified Circuit.Format.Acirc as B

{- | Package up the state we need during `eval`. This includes
- the memoization table, `synthesisHash`, we use for keeping track
- of wires and gates. -}
data Synthesis t = Synthesis
  { synthesisState :: IORef B.BuildSt -- ^ BuildSt contains the intermediate representation for Acirc 
  , synthesisHash  :: HashTable RealWorld (Nonce t) NameType -- ^ memo table from ids (`Nonce`) to evaluated
                                                             -- form (`NameType`)
  }

-- | This represents the simplified terms from crucible.
data NameType (tp :: BaseType) where
  IntToReal :: NameType BaseIntegerType -> NameType BaseRealType
  Ref       :: B.Ref   -> NameType BaseIntegerType

-- | Holds the results of a simulation run. This should be passed to
-- generateCircuit.
data SimulationResult a = SimulationResult
  { srInputs :: [a] -- ^ Tracks the expected inputs, in order, so that input wires can be
                    --   added correctly.
  , srTerms  :: [a] -- ^ The terms resulting from the simulation. The circuit is built from these.
  }

-- | memoization function.
--   * Takes the synthesis state
--   * id of the term (nonce)
--   * action to use in the case the term has not been
--     seen before
--   Returns the simplified term for the nonce.
memoEltNonce :: Synthesis t
             -> Nonce t tp
             -> IO (B.Builder (NameType tp))
             -> IO (NameType tp)
memoEltNonce synth n act = do
  let h = synthesisHash synth
  mn <- liftST $ H.lookup h n
  case mn of
    Just m  -> return m -- The id was found in the memo table
    Nothing -> do
      a    <- act
      name <- atomicModifyIORef (synthesisState synth)
                                (swap . runState a)
      liftST $ H.insert h n name
      return name

-- | A version of memoEltNonce that works for non-bound varables like an
-- concrete value. See 'addConstantValue' for more details.
memoElt :: Synthesis t
        -> IO (B.Builder (NameType tp))
        -> IO (NameType tp)
memoElt synth act = do
  a    <- act
  name <- atomicModifyIORef (synthesisState synth)
                            (swap . runState a)
  return name

-- | Top level function for generating the circuit. Takes a SimulationResult
-- containing the inputs to the circuit as well as the crucible terms and
-- writes the circuit description to a file.
-- The basetype of the second argument must be BaseIntegerType
generateCircuit :: FilePath -> SimulationResult (Elt t BaseIntegerType) -> IO ()
generateCircuit fp (SimulationResult { srInputs = is, srTerms = es }) = do
  -- First, we create empty data structures for the conversion
  ref <- newIORef (B.emptyBuildWithV 1 0) -- initialize the build state with the version
  h   <- liftST H.new
  let synth = Synthesis { synthesisState = ref
                        , synthesisHash  = h
                        }
  -- Second, the next step is to find all the inputs to the computation so that
  -- we can create the circuit inputs.
  recordInputs synth is
  -- Third, generate the structure of the circuit from the crucible term
  names <- mapM (eval synth) es
  mapM_ (synthesize synth) names
  -- Finally, we have the final circuit and we can write it to the output file.
  st' <- readIORef (synthesisState synth)
  writeCircuit fp st'
  where
  synthesize :: Synthesis t -> NameType BaseIntegerType -> IO ()
  synthesize synth name = buildStep synth $
    case name of Ref r -> B.output r

buildStep :: Synthesis t -> B.Builder a -> IO a
buildStep synth a = do
  st <- readIORef (synthesisState synth)
  -- now we need to generate the circuit's output
  let (c, st') = runState a st
  writeIORef (synthesisState synth) st'
  return c

-- | Record all the inputs to the function/circuit in the memo table
recordInputs :: Synthesis t -> [Elt t BaseIntegerType] -> IO ()
recordInputs synth vars = do
  mapM_ (addInput synth) vars

-- | Add an individual input to the memo table
addInput :: Synthesis t -> Elt t BaseIntegerType -> IO ()
addInput synth var = do
  case var of
    BoundVarElt bvar -> addBoundVar synth (Some bvar)
    -- TODO: ASKROB: Does this make sense? Don't we need to
    -- note down the input? Well, shouldn't need to because it should never
    -- come up again since it's unused in the circuit.
    IntElt _i _loc   -> addConstantValue synth
    t -> error $ "Unsupported representation: " ++ show t

-- | Add a individual bound variable as a circuit input
addBoundVar :: Synthesis t -> Some (SimpleBoundVar t) -> IO ()
addBoundVar synth (Some bvar) = do
  case bvarType bvar of
    BaseIntegerRepr -> void $ memoEltNonce synth (bvarId bvar) $ return $ do
      Ref <$> B.inputTyped (Just $ B.Vector B.Integer)
    t -> error $ "Unsupported representation: " ++ show t

-- | This is for handling a special case of inputs. Sometimes the parameters are
-- fixed and known, but we still want the function/circuit to take values in
-- those places as "inputs". In this case, we want the circuit to declare wires
-- for them but not connect them to the rest of the circuit. So we have a
-- special case where we put them in the memo table but otherwise throw away
-- their references.
addConstantValue :: Synthesis t -> IO ()
addConstantValue synth = void $ memoElt synth $ return $ do
  Ref <$> B.inputTyped (Just $ B.Vector B.Integer)

-- | Write an intermediate circuit state to a file as a circuit
writeCircuit :: FilePath -> B.BuildSt -> IO ()
writeCircuit fp st = B.writeAcirc fp (B.bs_circ st)

--

-- | Construct the bulk of a circuit from a crucible term.
-- This doesn't handle inputs and outputs.
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
eval synth (IntElt n _)   = buildStep synth $ do
  constantRef <- B.constant n
  return (Ref constantRef)
eval synth (AppElt a) = do
  memoEltNonce synth (eltId a) $ do
    doApp synth a

-- | Process an application term and returns the Acirc action that creates the
-- corresponding circuitry.
doApp :: Synthesis t -> AppElt t tp -> IO (B.Builder (NameType tp))
doApp synth ae = do
  case appEltApp ae of
    -- Internally crucible converts integers to reals. We need to
    -- undo that, as we only support integers.
    RealToInteger n -> do
      n' <- eval synth n
      return $! return (intToReal n') -- TODO: rename `intToReal`
    IntegerToReal n -> do
      n' <- eval synth n
      return $! return (IntToReal n')
    RealMul n m -> do
      -- Like the first case above, we know that for our purposes these are
      -- really computations on integers. So we do the necessary conversions
      -- here.
      IntToReal (Ref n') <- eval synth n
      IntToReal (Ref m') <- eval synth m
      return (IntToReal . Ref <$> B.circMul n' m')
    RealSum ws -> do
      -- This is by far the trickiest case.  Crucible stores sums as weighted
      -- sums. This representation is basically a set of coefficients that are
      -- meant to be multiplied with some sums.
      ws' <- WS.eval (\r1 r2 -> do
                       r1' <- r1
                       r2' <- r2
                       return $ do
                         r1'' <- r1'
                         r2'' <- r2'
                         return $! r1'' ++ r2'')
                     -- coefficient case
                     (\c t -> do
                       IntToReal (Ref t') <- eval synth t
                       assert (denominator c == 1) $ return $ do
                         -- simplify products to simple addition, when we can
                         case numerator c of
                           1  -> return [t']
                           -1 -> (:[]) <$> B.circNeg t'
                           -- Code below is for when we can support constants
                           _ -> do c' <- B.constant (numerator c)
                                   (:[]) <$> B.circMul c' t')
                     -- just a constant
                     -- TODO what's up with this error
                     (\c -> error "We cannot support raw literals"
                       -- Code below is for when we can support constants
                       assert (denominator c == 1) $ do
                         B.constant (numerator c))
                     ws
      return $! do
        ws'' <- ws'
        case ws'' of
          -- Handle the degenerate sum case (eg., +x) by propagating
          -- the reference to x forward instead of the sum.
          [x] -> return $! IntToReal (Ref x)
          _   -> IntToReal . Ref <$> (B.circSumN ws'')
    x -> fail $ "Not supported: " ++ show x

  where
  intToReal :: NameType BaseRealType -> NameType BaseIntegerType
  intToReal (IntToReal m) = m

-- | Process an application term and returns the Acirc action that creates the
-- corresponding circuitry.
doNonceApp :: Synthesis t -> NonceAppElt t tp -> IO (B.Builder (NameType tp))
doNonceApp synth ae =
  case nonceEltApp ae of
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
              return (Ref <$> B.circRShift base by)
            _ -> fail "The improbable happened: Wrong number of arguments to shift right"
        _ -> fail "The improbable happened: shift right should only return Integer type"
      x -> fail $ "Not supported: " ++ show x
    _ -> fail $ "Not supported"
