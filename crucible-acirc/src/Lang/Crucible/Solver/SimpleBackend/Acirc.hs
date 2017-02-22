{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module Lang.Crucible.Solver.SimpleBackend.Acirc
( generateCircuit
) where

import           Data.Tuple ( swap )
import           Data.Ratio ( denominator, numerator )
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef, atomicModifyIORef )
import           Data.Set ( Set )
import qualified Data.Set as S
import qualified Data.Foldable as Fold

import           Control.Lens ( (^.) )
import           Control.Exception ( assert )
import           Control.Monad ( void )
import           Control.Monad.ST ( RealWorld, runST )
import           Control.Monad.State ( runState, execState )

-- Crucible imports
import           Data.Parameterized.HashTable (HashTable)
import qualified Data.Parameterized.HashTable as H
import           Data.Parameterized.Nonce ( Nonce )
import           Data.Parameterized.Some ( Some(..) )
import           Lang.Crucible.BaseTypes ( BaseType, BaseIntegerType, BaseTypeRepr(..)
                                         , BaseRealType )
import           Lang.Crucible.Utils.MonadST ( liftST )
import           Lang.Crucible.Solver.SimpleBuilder ( Elt(..), SimpleBoundVar(..), VarKind(..)
                                                    , App(..), AppElt(..)
                                                    , eltId, appEltApp )
import           Lang.Crucible.Solver.SimpleBackend.VarIdentification ( CollectedVarInfo, Scope(..)
                                                                      , collectVarInfo, recordEltVars
                                                                      , uninterpConstants)
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
  GroundInt :: Integer -> NameType BaseIntegerType
  Ref       :: B.Ref   -> NameType BaseIntegerType

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

-- | Top level function for generating the circuit. Takes the crucible term and
-- writes the circuit description to a file.
-- The basetype of the second argument must be BaseIntegerType
generateCircuit :: FilePath -> [Elt t BaseIntegerType] -> IO ()
generateCircuit fp es = do
  -- First, we create empty data structures for the conversion
  ref <- newIORef B.emptyBuild
  h   <- liftST H.new
  let synth = Synthesis { synthesisState = ref
                        , synthesisHash  = h
                        }
  -- Second, the next step is to find all the inputs to the computation so that
  -- we can create the circuit inputs.
  let vars = S.unions (map ((^.uninterpConstants) . eltVarInfo) es)
  recordUninterpConstants synth vars
  -- Third, generate the structure of the circuit from the crucible term
  names <- mapM (eval synth) es
  mapM_ (synthesize synth) names
  -- Finally, we have the final circuit and we can write it to the output file.
  st' <- readIORef (synthesisState synth)
  writeCircuit fp st'
  where
  synthesize :: Synthesis t -> NameType BaseIntegerType -> IO ()
  synthesize synth name = do
    st <- readIORef (synthesisState synth)
    -- now we need to generate the circuit's output
    let st' = flip execState st $
          case name of
            GroundInt n -> do
              {- this int is our constant output from the circuit -}
              constantRef <- B.constant n
              B.output constantRef
              {- this is the output wire of our circuit -}
            Ref r -> B.output r
    writeIORef (synthesisState synth) st'

-- Elt and CollectedVarInfo are Crucible types
-- CollectedVarInfo is a wrapper type for an existantial type

-- | Gather up the variables that correspond to inputs
eltVarInfo :: Elt t tp -> CollectedVarInfo t
eltVarInfo e = runST $ collectVarInfo $ recordEltVars ExistsOnly e

-- Some is also a wrapper type

-- | Given a set of bound variables, generates inputs for them in the circuit
recordUninterpConstants :: Synthesis t -> Set (Some (SimpleBoundVar t)) -> IO ()
recordUninterpConstants synth vars = do
  mapM_ (addBoundVar synth) (Fold.toList vars)

-- | Add a individual bound variable as a circuit input
addBoundVar :: Synthesis t -> Some (SimpleBoundVar t) -> IO ()
addBoundVar synth (Some bvar) = do
  case bvarType bvar of
    BaseIntegerRepr -> void $ memoEltNonce synth (bvarId bvar) $ return $ do
      Ref <$> B.input
    t -> error $ "Unsupported representation: " ++ show t

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
eval _ NonceAppElt{}  = fail "Nonce application not supported"
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
eval _ (IntElt n _)   = return (GroundInt n)
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
                           _  -> error "We can only support multiplication of 1 and -1 constants")
                           -- TODO: Code below is for when we can support constants
                           -- _ -> do c' <- B.constant (numerator c)
                           --         B.circMul c' t')
                     -- just a constant
                     (\c -> error "We cannot support raw literals")
                       -- TODO: Code below is for when we can support constants
                       -- assert (denominator c == 1) $ return $ do
                       --   B.constant (numerator c))
                     ws
      return $! IntToReal . Ref <$> (B.circSumN =<< ws')
    _ -> fail "Not supported"

  where
  intToReal :: NameType BaseRealType -> NameType BaseIntegerType
  intToReal (IntToReal m) = m

