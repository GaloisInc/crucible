------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.SimpleBackend.VarIdentification
-- Description      : Compute the bound and free variables appearing in Crucible expressions
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lang.Crucible.Solver.SimpleBackend.VarIdentification
  ( -- * CollectedVarInfo
    CollectedVarInfo
  , uninterpConstants
  , latches
  , QuantifierInfo(..)
  , BoundQuant(..)
  , QuantifierInfoMap
  , problemFeatures
  , existQuantifiers
  , forallQuantifiers
  , varErrors
    -- * CollectedVarInfo generation
  , Scope(..)
  , Polarity(..)
  , VarRecorder
  , collectVarInfo
  , recordEltVars
  , predicateVarInfo
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Bits
import qualified Data.HashTable.ST.Cuckoo as H
import           Data.Map.Strict as Map
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word
import           Text.PrettyPrint.ANSI.Leijen

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.Solver.Interface (ArrayResultWrapper(..))
import           Lang.Crucible.Solver.SimpleBackend.AppTheory
import           Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
import           Lang.Crucible.Solver.SimpleBuilder
import           Lang.Crucible.Utils.MonadST

data BoundQuant = ForallBound | ExistBound

-- | Contains all information about a bound variable appearing in the
-- expression.
data QuantifierInfo t tp
   = BVI { -- | The outer term containing the binding (e.g., Ax.f(x))
           boundTopTerm :: !(NonceAppElt t BaseBoolType)
           -- | The type of quantifier that appears
         , boundQuant :: !BoundQuant
           -- | The variable that is bound
           -- Variables may be bound multiple times.
         , boundVar   :: !(SimpleBoundVar t tp)
           -- | The term that appears inside the binding.
         , boundInnerTerm :: !(Elt t BaseBoolType)
         }

-- This is a map from quantified formulas to the information about the
-- formula.
type QuantifierInfoMap t = Map (NonceAppElt t BaseBoolType) (Some (QuantifierInfo t))

-- Due to sharing, a variable may be both existentially and universally quantified even
-- though it is technically bound once.
data CollectedVarInfo t
   = CollectedVarInfo { _problemFeatures :: !ProblemFeatures
                      , _uninterpConstants :: !(Set (Some (SimpleBoundVar t)))
                      , _existQuantifiers  :: !(QuantifierInfoMap t)
                      , _forallQuantifiers :: !(QuantifierInfoMap t)
                      , _latches  :: !(Set (Some (SimpleBoundVar t)))
                        -- | List of errors found during parsing.
                      , _varErrors :: !(Seq Doc)
                      }

-- | Describes types of functionality required by solver based on the problem.
problemFeatures :: Simple Lens (CollectedVarInfo t) ProblemFeatures
problemFeatures = lens _problemFeatures (\s v -> s { _problemFeatures = v })

uninterpConstants :: Simple Lens (CollectedVarInfo t) (Set (Some (SimpleBoundVar t)))
uninterpConstants = lens _uninterpConstants (\s v -> s { _uninterpConstants = v })

-- | Expressions appearing in the problem as existentially quantified when
-- the problem is expressed in negation normal form.  This is a map
-- from the existential quantifier element to the info.
existQuantifiers :: Simple Lens (CollectedVarInfo t) (QuantifierInfoMap t)
existQuantifiers = lens _existQuantifiers (\s v -> s { _existQuantifiers = v })

-- | Expressions appearing in the problem as existentially quantified when
-- the problem is expressed in negation normal form.  This is a map
-- from the existential quantifier element to the info.
forallQuantifiers :: Simple Lens (CollectedVarInfo t) (QuantifierInfoMap t)
forallQuantifiers = lens _forallQuantifiers (\s v -> s { _forallQuantifiers = v })

latches :: Simple Lens (CollectedVarInfo t) (Set (Some (SimpleBoundVar t)))
latches = lens _latches (\s v -> s { _latches = v })

varErrors :: Simple Lens (CollectedVarInfo t) (Seq Doc)
varErrors = lens _varErrors (\s v -> s { _varErrors = v })

-- | Return variables needed to define element as a predicate
predicateVarInfo :: Elt t BaseBoolType -> CollectedVarInfo t
predicateVarInfo e = runST $ collectVarInfo $ recordAssertionVars ExistsOnly Positive e

newtype VarRecorder s t a
      = VR { unVR :: ReaderT (H.HashTable s Word64 (Maybe Polarity))
                             (StateT (CollectedVarInfo t) (ST s))
                             a
           }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadST s
           )

collectVarInfo :: VarRecorder s t () -> ST s (CollectedVarInfo t)
collectVarInfo m = do
  h <- H.new
  let s = CollectedVarInfo { _problemFeatures = noFeatures
                    , _uninterpConstants = Set.empty
                    , _existQuantifiers  = Map.empty
                    , _forallQuantifiers = Map.empty
                    , _latches   = Set.empty
                    , _varErrors = Seq.empty
                    }
  execStateT (runReaderT (unVR m) h) s

addFeatures :: ProblemFeatures -> VarRecorder s t ()
addFeatures f = VR $ problemFeatures %= (.|. f)

-- | Add the featured expected by a variable with the given type.
addFeaturesForVarType :: BaseTypeRepr tp -> VarRecorder s t ()
addFeaturesForVarType tp =
  case tp of
    BaseBoolRepr     -> return ()
    BaseBVRepr _     -> addFeatures useBitvectors
    BaseNatRepr      -> addFeatures useIntegerArithmetic
    BaseIntegerRepr  -> addFeatures useIntegerArithmetic
    BaseRealRepr     -> addFeatures useLinearArithmetic
    BaseComplexRepr  -> addFeatures useComplexArithmetic
    BaseStringRepr   -> addFeatures useStrings
    BaseArrayRepr{}  -> addFeatures useSymbolicArrays
    BaseStructRepr{} -> addFeatures useStructs


-- | Information about bound variables outside this context.
data Scope
   = ExistsOnly
   | ExistsForall


addExistVar :: Scope -- ^ Quantifier scope
            -> Polarity -- ^ Polarity of variable
            -> NonceAppElt t BaseBoolType -- ^ Top term
            -> BoundQuant                 -- ^ Quantifier appearing in top term.
            -> SimpleBoundVar t tp
            -> Elt t BaseBoolType
            -> VarRecorder s t ()
addExistVar ExistsOnly p e q v x = do
  let info = BVI { boundTopTerm = e
                 , boundQuant = q
                 , boundVar = v
                 , boundInnerTerm = x
                 }
  VR $ existQuantifiers %= Map.insert e (Some info)
  recordAssertionVars ExistsOnly p x
addExistVar ExistsForall _ _ _ _ _ = do
  fail $ "mss does not allow existental variables to appear inside forall quantifier."

-- \ Describes whether the polarity of a subformula.
--
-- A formula is positive if it appears under an even number of negations, and
-- positive otherwise.
data Polarity = Positive | Negative
  deriving (Eq)

negatePolarity :: Polarity -> Polarity
negatePolarity Positive = Negative
negatePolarity Negative = Positive

addForallVar :: Polarity -- ^ Polarity of formula
             -> NonceAppElt t BaseBoolType -- ^ Top term
             -> BoundQuant            -- ^ Quantifier appearing in top term.
             -> SimpleBoundVar t tp   -- ^ Bound variable
             -> Elt t BaseBoolType    -- ^ Expression inside quant
             -> VarRecorder s t ()
addForallVar p e q v x = do
  let info = BVI { boundTopTerm = e
                 , boundQuant = q
                 , boundVar = v
                 , boundInnerTerm = x
                 }
  VR $ forallQuantifiers %= Map.insert e (Some info)
  recordAssertionVars ExistsForall p x

-- | Record a Forall/Exists quantifier is found in a context where
-- it will appear both positively and negatively.
addBothVar :: Scope                 -- ^ Scope where binding is seen.
           -> NonceAppElt t BaseBoolType -- ^ Top term
           -> BoundQuant            -- ^ Quantifier appearing in top term.
           -> SimpleBoundVar t tp   -- ^ Variable that is bound.
           -> Elt t BaseBoolType    -- ^ Predicate over bound variable.
           -> VarRecorder s t ()
addBothVar ExistsOnly e q v x = do
  let info = BVI { boundTopTerm = e
                 , boundQuant = q
                 , boundVar = v
                 , boundInnerTerm = x
                 }
  VR $ existQuantifiers  %= Map.insert e (Some info)
  VR $ forallQuantifiers %= Map.insert e (Some info)
  recordEltVars ExistsForall x
addBothVar ExistsForall _ _ _ _ = do
  fail $ "mss does not allow existental variables to appear inside forall quantifier."

-- | Record variables in a predicate that we are checking satisfiability of.
recordAssertionVars :: Scope
                       -- ^ Scope of assertion
                    -> Polarity
                       -- ^ Polarity of this formula.
                    -> Elt t BaseBoolType
                       -- ^ Predicate to assert
                    -> VarRecorder s t ()
recordAssertionVars scope p (AppElt ae) = do
  ht <- VR ask
  let idx = indexValue (appEltId ae)
  mp <- liftST $ H.lookup ht idx
  case mp of
    -- We've seen this element in both positive and negative contexts.
    Just Nothing -> return ()
    -- We've already seen the element in the context @oldp@.
    Just (Just oldp) -> do
      when (oldp /= p) $ do
        recurseAssertedAppEltVars scope p ae
        liftST $ H.insert ht idx Nothing
    -- We have not seen this element yet.
    Nothing -> do
      recurseAssertedAppEltVars scope p ae
      liftST $ H.insert ht idx (Just p)
recordAssertionVars scope p (NonceAppElt ae) = do
  ht <- VR ask
  let idx = indexValue (nonceEltId ae)
  mp <- liftST $ H.lookup ht idx
  case mp of
    -- We've seen this element in both positive and negative contexts.
    Just Nothing -> return ()
    -- We've already seen the element in the context @oldp@.
    Just (Just oldp) -> do
      when (oldp /= p) $ do
        recurseAssertedNonceAppEltVars scope p ae
        liftST $ H.insert ht idx Nothing
    -- We have not seen this element yet.
    Nothing -> do
      recurseAssertedNonceAppEltVars scope p ae
      liftST $ H.insert ht idx (Just p)
recordAssertionVars scope _ e = do
  recordEltVars scope e

-- | This records asserted variables in an app elt.
recurseAssertedNonceAppEltVars :: Scope
                           -> Polarity
                           -> NonceAppElt t BaseBoolType
                           -> VarRecorder s t ()
recurseAssertedNonceAppEltVars scope p ea0 =
  case nonceEltApp ea0 of
    Forall v x -> do
      case p of
        Positive -> do
          addFeatures useExistForall
          addForallVar      p ea0 ForallBound v x
        Negative ->
          addExistVar scope p ea0 ForallBound v x
    Exists v x -> do
      case p of
        Positive ->
          addExistVar scope p ea0 ExistBound v x
        Negative -> do
          addFeatures useExistForall
          addForallVar      p ea0 ExistBound v x
    _ -> recurseNonceAppVars scope ea0

-- | This records asserted variables in an app elt.
recurseAssertedAppEltVars :: Scope -> Polarity -> AppElt t BaseBoolType -> VarRecorder s t ()
recurseAssertedAppEltVars scope p ea0 =
  case appEltApp ea0 of
    NotBool x -> recordAssertionVars scope (negatePolarity p) x
    AndBool x y -> mapM_ (recordAssertionVars scope p) [x, y]
    IteBool c x y -> do
      recordEltVars scope c
      recordAssertionVars scope p x
      recordAssertionVars scope p y
    _ -> recurseEltVars scope ea0


memoEltVars :: Nonce t (tp::BaseType) -> VarRecorder s t () -> VarRecorder s t ()
memoEltVars n recurse = do
  let idx = indexValue n
  ht <- VR ask
  mp <- liftST $ H.lookup ht idx
  case mp of
    Just Nothing -> return ()
    _ -> do
      recurse
      liftST $ H.insert ht idx Nothing

-- | Record the variables in an element.
recordEltVars :: Scope -> Elt t tp -> VarRecorder s t ()
recordEltVars _ SemiRingLiteral{} = addFeatures useLinearArithmetic
recordEltVars _ BVElt{}  = addFeatures useBitvectors
recordEltVars _ StringElt{} = addFeatures useStrings
recordEltVars scope (NonceAppElt e0) = do
  memoEltVars (nonceEltId e0) $ do
    recurseNonceAppVars scope e0
recordEltVars scope (AppElt e0) = do
  memoEltVars (appEltId e0) $ do
    recurseEltVars scope e0
recordEltVars _ (BoundVarElt info) = do
  addFeaturesForVarType (bvarType info)
  case bvarKind info of
    QuantifierVarKind ->
      return ()
    LatchVarKind ->
      VR $ latches %= Set.insert (Some info)
    UninterpVarKind ->
      VR $ uninterpConstants %= Set.insert (Some info)

recordFnVars :: SimpleSymFn t args ret -> VarRecorder s t ()
recordFnVars f = do
  case symFnInfo f of
    UninterpFnInfo{}  -> return ()
    DefinedFnInfo _ d _ -> recordEltVars ExistsForall d
    MatlabSolverFnInfo _ _ d -> recordEltVars ExistsForall d


-- | Recurse through the variables in the element, adding bound variables
-- as both exist and forall vars.
recurseNonceAppVars :: forall s t tp. Scope -> NonceAppElt t tp -> VarRecorder s t ()
recurseNonceAppVars scope ea0 = do
  let a0 = nonceEltApp ea0
  case a0 of
    Forall v x ->
      addBothVar scope ea0 ForallBound v x
    Exists v x ->
      addBothVar scope ea0 ExistBound  v x
    ArrayFromFn f -> do
      recordFnVars f
    MapOverArrays f _ a -> do
      recordFnVars f
      traverseFC_ (\(ArrayResultWrapper e) -> recordEltVars scope e) a
    ArrayTrueOnEntries f a -> do
      recordFnVars f
      recordEltVars scope a

    FnApp f a -> do
      recordFnVars f
      traverseFC_ (recordEltVars scope) a

addTheoryFeatures :: AppTheory -> VarRecorder s t ()
addTheoryFeatures th =
  case th of
    BoolTheory -> return ()
    LinearArithTheory     -> addFeatures useLinearArithmetic
    NonlinearArithTheory  -> addFeatures useNonlinearArithmetic
    ComputableArithTheory -> addFeatures useComputableReals
    BitvectorTheory       -> addFeatures useBitvectors
    ArrayTheory           -> addFeatures useSymbolicArrays
    StructTheory          -> addFeatures useStructs
    QuantifierTheory -> return ()
    FnTheory         -> return ()

-- | Recurse through the variables in the element, adding bound variables
-- as both exist and forall vars.
recurseEltVars :: forall s t tp. Scope -> AppElt t tp -> VarRecorder s t ()
recurseEltVars scope ea0 = do
  addTheoryFeatures (appTheory (appEltApp ea0))
  traverseFC_ (recordEltVars scope) (appEltApp ea0)
