------------------------------------------------------------------------
-- |
-- Module           : What4.Expr.VarIdentification
-- Description      : Compute the bound and free variables appearing in expressions
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module What4.Expr.VarIdentification
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
  , recordExprVars
  , predicateVarInfo
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Bits
import qualified Data.HashTable.ST.Cuckoo as H
import           Data.List.NonEmpty (NonEmpty(..))
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

import           What4.BaseTypes
import           What4.Expr.AppTheory
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.Builder
import           What4.ProblemFeatures
import qualified What4.SemiRing as SR
import           What4.Utils.MonadST

data BoundQuant = ForallBound | ExistBound

-- | Contains all information about a bound variable appearing in the
-- expression.
data QuantifierInfo t fs tp
   = BVI { -- | The outer term containing the binding (e.g., Ax.f(x))
           boundTopTerm :: !(NonceAppExpr t fs BaseBoolType)
           -- | The type of quantifier that appears
         , boundQuant :: !BoundQuant
           -- | The variable that is bound
           -- Variables may be bound multiple times.
         , boundVar   :: !(ExprBoundVar t tp)
           -- | The term that appears inside the binding.
         , boundInnerTerm :: !(Expr t fs BaseBoolType)
         }

-- This is a map from quantified formulas to the information about the
-- formula.
type QuantifierInfoMap t fs = Map (NonceAppExpr t fs BaseBoolType) (Some (QuantifierInfo t fs))

-- Due to sharing, a variable may be both existentially and universally quantified even
-- though it is technically bound once.
data CollectedVarInfo t fs
   = CollectedVarInfo { _problemFeatures :: !ProblemFeatures
                      , _uninterpConstants :: !(Set (Some (ExprBoundVar t)))
                      , _existQuantifiers  :: !(QuantifierInfoMap t fs)
                      , _forallQuantifiers :: !(QuantifierInfoMap t fs)
                      , _latches  :: !(Set (Some (ExprBoundVar t)))
                        -- | List of errors found during parsing.
                      , _varErrors :: !(Seq Doc)
                      }

-- | Describes types of functionality required by solver based on the problem.
problemFeatures :: Lens' (CollectedVarInfo t fs) ProblemFeatures
problemFeatures = lens _problemFeatures (\s v -> s { _problemFeatures = v })

uninterpConstants :: Lens' (CollectedVarInfo t fs) (Set (Some (ExprBoundVar t)))
uninterpConstants = lens _uninterpConstants (\s v -> s { _uninterpConstants = v })

-- | Expressions appearing in the problem as existentially quantified when
-- the problem is expressed in negation normal form.  This is a map
-- from the existential quantifier element to the info.
existQuantifiers :: Lens' (CollectedVarInfo t fs) (QuantifierInfoMap t fs)
existQuantifiers = lens _existQuantifiers (\s v -> s { _existQuantifiers = v })

-- | Expressions appearing in the problem as existentially quantified when
-- the problem is expressed in negation normal form.  This is a map
-- from the existential quantifier element to the info.
forallQuantifiers :: Lens' (CollectedVarInfo t fs) (QuantifierInfoMap t fs)
forallQuantifiers = lens _forallQuantifiers (\s v -> s { _forallQuantifiers = v })

latches :: Lens' (CollectedVarInfo t fs) (Set (Some (ExprBoundVar t)))
latches = lens _latches (\s v -> s { _latches = v })

varErrors :: Lens' (CollectedVarInfo t fs) (Seq Doc)
varErrors = lens _varErrors (\s v -> s { _varErrors = v })

-- | Return variables needed to define element as a predicate
predicateVarInfo :: Expr t fs BaseBoolType -> CollectedVarInfo t fs
predicateVarInfo e = runST $ collectVarInfo $ recordAssertionVars ExistsOnly Positive e

newtype VarRecorder s t fs a
      = VR { unVR :: ReaderT (H.HashTable s Word64 (Maybe Polarity))
                             (StateT (CollectedVarInfo t fs) (ST s))
                             a
           }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadFail
           , MonadST s
           )

collectVarInfo :: VarRecorder s t fs () -> ST s (CollectedVarInfo t fs)
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

addFeatures :: ProblemFeatures -> VarRecorder s t fs ()
addFeatures f = VR $ problemFeatures %= (.|. f)

-- | Add the featured expected by a variable with the given type.
addFeaturesForVarType :: BaseTypeRepr tp -> VarRecorder s t fs ()
addFeaturesForVarType tp =
  case tp of
    BaseBoolRepr     -> return ()
    BaseBVRepr _     -> addFeatures useBitvectors
    BaseNatRepr      -> addFeatures useIntegerArithmetic
    BaseIntegerRepr  -> addFeatures useIntegerArithmetic
    BaseRealRepr     -> addFeatures useLinearArithmetic
    BaseComplexRepr  -> addFeatures useLinearArithmetic
    BaseStringRepr _ -> addFeatures useStrings
    BaseArrayRepr{}  -> addFeatures useSymbolicArrays
    BaseStructRepr{} -> addFeatures useStructs
    BaseFloatRepr _  -> addFeatures useFloatingPoint


-- | Information about bound variables outside this context.
data Scope
   = ExistsOnly
   | ExistsForall


addExistVar :: Scope -- ^ Quantifier scope
            -> Polarity -- ^ Polarity of variable
            -> NonceAppExpr t fs BaseBoolType -- ^ Top term
            -> BoundQuant                 -- ^ Quantifier appearing in top term.
            -> ExprBoundVar t tp
            -> Expr t fs BaseBoolType
            -> VarRecorder s t fs ()
addExistVar ExistsOnly p e q v x = do
  let info = BVI { boundTopTerm = e
                 , boundQuant = q
                 , boundVar = v
                 , boundInnerTerm = x
                 }
  VR $ existQuantifiers %= Map.insert e (Some info)
  recordAssertionVars ExistsOnly p x
addExistVar ExistsForall _ _ _ _ _ = do
  fail $ "what4 does not allow existental variables to appear inside forall quantifier."

addForallVar :: Polarity -- ^ Polarity of formula
             -> NonceAppExpr t fs BaseBoolType -- ^ Top term
             -> BoundQuant            -- ^ Quantifier appearing in top term.
             -> ExprBoundVar t tp   -- ^ Bound variable
             -> Expr t fs BaseBoolType    -- ^ Expression inside quant
             -> VarRecorder s t fs ()
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
           -> NonceAppExpr t fs BaseBoolType -- ^ Top term
           -> BoundQuant            -- ^ Quantifier appearing in top term.
           -> ExprBoundVar t tp   -- ^ Variable that is bound.
           -> Expr t fs BaseBoolType    -- ^ Predicate over bound variable.
           -> VarRecorder s t fs ()
addBothVar ExistsOnly e q v x = do
  let info = BVI { boundTopTerm = e
                 , boundQuant = q
                 , boundVar = v
                 , boundInnerTerm = x
                 }
  VR $ existQuantifiers  %= Map.insert e (Some info)
  VR $ forallQuantifiers %= Map.insert e (Some info)
  recordExprVars ExistsForall x
addBothVar ExistsForall _ _ _ _ = do
  fail $ "what4 does not allow existental variables to appear inside forall quantifier."

-- | Record variables in a predicate that we are checking satisfiability of.
recordAssertionVars :: Scope
                       -- ^ Scope of assertion
                    -> Polarity
                       -- ^ Polarity of this formula.
                    -> Expr t fs BaseBoolType
                       -- ^ Predicate to assert
                    -> VarRecorder s t fs ()
recordAssertionVars scope p e@(AppExpr ae) = do
  ht <- VR ask
  let idx = indexValue (appExprId ae)
  mp <- liftST $ H.lookup ht idx
  case mp of
    -- We've seen this element in both positive and negative contexts.
    Just Nothing -> return ()
    -- We've already seen the element in the context @oldp@.
    Just (Just oldp) -> do
      when (oldp /= p) $ do
        recurseAssertedAppExprVars scope p e
        liftST $ H.insert ht idx Nothing
    -- We have not seen this element yet.
    Nothing -> do
      recurseAssertedAppExprVars scope p e
      liftST $ H.insert ht idx (Just p)
recordAssertionVars scope p (NonceAppExpr ae) = do
  ht <- VR ask
  let idx = indexValue (nonceExprId ae)
  mp <- liftST $ H.lookup ht idx
  case mp of
    -- We've seen this element in both positive and negative contexts.
    Just Nothing -> return ()
    -- We've already seen the element in the context @oldp@.
    Just (Just oldp) -> do
      when (oldp /= p) $ do
        recurseAssertedNonceAppExprVars scope p ae
        liftST $ H.insert ht idx Nothing
    -- We have not seen this element yet.
    Nothing -> do
      recurseAssertedNonceAppExprVars scope p ae
      liftST $ H.insert ht idx (Just p)
recordAssertionVars scope _ e = do
  recordExprVars scope e

-- | This records asserted variables in an app expr.
recurseAssertedNonceAppExprVars :: Scope
                           -> Polarity
                           -> NonceAppExpr t fs BaseBoolType
                           -> VarRecorder s t fs ()
recurseAssertedNonceAppExprVars scope p ea0 =
  case nonceExprApp ea0 of
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

-- | This records asserted variables in an app expr.
recurseAssertedAppExprVars :: Scope -> Polarity -> Expr t fs BaseBoolType -> VarRecorder s t fs ()
recurseAssertedAppExprVars scope p e = go e
 where
 go BoolExpr{} = return ()

 go (asApp -> Just (NotPred x)) =
        recordAssertionVars scope (negatePolarity p) x

 go (asApp -> Just (ConjPred xs)) =
   let pol (x,Positive) = recordAssertionVars scope p x
       pol (x,Negative) = recordAssertionVars scope (negatePolarity p) x
   in
   case BM.viewBoolMap xs of
     BM.BoolMapUnit -> return ()
     BM.BoolMapDualUnit -> return ()
     BM.BoolMapTerms (t:|ts) -> mapM_ pol (t:ts)

 go (asApp -> Just (BaseIte BaseBoolRepr _ c x y)) =
   do recordExprVars scope c
      recordAssertionVars scope p x
      recordAssertionVars scope p y

 go _ = recordExprVars scope e


memoExprVars :: Nonce t (tp::BaseType) -> VarRecorder s t fs () -> VarRecorder s t fs ()
memoExprVars n recurse = do
  let idx = indexValue n
  ht <- VR ask
  mp <- liftST $ H.lookup ht idx
  case mp of
    Just Nothing -> return ()
    _ -> do
      recurse
      liftST $ H.insert ht idx Nothing

-- | Record the variables in an element.
recordExprVars :: Scope -> Expr t fs tp -> VarRecorder s t fs ()
recordExprVars _ (SemiRingLiteral sr _ _) =
  case sr of
    SR.SemiRingBVRepr _ _ -> addFeatures useBitvectors
    _                     -> addFeatures useLinearArithmetic
recordExprVars _ StringExpr{} = addFeatures useStrings
recordExprVars _ BoolExpr{} = return ()
recordExprVars scope (NonceAppExpr e0) = do
  memoExprVars (nonceExprId e0) $ do
    recurseNonceAppVars scope e0
recordExprVars scope (AppExpr e0) = do
  memoExprVars (appExprId e0) $ do
    recurseExprVars scope e0
recordExprVars _ (BoundVarExpr info) = do
  addFeaturesForVarType (bvarType info)
  case bvarKind info of
    QuantifierVarKind ->
      return ()
    LatchVarKind ->
      VR $ latches %= Set.insert (Some info)
    UninterpVarKind ->
      VR $ uninterpConstants %= Set.insert (Some info)

recordFnVars :: ExprSymFn t fs args ret -> VarRecorder s t fs ()
recordFnVars f = do
  case symFnInfo f of
    UninterpFnInfo{}  -> return ()
    DefinedFnInfo _ d _ -> recordExprVars ExistsForall d
    MatlabSolverFnInfo _ _ d -> recordExprVars ExistsForall d


-- | Recurse through the variables in the element, adding bound variables
-- as both exist and forall vars.
recurseNonceAppVars :: forall s t fs tp. Scope -> NonceAppExpr t fs tp -> VarRecorder s t fs ()
recurseNonceAppVars scope ea0 = do
  let a0 = nonceExprApp ea0
  case a0 of
    Forall v x ->
      addBothVar scope ea0 ForallBound v x
    Exists v x ->
      addBothVar scope ea0 ExistBound  v x
    ArrayFromFn f -> do
      recordFnVars f
    MapOverArrays f _ a -> do
      recordFnVars f
      traverseFC_ (\(ArrayResultWrapper e) -> recordExprVars scope e) a
    ArrayTrueOnEntries f a -> do
      recordFnVars f
      recordExprVars scope a

    FnApp f a -> do
      recordFnVars f
      traverseFC_ (recordExprVars scope) a

addTheoryFeatures :: AppTheory -> VarRecorder s t fs ()
addTheoryFeatures th =
  case th of
    BoolTheory -> return ()
    LinearArithTheory     -> addFeatures useLinearArithmetic
    NonlinearArithTheory  -> addFeatures useNonlinearArithmetic
    ComputableArithTheory -> addFeatures useComputableReals
    BitvectorTheory       -> addFeatures useBitvectors
    ArrayTheory           -> addFeatures useSymbolicArrays
    StructTheory          -> addFeatures useStructs
    StringTheory          -> addFeatures useStrings
    FloatingPointTheory   -> addFeatures useFloatingPoint
    QuantifierTheory -> return ()
    FnTheory         -> return ()

-- | Recurse through the variables in the element, adding bound variables
-- as both exist and forall vars.
recurseExprVars :: forall s t fs tp. Scope -> AppExpr t fs tp -> VarRecorder s t fs ()
recurseExprVars scope ea0 = do
  addTheoryFeatures (appTheory (appExprApp ea0))
  traverseFC_ (recordExprVars scope) (appExprApp ea0)
