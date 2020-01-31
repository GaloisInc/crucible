-----------------------------------------------------------------------
-- |
-- Module           : What4.Solver.BLT
-- Description      : What4 solver interface for BLT
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : bjones@galois.com
-- Stability        : provisional
--
-- This module provides the BLT integer linear programming library
-- as an optional solver in MSS.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
module What4.Solver.BLT
  ( -- * BLT Adapter API
    bltParams
  , bltOptions
  , bltAdapter
    -- * BLT Solver API
  , Handle
  , BLTParams(..)
  , parseBLTParams
  , newHandle
  , withHandle
  , checkSat
  , assume
  , bltDefaultParams
    -- * BLTExpr API
  , BLTVar(..)
  , mkBLTVar
  , BLTExpr(..)
  , isBLTConst
  , isBLTZero
  , isBLTHomog
  , IsBLT
  , addBLTE
  , multBLTE
  , leadingVar
  , leadingCoeff
  , normalizeLEQ
    -- * Low level interaction with BLT package
  , toCExpr
    -- * Exported for testing purposes
  , isCompleteBounds
  , recordLowerBound
  , recordUpperBound
  ) where

import           Control.Exception (assert, Exception, bracket, throwIO)
import qualified Control.Exception as Ex
import           Control.Lens
import           Control.Monad (foldM, forM_, when, liftM2)
import           Control.Monad.ST
import           Data.IORef
import           Data.Int (Int64)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe, isJust)
import qualified Data.Text as T
import           Data.Traversable
import           Data.Typeable
import           System.IO (hPutStrLn, stderr)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.Parameterized.HashTable as PH
import           Data.Parameterized.Nonce

import           What4.BaseTypes
import           What4.Config
import           What4.ProgramLoc
import           What4.Concrete
import           What4.Interface
import           What4.SatResult
import           What4.Expr
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.GroundEval
import           What4.Expr.Builder
import qualified What4.Expr.WeightedSum as WSum
import           What4.Solver.Adapter
import qualified What4.Utils.AbstractDomains as AD
import           What4.Utils.Complex

import           BLT.Binding

-- | BLT's parameter string, parsed by the function 'parseBLTParams' below.
bltParams :: ConfigOption (BaseStringType Unicode)
bltParams = configOption knownRepr "blt_params"

bltOptions :: [ConfigDesc]
bltOptions =
  [ opt         bltParams         (ConcreteString (UnicodeLiteral ""))
    (text "Command-line parameters to send to BLT")
  ]

bltAdapter :: SolverAdapter t
bltAdapter =
   SolverAdapter
   { solver_adapter_name = "blt"
   , solver_adapter_config_options = bltOptions
   , solver_adapter_check_sat = \sym logData ps cont ->
           runBLTInOverride sym logData ps
             (cont . runIdentity . traverseSatResult (\x -> pure (x,Nothing)) pure)
   , solver_adapter_write_smt2 = \_ _ _ -> do
       fail "BLT backend does not support writing SMTLIB2 files."
   }

runBLTInOverride :: IsExprBuilder sym
                 => sym
                 -> LogData
                 -> [BoolExpr t fs] -- ^ propositions to check
                 -> (SatResult (GroundEvalFn t fs) () -> IO a)
                 -> IO a
runBLTInOverride sym logData ps contFn = do
  let cfg = getConfiguration sym
  epar <- parseBLTParams . T.unpack <$> (getOpt =<< getOptionSetting bltParams cfg)
  par  <- either fail return epar
  logSolverEvent sym
    SolverStartSATQuery
    { satQuerySolverName = "BLT"
    , satQueryReason = logReason logData
    }
  withHandle par $ \h -> do
    forM_ ps (assume h)
    result <- checkSat h
    logSolverEvent sym
      SolverEndSATQuery
      { satQueryResult = forgetModelAndCore result
      , satQueryError  = Nothing
      }
    contFn result

------------------------------------------------------------------------
-- BLTExpr data type and arithmetic
------------------------------------------------------------------------

-- | Represents a BLT variable
newtype BLTVar = BLTVar { varID :: Int }
  deriving (Eq, Ord)

instance Show BLTVar where
  show (BLTVar i) = "x" ++ show i

mkBLTVar :: Int -> BLTVar
mkBLTVar = BLTVar

-- | Represent rational-linear combinations of variables and constants.
data BLTExpr = BLTExpr
    { -- | associates rational coefficients to variables
      blte_coeff :: Map BLTVar Rational
      -- | constant term
    , blte_const :: Rational
    }
  deriving (Eq, Ord, Show)

-- | A BLTExpr is constant iff its symbolic term is zero
isBLTConst :: BLTExpr -> Bool
isBLTConst (BLTExpr s _) = all (==0) (Map.elems s)

-- | A BLTExpr is zero if it is constant and that constant is zero
isBLTZero :: BLTExpr -> Bool
isBLTZero b = isBLTConst b && blte_const b == 0

-- | A BLTExpr is homogeneous iff it is non-zero and non-constant
isBLTHomog :: BLTExpr -> Bool
isBLTHomog b = (not . isBLTConst $ b) && (not . isBLTZero $ b)

-- | Typeclass for overloading functions of BLTExpr arguments
class IsBLT a where
  mkBLT :: a -> BLTExpr

instance IsBLT BLTExpr where
  mkBLT = id

instance IsBLT Rational where
  mkBLT = BLTExpr Map.empty

instance IsBLT Integer where
  mkBLT x = BLTExpr Map.empty (toRational x)

instance IsBLT Int where
  mkBLT x = BLTExpr Map.empty (toRational x)

instance IsBLT BLTVar where
  mkBLT v = BLTExpr (Map.singleton v 1) 0

-- | Add two BLT expressions (overloaded)
addBLTE :: (IsBLT a, IsBLT b) => a -> b -> BLTExpr
addBLTE (mkBLT -> BLTExpr s1 c1) (mkBLT -> BLTExpr s2 c2) = BLTExpr s' c'
  where
  s' = Map.unionWith (+) s1 s2
  c' = c1 + c2

-- | Multiply two BLT expressions (overloaded)
multBLTE :: (IsBLT a, IsBLT b) => a -> b -> BLTExpr
multBLTE (mkBLT -> e) (mkBLT -> f)
    | isBLTConst e = multByConst (blte_const e) f
    | isBLTConst f = multByConst (blte_const f) e
    | otherwise = error "Non-linear expressions are not supported by BLT"
  where
  multByConst r m = BLTExpr (Map.map (*r) (blte_coeff m)) (r * blte_const m)

-- | Multiply by -1
negBLTE :: IsBLT a => a -> BLTExpr
negBLTE (mkBLT -> e) = multBLTE (-1 :: Rational) e

-- | Given a homogeneous BLTExpr, return a tuple with the leading coefficient
-- and the BLTExpr with this coefficient factored out. Such an expression is
-- called "monic".
monicBLTE :: BLTExpr -> (Rational, BLTExpr)
monicBLTE b = assert (isBLTHomog b) (l, multBLTE (1/l) b)
  where l = leadingCoeff b

-- | Return the variable with lowest ID among those with non-zero coefficient.
-- If there is no such variable, return Nothing.
leadingVar :: BLTExpr -> Maybe BLTVar
leadingVar (blte_coeff -> m) =
  let ks = Map.keys . Map.filter (/= 0) $ m
  in if null ks
        then Nothing
        else Just (minimum ks)

-- | If the expression has a leading variable, return its coefficient.
-- Otherwise return 1.
leadingCoeff :: BLTExpr -> Rational
leadingCoeff b@(blte_coeff -> m) =
  let mCoeff = leadingVar b >>= (`Map.lookup` m)
  in fromMaybe 1 mCoeff

-- | Convert BLTExpr arithmetic into BLT arithmetic
toCExpr :: HContext -> BLTExpr -> IO CExpr
toCExpr ctx (BLTExpr s c) = do
  c' <- bltConst ctx c
  ts <- forM (Map.toList s) $ \(v, a) ->
    bltVar ctx (show . varID $ v) >>= bltSmul ctx a
  foldM (bltAdd ctx) c' ts

------------------------------------------------------------------------
-- BLT Parameters
------------------------------------------------------------------------

data BLTParams = BLTParams
  { _blt_mode :: RatMode
  , _blt_verb :: Bool
  , _blt_sound :: Bool
  } deriving (Eq, Show)

-- | Lenses for BLTParams
blt_mode :: Lens' BLTParams RatMode
blt_mode = lens _blt_mode (\c a -> c { _blt_mode = a })

blt_verb :: Lens' BLTParams Bool
blt_verb = lens _blt_verb (\c a -> c { _blt_verb = a })

blt_sound :: Lens' BLTParams Bool
blt_sound = lens _blt_sound (\c a -> c { _blt_sound = a })

-- | Default parameters to use when none are user specified
bltDefaultParams :: BLTParams
bltDefaultParams = BLTParams
  { _blt_mode = RatID
  , _blt_verb = False
  , _blt_sound = False
  }

-- | A parser for BLT parameters. Valid parameters options are:
--
-- ""            pass coefficients through untouched to BLT,
--                 verbosity disabled
--
-- "-p <INT>"    set denominator precision to <int>
-- "-s <INT64>"  scale by <int64> and round all coeff's
-- "-v"          enable verbose output
-- "-y"          enable sound mode (requires Yices)
--
-- where <INT> should parse as a Haskell 'Int' and <INT64> a Haskell
-- 'Data.Int.Int64'. Options may be combined, except that -s and -p are
-- incompatible.
--

-- RWD FIXME, update parser to enable the BLT "sound" mode
parseBLTParams :: String -> Either String BLTParams
parseBLTParams []  = Right bltDefaultParams
parseBLTParams str = goParse (words str) (Right bltDefaultParams)
  where
  goParse :: [String] -> Either String BLTParams -> Either String BLTParams
  goParse [] par = par
  goParse (m:rest) par =
    case () of
      _ | m == "-v" -> goParse rest (set blt_verb True <$> par)
        | m == "-y" -> goParse rest (set blt_sound True <$> par)
        | m == "-s" || m == "-p" -> goParseMode (m:rest) par
        | otherwise -> parseFail

  goParseMode :: [String] -> Either String BLTParams -> Either String BLTParams
  goParseMode [] par = par
  goParseMode [_] _  = parseFail
  goParseMode (m:i:rest) par =
    case () of
      _ | m == "-s" ->
          goParse rest (set blt_mode (RatFixed (read i :: Int64)) <$> par)
        | m == "-p" ->
          goParse rest (set blt_mode (RatApprox (read i :: Int)) <$> par)
        | otherwise -> parseFail

  parseFail = Left ("parseBLTParams: failed to parse " ++ str)


------------------------------------------------------------------------
-- Problem handle (context)
-----------------------------------------------------------------------

-- | Partial (lower, upper) bounds on a symboic expression along with a
-- saved scaling factor.
type Bounds = ( Rational        -- scaling factor
              , Maybe Rational  -- lower bound
              , Maybe Rational  -- upper bound
              )

newtype NameType (tp :: BaseType) = N { asName :: BLTExpr }

data VarIndex tp where
  IntegerVarIndex :: Int -> VarIndex BaseIntegerType

-- | Handle type for a BLT solver session
data Handle t = Handle
  { -- | pointer to the C library problem context
    getCtx     :: HContext
    -- | associate elements for variables to the index.
  , varIndices :: !(PH.HashTable RealWorld (Nonce t) VarIndex)
    -- | associate each observed Expr with a BLTExpr that represents the
    -- variable on the BLT side
  , exprCache  :: !(IdxCache t NameType)
    -- | associate lower/upper bounds with each top level expression
  , boundMap   :: !(IORef (Map BLTExpr Bounds))
    -- | flag set if a trivial conflict in assumptions is found
  , flagUNSAT  :: !(IORef Bool)
    -- | flag set if verbose output is desired during problem construction
  , params     :: !BLTParams
  }

-- | Check verbosity flag
isVerb :: Handle t -> Bool
isVerb = view blt_verb . params

-- | Check if the handle's bounds map is valid and complete: it should be
-- keyed on monic BLTExpr's and have a definite lower and upper bound set.
isCompleteBounds :: Handle t -> IO Bool
isCompleteBounds h = do
    mp <- Map.toList <$> readIORef (boundMap h)
    return $ all checkBnd mp
  where
    checkBnd (b, (_, ml, mu)) = leadingCoeff b == 1
                             && isJust ml
                             && isJust mu

-- | Create a new handle & BLT problem context
newHandle :: BLTParams -> IO (Handle t)
newHandle par = do
  getCtx     <- bltInit (par^.blt_mode) (par^.blt_sound)
  varIndices <- stToIO PH.new
  exprCache  <- newIdxCache
  boundMap   <- newIORef Map.empty
  flagUNSAT  <- newIORef False
  let params = par
  return Handle {..}

-- | Free foreign memory associated with a handle
closeHandle :: Handle t -> IO ()
closeHandle h = bltFree (getCtx h)

-- | Run an action with a new handle, close it when done
withHandle :: BLTParams -> (Handle t -> IO a) -> IO a
withHandle par f = do
  r <- bracket (newHandle par) closeHandle (Ex.try . f)
  case r of
    Left (BLTE msg) -> fail msg
    Right v -> return v

-- | Indicate that the problem is trivially UNSAT
setUNSAT :: Handle t -> IO ()
setUNSAT h = do
  when (isVerb h) $ hPutStrLn stderr "Warning: problem is trivially UNSAT"
  writeIORef (flagUNSAT h) True


------------------------------------------------------------------------
-- Evaluate Symbolic Expressions from 'crucible'
------------------------------------------------------------------------

-- | Parse given Expr Bool as a conjunction of inequalities and record them
assume :: Handle t -> BoolExpr t fs -> IO ()
assume _ (BoundVarExpr v) =
  failAt' (bvarLoc v) "Boolean variables are not supported by BLT."
#if !MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
assume _ (SemiRingLiteral sr _ _) = case sr of {}
#endif
assume _ (NonceAppExpr e) =
  fail . show $
    text "Unsupported term created at" <+> pretty (plSourceLoc l) <>
    text ":" <$$> indent 2 (pretty (NonceAppExpr e))
  where
  l = nonceExprLoc e
assume h (BoolExpr b l)
  | b = return ()
  | otherwise =
      do when (isVerb h) $ warnAt l "problem assumes False"
         setUNSAT h
assume h b@(AppExpr ba) =
  let a = appExprApp ba in
    case a of
      ConjPred xs ->
        case BM.viewBoolMap xs of
          BM.BoolMapUnit -> return ()
          BM.BoolMapDualUnit ->
               do when (isVerb h) $ warnAt l "problem assumes False"
                  setUNSAT h
          BM.BoolMapTerms (t:|ts) -> mapM_ f (t:ts)
            where f (x,BM.Positive) = assume h x
                  f (_,BM.Negative) = unsupported

      SemiRingLe OrderedSemiRingIntegerRepr x y  -> do
        x' <- evalInteger h x
        y' <- evalInteger h y
        appLEq x' y'
      SemiRingLe OrderedSemiRingRealRepr x y  -> do
        x' <- evalReal h x
        y' <- evalReal h y
        appLEq x' y'
      _ -> unsupported
  where
  unsupported = fail $ show $
        text "Unsupported term created at" <+> pretty (plSourceLoc l) <>
        text ":" <$$> indent 2 (pretty b)
  l = appExprLoc ba
  appLEq lhs rhs =
    let (lhs', rhs') = normalizeLEQ lhs rhs in
    case (isBLTConst lhs', isBLTConst rhs') of
      -- const <= const
      (True, True)
        | blte_const lhs' <= blte_const rhs' -> do
            when (isVerb h) $
              warnAt l "problem contains trivial (constant) inequality"
        | otherwise -> do
            when (isVerb h) $ warnAt l
               ("problem assumes contradictory constraints: "
                ++ show (blte_const lhs') ++ " <= "
                ++ show (blte_const rhs'))
            setUNSAT h
      -- const <= symbolic
      (True, False) -> do
        when (isVerb h) $ putStrLn "BLT.hs@assume: recorded lower bound"
        let c = blte_const lhs'
        recordLowerBound h c rhs'
      -- symbolic <= const
      (False, True) -> do
        when (isVerb h) $ putStrLn "BLT.hs@assume: recorded upper bound"
        let c = blte_const rhs'
        recordUpperBound h c lhs'
      (False, False) ->
        failAt l "assertion failed: both sides of normalized <= are symbolic"

-- | Normalize an inequality by adding or subtracting terms from one side to
-- the other so that one side is constant and the other is either also
-- /constant/ or is /homogeneous with positive leading term/. This is what we
-- call "normal form" for the purposes of this module.
normalizeLEQ :: BLTExpr -> BLTExpr -> (BLTExpr, BLTExpr)
normalizeLEQ lhs rhs =
  if isBLTConst lhs && isBLTConst rhs
     then (lhs, rhs)
     else
       let -- lhs - rhs
           ltmp = addBLTE lhs (negBLTE rhs)
           -- subtract const term on lhs from both sides
           rhs' = mkBLT $ (-1 :: Rational) * blte_const ltmp
           lhs' = addBLTE ltmp rhs'
           -- at this point, lhs' is homogeneous and rhs' is constant
           lc = leadingCoeff lhs'
       in if lc > 0
             then (lhs', rhs')
             else (negBLTE rhs', negBLTE lhs')  -- reverse sides

-- | Record a lower bound for the given BLT expression. Pre-condition: the 3rd
-- argument must be a non-zero, homogeneous BLTExpr with positive leading
-- coeff.
recordLowerBound :: Handle t -> Rational -> BLTExpr -> IO ()
recordLowerBound h r e = assert (isBLTHomog e && leadingCoeff e > 0) $ do
  mp <- readIORef $ boundMap h
  let (s, mon) = monicBLTE e
      replace = case Map.lookup mon mp of
                  Nothing -> (s, Just (r/s), Nothing)
                  Just (_, Nothing, mu) -> (s, Just (r/s), mu)
                  Just (_, Just l, mu) -> if l <= (r/s)
                                             then (s, Just (r/s), mu)
                                             else (s, Just l,     mu)
  writeIORef (boundMap h) $ Map.insert mon replace mp

-- | Record an upper bound for the given BLT expression. Pre-condition: the 3rd
-- argument must be a non-zero, homogeneous BLTExpr with positive leading
-- coeff.
recordUpperBound :: Handle t -> Rational -> BLTExpr -> IO ()
recordUpperBound h r e = assert (isBLTHomog e && leadingCoeff e > 0) $ do
  mp <- readIORef $ boundMap h
  let (s, mon) = monicBLTE e
      replace = case Map.lookup mon mp of
                  Nothing -> (s, Nothing, Just (r/s))
                  Just (_, ml, Nothing) -> (s, ml, Just (r/s))
                  Just (_, ml, Just u) -> if (r/s) <= u
                                             then (s, ml, Just (r/s))
                                             else (s, ml, Just u)
  writeIORef (boundMap h) $ Map.insert mon replace mp


-- | Cached version of evalReal'. We wrap and unwrap the NameType to be
-- compatible with IdxCache functions in Core.
evalReal :: Handle t -> RealExpr t fs -> IO BLTExpr
evalReal h e = asName <$> idxCacheEval (exprCache h) e (N <$> evalReal' h e)

-- | Parse a RealVal expression, flattening it to a (new) BLTExpr.

evalReal' :: Handle t -> RealExpr t fs -> IO BLTExpr
-- Integer variables are supported, but not Real
evalReal' _ (BoundVarExpr v) =
  failAt (bvarLoc v) "Real variables are not supported by BLT."
evalReal' h (SemiRingLiteral SemiRingRealRepr r _) = do
  when (isVerb h) $ putStrLn ("BLT@evalReal: rational const " ++ show r)
  return (mkBLT r)
evalReal' _ (NonceAppExpr ea) =
  failAt (nonceExprLoc ea) "symbolic functions"
evalReal' h epr@(AppExpr epa) = do
  let l = exprLoc epr
  case appExprApp epa of

    RealPart c -> do
      (r :+ _) <- evalCplx h c
      return r
    ImagPart c -> do
      (_ :+ i) <- evalCplx h c
      return i

    -- support only linear expressions
    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SemiRingRealRepr ->
          fromMaybe (mkBLT (1::Rational)) <$>
            WSum.prodEvalM (\a b -> pure (multBLTE a b)) (evalReal h) pd

    SemiRingSum s ->
      case WSum.sumRepr s of
        SemiRingRealRepr ->
          WSum.eval (liftM2 addBLTE) smul con s
         where smul sm e = multBLTE (mkBLT sm) <$> evalReal h e
               con = return . mkBLT

    IntegerToReal x ->
      evalInteger h x

    -- support only linear expressions
    RealDiv x y -> do
      x' <- evalReal h x
      y' <- evalReal h y
      if isBLTConst y'
         then return $ multBLTE (1 / blte_const y') x'
         else failAt l "Reciprocal symbolic expressions"

    _ ->
      fail $ "BLT encountered a real expression that it does not support.\n"
          ++ "The term was created at " ++ show (plSourceLoc l) ++ ":\n"
          ++ "  " ++ show (ppExprTop epr)


-- | Cached version of evalInteger'. We wrap and unwrap the NameType to be
-- compatible with IdxCache functions in Core.
evalInteger :: Handle t -> IntegerExpr t fs -> IO BLTExpr
evalInteger h e = asName <$> idxCacheEval (exprCache h) e (N <$> evalInteger' h e)

-- | Parse an IntegerType element, flattening it to a (new) BLTExpr.
evalInteger' :: Handle t -> IntegerExpr t fs -> IO BLTExpr
-- Match integer variable.
evalInteger' h (BoundVarExpr info) =
  case bvarKind info of
    QuantifierVarKind ->
      failAt' (bvarLoc info) "Bound variables are not supported by BLT."
    LatchVarKind ->
      failAt' (bvarLoc info) "Latches are not supported by BLT."
    UninterpVarKind -> do
      let i = fromEnum . indexValue $ bvarId info :: Int
      let v = mkBLTVar i
      stToIO $ PH.insert (varIndices h) (bvarId info) (IntegerVarIndex i)
      let e = mkBLT v
      case AD.rangeLowBound <$> (bvarAbstractValue info) of
        Just (AD.Inclusive lo) -> recordLowerBound h (fromInteger lo) e
        _ -> return ()
      case AD.rangeHiBound <$> (bvarAbstractValue info) of
        Just (AD.Inclusive hi) -> recordUpperBound h (fromInteger hi) e
        _ -> return ()
      return e

-- Match integer constant
evalInteger' h (SemiRingLiteral SemiRingIntegerRepr i _) = do
  when (isVerb h) $ putStrLn ("BLT@evalInteger: integer const " ++ show i)
  return $ mkBLT (toRational i)
-- Match expression
evalInteger' _ (NonceAppExpr ea) =
  failAt (nonceExprLoc ea) "symbolic functions"
evalInteger' h (AppExpr epa) = do
  let l = appExprLoc epa
  case appExprApp epa of
    -- support only linear expressions
    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SemiRingIntegerRepr ->
          fromMaybe (mkBLT (1::Integer)) <$>
            WSum.prodEvalM (\a b -> pure (multBLTE a b)) (evalInteger h) pd

    SemiRingSum s ->
      case WSum.sumRepr s of
        SemiRingIntegerRepr -> WSum.eval (liftM2 addBLTE) smul con s
          where smul sm e = multBLTE (mkBLT sm) <$> evalInteger h e
                con = return . mkBLT

    RealToInteger x -> evalReal h x

    _ -> failAt l "The given integer expressions"

-- | Evaluate complex symbolic expressions to their ModelExpr type.
evalCplx :: Handle t -> CplxExpr t fs -> IO (Complex BLTExpr)
evalCplx _ (BoundVarExpr i) = failAt (bvarLoc i) "Complex variables"
#if !MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
evalCplx _ (SemiRingLiteral sr _ _) = case sr of {}
#endif
evalCplx _ (NonceAppExpr ea) =
  failAt (nonceExprLoc ea) "symbolic functions"
evalCplx h (AppExpr ea) =
  case appExprApp ea of
    Cplx (r :+ i) -> do
      r' <- evalReal h r
      i' <- evalReal h i
      return (r' :+ i')
#if !MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
    SemiRingSum s -> case WSum.sumRepr s of {}
    SemiRingProd pd -> case WSum.prodRepr pd of {}
#endif
    BaseIte{} -> failAt (appExprLoc ea) "complex if/then/else"
    SelectArray{} -> failAt (appExprLoc ea) "symbolic arrays"
    StructField{} -> failAt (appExprLoc ea) "symbolic arrays"

------------------------------------------------------------------------
-- Call Solver
------------------------------------------------------------------------

-- | check here for lwr, upr bounds
checkSat :: forall t fs. Handle t -> IO (SatResult (GroundEvalFn t fs) ())
checkSat h = do
    let ctx = getCtx h
    bnds <- readIORef (boundMap h)
    when (Map.null bnds) $ do
      fail "BLT checksat given empty bounds."
    doAssumptions ctx bnds
    isTrivial <- readIORef (flagUNSAT h)
    if isTrivial
       then return (Unsat ())
       else doCheck ctx
  where
  -- assert inequalities to BLT
  doAssumptions ctx bnds =
    forM_ (Map.toList bnds) $ \(bexpr, bs) ->
      case bs of
        -- scale factor and bounds pair
        (s, Just l, Just u) -> do
          when (isVerb h) $ do
            putStrLn $ "BLT.hs@checkSat: bounds " ++ show l ++ " <= ... <= " ++ show u
            putStrLn $ "BLT.hs@checkSat: scalar " ++ show s
          if l <= u
             then do
               e <- toCExpr ctx (multBLTE s bexpr)
               _  <- bltAssume ctx (s*l) e (s*u)
               return ()
             else
               setUNSAT h
        -- TODO add source location of unbounded expression
        (_, Nothing, Just _) ->
          fail "FATAL -- BLT found a top-level expression with no lower bound"
        (_, Just _, Nothing) ->
          fail "FATAL -- BLT found a top-level expression with no upper bound"
        (_, Nothing, Nothing) ->
          fail "FATAL -- BLT found a top-level expression with no bounds at all"

  -- Run the solver!
  doCheck ctx = do
    rc <- bltCheck ctx
    case () of
      _ | bltUNSAT == rc -> return (Unsat ())
        | bltSAT   == rc -> do
          groundCache <- newIdxCache
          let f :: Expr t fs tp -> IO (GroundValue tp)
              f (BoundVarExpr info) = do
                -- See what this was bound to.
                me <- stToIO $ PH.lookup (varIndices h) (bvarId info)
                case me of
                  Just (IntegerVarIndex i) ->
                    maybe 0 toInteger <$> bltModel ctx (show i)
                  Nothing ->
                   return $ defaultValueForType $ bvarType info

              f e = unGVW <$> idxCacheEval groundCache e (GVW <$> evalGroundExpr f e)
          return $ Sat $ GroundEvalFn f
        | otherwise -> fail ("** BLT: checkSat failed, return code = " ++ show rc)

------------------------------------------------------------------------
-- Failures and Warnings
------------------------------------------------------------------------

failAt :: ProgramLoc -> String -> IO a
failAt l msg = failAt' l (msg ++ " is/are not supported by BLT.")

failAt' :: ProgramLoc -> String -> IO a
failAt' l msg = throwIO $ BLTE $ msg ++ "\nTerm created at " ++ show sl ++ "."
  where sl = plSourceLoc l

warnAt :: ProgramLoc -> String -> IO ()
warnAt l msg = hPutStrLn stderr
     $ "BLT: WARNING: " ++ msg
    ++ "\nTerm created at " ++ show sl ++ "."
  where sl = plSourceLoc l

------------------------------------------------------------------------
-- Exceptions
------------------------------------------------------------------------

newtype BLTException = BLTE String
  deriving (Typeable)

instance Exception BLTException

instance Show BLTException where
  show (BLTE msg) = "BLT Error: " ++ msg
