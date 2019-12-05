{- |
Module      : What4.Protocol.SMTWriter
Copyright   : (c) Galois, Inc 2014-16.
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This defines common definitions used in writing SMTLIB (2.0 and later), and
yices outputs from 'Expr' values.

The writer is designed to support solvers with arithmetic, propositional
logic, bitvector, tuples (aka. structs), and arrays.

It maps complex Expr values to either structs or arrays depending
on what the solver supports (structs are preferred if both are supported).

It maps multi-dimensional arrays to either arrays with structs as indices
if structs are supported or nested arrays if they are not.

The solver should detect when something is not supported and give an
error rather than sending invalid output to a file.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module What4.Protocol.SMTWriter
  ( -- * Type classes
    SupportTermOps(..)
  , ArrayConstantFn
  , SMTWriter(..)
  , SMTReadWriter (..)
  , SMTEvalBVArrayFn
  , SMTEvalBVArrayWrapper(..)
    -- * Terms
  , Term
  , app
  , app_list
  , builder_list
    -- * SMTWriter
  , WriterConn( supportFunctionDefs
              , supportFunctionArguments
              , supportQuantifiers
              , supportedFeatures
              , connHandle
              , smtWriterName
              )
  , connState
  , newWriterConn
  , resetEntryStack
  , entryStackHeight
  , pushEntryStack
  , popEntryStack
  , Command
  , addCommand
  , addCommandNoAck
  , addCommands
  , mkFreeVar
  , bindVarAsFree
  , TypeMap(..)
  , freshBoundVarName
  , assumeFormula
  , assumeFormulaWithName
  , assumeFormulaWithFreshName
  , DefineStyle(..)
  , AcknowledgementAction(..)
  , nullAcknowledgementAction
    -- * SMTWriter operations
  , assume
  , mkSMTTerm
  , mkFormula
  , mkAtomicFormula
  , SMTEvalFunctions(..)
  , smtExprGroundEvalFn
    -- * Reexports
  , What4.Interface.RoundingMode(..)
  ) where

import           Control.Exception
import           Control.Lens hiding ((.>))
import           Control.Monad.Extra
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Maybe
import           Data.ByteString (ByteString)
import           Data.Bits (shiftL)
import           Data.IORef
import           Data.Kind
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes (ShowF(..))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.HashTable as PH
import           Data.Parameterized.Nonce (Nonce)
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Data.Semigroup( (<>) )
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.Builder.Int as Builder (decimal)
import qualified Data.Text.Lazy as Lazy
import           Data.Word
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
import           System.IO.Streams (OutputStream)
import qualified System.IO.Streams as Streams

import           What4.BaseTypes
import           What4.Interface (ArrayResultWrapper(..), IndexLit(..), RoundingMode(..), StringLiteral(..), stringInfo)
import           What4.ProblemFeatures
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import qualified What4.Expr.StringSeq as SSeq
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.UnaryBV as UnaryBV
import           What4.ProgramLoc
import           What4.SatResult
import qualified What4.SemiRing as SR
import           What4.Symbol
import           What4.Utils.AbstractDomains
import qualified What4.Utils.BVDomain as BVD
import           What4.Utils.Complex
import qualified What4.Utils.Hashable as Hash
import           What4.Utils.StringLiteral

------------------------------------------------------------------------
-- Term construction typeclasses

-- | 'TypeMap' defines how a given 'BaseType' maps to an SMTLIB type.
--
-- It is necessary as there may be several ways in which a base type can
-- be encoded.
data TypeMap (tp::BaseType) where
  BoolTypeMap    :: TypeMap BaseBoolType
  NatTypeMap     :: TypeMap BaseNatType
  IntegerTypeMap :: TypeMap BaseIntegerType
  RealTypeMap    :: TypeMap BaseRealType
  BVTypeMap      :: (1 <= w) => !(NatRepr w) -> TypeMap (BaseBVType w)
  FloatTypeMap   :: !(FloatPrecisionRepr fpp) -> TypeMap (BaseFloatType fpp)
  Char8TypeMap   :: TypeMap (BaseStringType Char8)

  -- A complex number mapped to an SMTLIB struct.
  ComplexToStructTypeMap:: TypeMap BaseComplexType
  -- A complex number mapped to an SMTLIB array from boolean to real.
  ComplexToArrayTypeMap  :: TypeMap BaseComplexType

  -- An array that is encoded using a builtin SMT theory of arrays.
  --
  -- This theory typically restricts the set of arrays that can be encoded,
  -- but have a decidable equality.
  PrimArrayTypeMap :: !(Ctx.Assignment TypeMap (idxl Ctx.::> idx))
                   -> !(TypeMap tp)
                   -> TypeMap (BaseArrayType (idxl Ctx.::> idx) tp)

  -- An array that is encoded as an SMTLIB function.
  --
  -- The element type must not be an array encoded as a function.
  FnArrayTypeMap :: !(Ctx.Assignment TypeMap (idxl Ctx.::> idx))
                 -> TypeMap tp
                 -> TypeMap (BaseArrayType (idxl Ctx.::> idx) tp)

  -- A struct encoded as an SMTLIB struct/ yices tuple.
  --
  -- None of the fields should be arrays encoded as functions.
  StructTypeMap :: !(Ctx.Assignment TypeMap idx)
                -> TypeMap (BaseStructType idx)


instance ShowF TypeMap

instance Show (TypeMap a) where
  show BoolTypeMap              = "BoolTypeMap"
  show NatTypeMap               = "NatTypeMap"
  show IntegerTypeMap           = "IntegerTypeMap"
  show RealTypeMap              = "RealTypeMap"
  show (BVTypeMap n)            = "BVTypeMap " ++ show n
  show (FloatTypeMap x)         = "FloatTypeMap " ++ show x
  show Char8TypeMap             = "Char8TypeMap"
  show (ComplexToStructTypeMap) = "ComplexToStructTypeMap"
  show ComplexToArrayTypeMap    = "ComplexToArrayTypeMap"
  show (PrimArrayTypeMap ctx a) = "PrimArrayTypeMap " ++ showF ctx ++ " " ++ showF a
  show (FnArrayTypeMap ctx a)   = "FnArrayTypeMap " ++ showF ctx ++ " " ++ showF a
  show (StructTypeMap ctx)      = "StructTypeMap " ++ showF ctx


instance Eq (TypeMap tp) where
  x == y = isJust (testEquality x y)

instance TestEquality TypeMap where
  testEquality BoolTypeMap BoolTypeMap = Just Refl
  testEquality NatTypeMap NatTypeMap = Just Refl
  testEquality IntegerTypeMap IntegerTypeMap = Just Refl
  testEquality RealTypeMap RealTypeMap = Just Refl
  testEquality Char8TypeMap Char8TypeMap = Just Refl
  testEquality (FloatTypeMap x) (FloatTypeMap y) = do
    Refl <- testEquality x y
    return Refl
  testEquality (BVTypeMap x) (BVTypeMap y) = do
    Refl <- testEquality x y
    return Refl
  testEquality ComplexToStructTypeMap ComplexToStructTypeMap =
    Just Refl
  testEquality ComplexToArrayTypeMap ComplexToArrayTypeMap =
    Just Refl
  testEquality (PrimArrayTypeMap xa xr) (PrimArrayTypeMap ya yr) = do
    Refl <- testEquality xa ya
    Refl <- testEquality xr yr
    Just Refl
  testEquality (FnArrayTypeMap xa xr) (FnArrayTypeMap ya yr) = do
    Refl <- testEquality xa ya
    Refl <- testEquality xr yr
    Just Refl
  testEquality (StructTypeMap x) (StructTypeMap y) = do
    Refl <- testEquality x y
    Just Refl
  testEquality _ _ = Nothing

semiRingTypeMap :: SR.SemiRingRepr sr -> TypeMap (SR.SemiRingBase sr)
semiRingTypeMap SR.SemiRingNatRepr         = NatTypeMap
semiRingTypeMap SR.SemiRingIntegerRepr     = IntegerTypeMap
semiRingTypeMap SR.SemiRingRealRepr        = RealTypeMap
semiRingTypeMap (SR.SemiRingBVRepr _flv w) = BVTypeMap w

type ArrayConstantFn v
   = [Some TypeMap]
     -- ^ Type for indices
     -> Some TypeMap
     -- ^ Type for value.
     -> v
     -- ^ Constant to assign all values.
     -> v

-- TODO, I'm not convinced it is valuable to have `SupportTermOps`
-- be a separate class from `SMTWriter`, and I'm really not sold
-- on the `Num` superclass constraint.

-- | A class of values containing rational and operations.
class Num v => SupportTermOps v where
  boolExpr :: Bool -> v

  notExpr  :: v -> v

  andAll :: [v] -> v
  orAll :: [v] -> v

  (.&&)    :: v -> v -> v
  x .&& y = andAll [x, y]

  (.||)    :: v -> v -> v
  x .|| y = orAll [x, y]

  -- | Compare two elements for equality.
  (.==)  :: v -> v -> v

  -- | Compare two elements for in-equality.
  (./=) :: v -> v -> v
  x ./= y = notExpr (x .== y)

  impliesExpr :: v -> v -> v
  impliesExpr x y = notExpr x .|| y

  -- | Create a let expression.  This is a "sequential" let,
  --   which is syntactic sugar for a nested series of single
  --   let bindings.  As a consequence, bound variables are in
  --   scope for the right-hand-sides of subsequent bindings.
  letExpr :: [(Text, v)] -> v -> v

  -- | Create an if-then-else expression.
  ite :: v -> v -> v -> v

  -- | Add a list of values together.
  sumExpr :: [v] -> v
  sumExpr [] = 0
  sumExpr (h:r) = foldl (+) h r

  -- | Convert an integer expression to a real.
  termIntegerToReal :: v -> v

  -- | Convert a real expression to an integer.
  termRealToInteger :: v -> v

  -- | Convert an integer to a term.
  integerTerm :: Integer -> v

  -- | Convert a rational to a term.
  rationalTerm :: Rational -> v

  -- | Less-then-or-equal
  (.<=) :: v -> v -> v

  -- | Less-then
  (.<)  :: v -> v -> v
  x .< y = notExpr (y .<= x)

  -- | Greater then
  (.>)  :: v -> v -> v
  x .> y = y .< x

  -- | Greater then or equal
  (.>=) :: v -> v -> v
  x .>= y = y .<= x

  -- | Integer theory terms
  intAbs :: v -> v
  intDiv :: v -> v -> v
  intMod :: v -> v -> v
  intDivisible :: v -> Natural -> v

  -- | Create expression from bitvector.
  bvTerm :: NatRepr w -> Integer -> v
  bvNeg :: v -> v
  bvAdd :: v -> v -> v
  bvSub :: v -> v -> v
  bvMul :: v -> v -> v

  bvSLe :: v -> v -> v
  bvULe :: v -> v -> v

  bvSLt :: v -> v -> v
  bvULt :: v -> v -> v

  bvUDiv :: v -> v -> v
  bvURem :: v -> v -> v
  bvSDiv :: v -> v -> v
  bvSRem :: v -> v -> v

  bvAnd :: v -> v -> v
  bvOr  :: v -> v -> v
  bvXor :: v -> v -> v
  bvNot :: v -> v

  bvShl  :: v -> v -> v
  bvLshr :: v -> v -> v
  bvAshr :: v -> v -> v

  -- | Concatenate two bitvectors together.
  bvConcat :: v -> v -> v

  -- | @bvExtract w i n v@ extracts bits [i..i+n) from @v@ as a new
  -- bitvector.   @v@ must contain at least @w@ elements, and @i+n@
  -- must be less than or equal to @w@.  The result has @n@ elements.
  -- The least significant bit of @v@ should have index @0@.
  bvExtract :: NatRepr w -> Natural -> Natural -> v -> v

  -- | @bvTestBit w i x@ returns predicate that holds if bit @i@
  -- in @x@ is set to true.  @w@ should be the number of bits in @x@.
  bvTestBit :: NatRepr w -> Natural -> v -> v
  bvTestBit w i x = (bvExtract w i 1 x .== bvTerm w1 1)
    where w1 :: NatRepr 1
          w1 = knownNat

  bvSumExpr :: NatRepr w -> [v] -> v
  bvSumExpr w [] = bvTerm w 0
  bvSumExpr _ (h:r) = foldl bvAdd h r

  floatPZero :: FloatPrecisionRepr fpp -> v
  floatNZero :: FloatPrecisionRepr fpp  -> v
  floatNaN   :: FloatPrecisionRepr fpp  -> v
  floatPInf  :: FloatPrecisionRepr fpp -> v
  floatNInf  :: FloatPrecisionRepr fpp -> v

  floatNeg  :: v -> v
  floatAbs  :: v -> v
  floatSqrt :: RoundingMode -> v -> v

  floatAdd :: RoundingMode -> v -> v -> v
  floatSub :: RoundingMode -> v -> v -> v
  floatMul :: RoundingMode -> v -> v -> v
  floatDiv :: RoundingMode -> v -> v -> v
  floatRem :: v -> v -> v
  floatMin :: v -> v -> v
  floatMax :: v -> v -> v

  floatFMA :: RoundingMode -> v -> v -> v -> v

  floatEq   :: v -> v -> v
  floatFpEq :: v -> v -> v
  floatLe   :: v -> v -> v
  floatLt   :: v -> v -> v

  floatIsNaN      :: v -> v
  floatIsInf      :: v -> v
  floatIsZero     :: v -> v
  floatIsPos      :: v -> v
  floatIsNeg      :: v -> v
  floatIsSubnorm  :: v -> v
  floatIsNorm     :: v -> v

  floatCast       :: FloatPrecisionRepr fpp -> RoundingMode -> v -> v
  floatRound      :: RoundingMode -> v -> v
  floatFromBinary :: FloatPrecisionRepr fpp -> v -> v
  bvToFloat       :: FloatPrecisionRepr fpp -> RoundingMode -> v -> v
  sbvToFloat      :: FloatPrecisionRepr fpp -> RoundingMode -> v -> v
  realToFloat     :: FloatPrecisionRepr fpp -> RoundingMode -> v -> v
  floatToBV       :: Natural -> RoundingMode -> v -> v
  floatToSBV      :: Natural -> RoundingMode -> v -> v
  floatToReal     :: v -> v

  -- | Predicate that holds if a real number is an integer.
  realIsInteger :: v -> v

  realSin :: v -> v

  realCos :: v -> v

  realATan2 :: v -> v -> v

  realSinh :: v -> v

  realCosh :: v -> v

  realExp  :: v -> v

  realLog  :: v -> v

  -- | Apply the arguments to the given function.
  smtFnApp :: v -> [v] -> v

  -- | Update a function value to return a new value at the given point.
  --
  -- This may be Nothing if solver has no builtin function for update.
  smtFnUpdate :: Maybe (v -> [v] -> v -> v)
  smtFnUpdate = Nothing

  -- | Function for creating a lambda term if output supports it.
  --
  -- Yices support lambda expressions, but SMTLIB2 does not.
  -- The function takes arguments and the expression.
  lambdaTerm :: Maybe ([(Text, Some TypeMap)] -> v -> v)
  lambdaTerm = Nothing

  fromText :: Text -> v


infixr 3 .&&
infixr 2 .||
infix 4 .==
infix 4 ./=
infix 4 .>
infix 4 .>=
infix 4 .<
infix 4 .<=

------------------------------------------------------------------------
-- Term

structComplexRealPart :: forall h. SMTWriter h => Term h -> Term h
structComplexRealPart c = structProj @h (Ctx.Empty Ctx.:> RealTypeMap Ctx.:> RealTypeMap) (Ctx.natIndex @0) c

structComplexImagPart :: forall h. SMTWriter h => Term h -> Term h
structComplexImagPart c = structProj @h (Ctx.Empty Ctx.:> RealTypeMap Ctx.:> RealTypeMap) (Ctx.natIndex @1) c

arrayComplexRealPart :: forall h . SMTWriter h => Term h -> Term h
arrayComplexRealPart c = arraySelect @h c [boolExpr False]

arrayComplexImagPart :: forall h . SMTWriter h => Term h -> Term h
arrayComplexImagPart c = arraySelect @h c [boolExpr True]

app :: Builder -> [Builder] -> Builder
app o [] = o
app o args = app_list o args

app_list :: Builder -> [Builder] -> Builder
app_list o args = "(" <> o <> go args
  where go [] = ")"
        go (f:r) = " " <> f <> go r

builder_list :: [Builder] -> Builder
builder_list [] = "()"
builder_list (h:l) = app_list h l

------------------------------------------------------------------------
-- Term

-- | A term in the output language.
type family Term (h :: Type) :: Type

------------------------------------------------------------------------
-- SMTExpr

-- | An expresion for the SMT solver together with information about its type.
data SMTExpr h (tp :: BaseType) where
  SMTName :: !(TypeMap tp) -> !Text -> SMTExpr h tp
  SMTExpr :: !(TypeMap tp) -> !(Term h) -> SMTExpr h tp

-- | Converts an SMT to a base expression.
asBase :: SupportTermOps (Term h)
       => SMTExpr h tp
       -> Term h
asBase (SMTName _ n) = fromText n
asBase (SMTExpr _ e) = e

smtExprType :: SMTExpr h tp -> TypeMap tp
smtExprType (SMTName tp _) = tp
smtExprType (SMTExpr tp _) = tp

------------------------------------------------------------------------
-- WriterState

-- | State for writer.
data WriterState = WriterState { _nextTermIdx :: !Word64
                               , _lastPosition :: !Position
                               , _position     :: !Position
                               }

-- | The next index to use in dynamically generating a variable name.
nextTermIdx :: Simple Lens WriterState Word64
nextTermIdx = lens _nextTermIdx (\s v -> s { _nextTermIdx = v })

-- | Last position written to file.
lastPosition :: Simple Lens WriterState Position
lastPosition = lens _lastPosition (\s v -> s { _lastPosition = v })

-- | Position written to file.
position :: Simple Lens WriterState Position
position = lens _position (\s v -> s { _position = v })

emptyState :: WriterState
emptyState = WriterState { _nextTermIdx     = 0
                         , _lastPosition = InternalPos
                         , _position     = InternalPos
                         }

-- | Create a new variable
--
-- Variable names have a prefix, an exclamation mark and a unique number.
-- The MSS system ensures that no
freshVarName :: State WriterState Text
freshVarName = freshVarName' "x!"

-- | Create a new variable
--
-- Variable names have a prefix, an exclamation mark and a unique number.
-- The MSS system ensures that no
freshVarName' :: Builder -> State WriterState Text
freshVarName' prefix = do
  n <- use nextTermIdx
  nextTermIdx += 1
  return $! (Lazy.toStrict $ Builder.toLazyText $ prefix <> Builder.decimal n)

------------------------------------------------------------------------
-- SMTWriter

data SMTSymFn ctx where
  SMTSymFn :: !Text
           -> !(Ctx.Assignment TypeMap args)
           -> !(TypeMap ret)
           -> SMTSymFn (args Ctx.::> ret)

data StackEntry t (h :: Type) = StackEntry
  { symExprCache :: !(IdxCache t (SMTExpr h))
  , symFnCache :: !(PH.HashTable PH.RealWorld (Nonce t) SMTSymFn)
  }

-- The writer connection maintains a connection to the SMT solver.
--
-- It is responsible for knowing the capabilities of the solver; generating
-- fresh names when needed; maintaining the stack of pushes and pops, and
-- sending queries to the solver.
data WriterConn t (h :: Type) =
  WriterConn { smtWriterName :: !String
               -- ^ Name of writer for error reporting purposes.
             , connHandle :: !(OutputStream Text)
               -- ^ Handle to write to
             , supportFunctionDefs :: !Bool
               -- ^ Indicates if the writer can define constants or functions in terms
               -- of an expression.
               --
               -- If this is not supported, we can only declare free variables, and
               -- assert that they are equal.
             , supportFunctionArguments :: !Bool
               -- ^ Functions may be passed as arguments to other functions.
               --
               -- We currently never allow SMT_FnType to appear in structs or array
               -- indices.
             , supportQuantifiers :: !Bool
               -- ^ Allow the SMT writer to generate problems with quantifiers.
             , supportedFeatures :: !ProblemFeatures
               -- ^ Indicates features supported by the solver.
             , entryStack :: !(IORef [StackEntry t h])
               -- ^ A stack of pairs of hash tables, each stack entry corresponding to
               --   a lexical scope induced by frame push/pops. The entire stack is searched
               --   top-down when looking up element nonce values. Elements that are to
               --   persist across pops are written through the entire stack.
             , stateRef :: !(IORef WriterState)
               -- ^ Reference to current state
             , varBindings :: !(SymbolVarBimap t)
               -- ^ Symbol variables.
             , connState :: !h
               -- ^ The specific connection information.
             , consumeAcknowledgement :: AcknowledgementAction t h
               -- ^ Consume an acknowledgement notifications the solver, if
               --   it produces one
             }

-- | An action for consuming an acknowledgement message from the solver,
--   if it is configured to produce ack messages.
newtype AcknowledgementAction t h =
  AckAction { runAckAction :: WriterConn t h -> Command h -> IO () }

-- | An acknowledgement action that does nothing
nullAcknowledgementAction :: AcknowledgementAction t h
nullAcknowledgementAction = AckAction (\_ _ -> return ())

newStackEntry :: IO (StackEntry t h)
newStackEntry = do
  exprCache <- newIdxCache
  fnCache   <- stToIO $ PH.new
  return StackEntry
    { symExprCache = exprCache
    , symFnCache   = fnCache
    }

-- | Clear the entry stack, and start with a fresh one.
resetEntryStack :: WriterConn t h -> IO ()
resetEntryStack c = do
  entry <- newStackEntry
  writeIORef (entryStack c) [entry]

-- | Return the number of pushed stack frames.  Note, this is one
--   fewer than the number of entries in the stack beacuse the
--   base entry is the top-level context that is not in the scope
--   of any push.
entryStackHeight :: WriterConn t h -> IO Int
entryStackHeight c =
  do es <- readIORef (entryStack c)
     return (length es - 1)

-- | Push a new frame to the stack for maintaining the writer cache.
pushEntryStack :: WriterConn t h -> IO ()
pushEntryStack c = do
  entry <- newStackEntry
  modifyIORef' (entryStack c) $ (entry:)

popEntryStack :: WriterConn t h -> IO ()
popEntryStack c = do
  stk <- readIORef (entryStack c)
  case stk of
   []  -> fail "Could not pop from empty entry stack."
   [_] -> fail "Could not pop from empty entry stack."
   (_:r) -> writeIORef (entryStack c) r

newWriterConn :: OutputStream Text
              -> AcknowledgementAction t cs
              -- ^ An action to consume solver acknowledgement responses
              -> String
              -- ^ Name of solver for reporting purposes.
              -> ProblemFeatures
              -- ^ Indicates what features are supported by the solver.
              -> SymbolVarBimap t
              -- ^ A bijective mapping between variables and their
              -- canonical name (if any).
              -> cs -- ^ State information specific to the type of connection
              -> IO (WriterConn t cs)
newWriterConn h ack solver_name features bindings cs = do
  entry <- newStackEntry
  stk_ref <- newIORef [entry]
  r <- newIORef emptyState
  return $! WriterConn { smtWriterName = solver_name
                       , connHandle    = h
                       , supportFunctionDefs      = False
                       , supportFunctionArguments = False
                       , supportQuantifiers       = False
                       , supportedFeatures        = features
                       , entryStack   = stk_ref
                       , stateRef     = r
                       , varBindings  = bindings
                       , connState    = cs
                       , consumeAcknowledgement = ack
                       }

-- | Status to indicate when term value will be uncached.
data TermLifetime
   = DeleteNever
     -- ^ Never delete the term
   | DeleteOnPop
     -- ^ Delete the term when the current frame is popped.
  deriving (Eq)

cacheValue
  :: WriterConn t h
  -> TermLifetime
  -> (StackEntry t h -> IO ())
  -> IO ()
cacheValue conn lifetime insert_action =
  readIORef (entryStack conn) >>= \case
    s@(h:_) -> case lifetime of
      DeleteOnPop -> insert_action h
      DeleteNever -> mapM_ insert_action s
    [] -> error "cacheValue: empty cache stack!"

cacheLookup
  :: WriterConn t h
  -> (StackEntry t h -> IO (Maybe a))
  -> IO (Maybe a)
cacheLookup conn lookup_action =
  readIORef (entryStack conn) >>= firstJustM lookup_action

cacheLookupExpr :: WriterConn t h -> Nonce t tp -> IO (Maybe (SMTExpr h tp))
cacheLookupExpr c n = cacheLookup c $ \entry ->
  lookupIdx (symExprCache entry) n

cacheLookupFn :: WriterConn t h -> Nonce t ctx -> IO (Maybe (SMTSymFn ctx))
cacheLookupFn c n = cacheLookup c $ \entry ->
  stToIO $ PH.lookup (symFnCache entry) n

cacheValueExpr
  :: WriterConn t h -> Nonce t tp -> TermLifetime -> SMTExpr h tp -> IO ()
cacheValueExpr conn n lifetime value = cacheValue conn lifetime $ \entry ->
  insertIdxValue (symExprCache entry) n value

cacheValueFn
  :: WriterConn t h -> Nonce t ctx -> TermLifetime -> SMTSymFn ctx -> IO ()
cacheValueFn conn n lifetime value = cacheValue conn lifetime $ \entry ->
  stToIO $ PH.insert (symFnCache entry) n value

-- | Run state with handle.
withWriterState :: WriterConn t h -> State WriterState a -> IO a
withWriterState c m = do
  s0 <- readIORef (stateRef c)
  let (v,s) = runState m s0
  writeIORef (stateRef c) $! s
  return v

-- | Update the current program location to the given one.
updateProgramLoc :: WriterConn t h -> ProgramLoc -> IO ()
updateProgramLoc c l = withWriterState c $ position .= plSourceLoc l

type family Command (h :: Type) :: Type

-- | Typeclass need to generate SMTLIB commands.
class (SupportTermOps (Term h)) => SMTWriter h where

  -- | Create a forall expression
  forallExpr :: [(Text, Some TypeMap)] -> Term h -> Term h

  -- | Create an exists expression
  existsExpr :: [(Text, Some TypeMap)] -> Term h -> Term h

  -- | Create a constant array
  --
  -- This may return Nothing if the solver does not support constant arrays.
  arrayConstant :: Maybe (ArrayConstantFn (Term h))
  arrayConstant = Nothing

  -- | Select an element from an array
  arraySelect :: Term h -> [Term h] -> Term h

  -- | 'arrayUpdate a i v' returns an array that contains value 'v' at
  -- index 'i', and the same value as in 'a' at every other index.
  arrayUpdate :: Term h -> [Term h] -> Term h -> Term h

  -- | Create a command that just defines a comment.
  commentCommand :: f h -> Builder -> Command h

  -- | Create a command that asserts a formula.
  assertCommand :: f h -> Term h -> Command h

  -- | Create a command that asserts a formula and attaches
  --   the given name to it (primarily for the purposes of
  --   later reporting unsatisfiable cores).
  assertNamedCommand :: f h -> Term h -> Text -> Command h

  -- | Push 1 new scope
  pushCommand   :: f h -> Command h

  -- | Pop 1 existing scope
  popCommand    :: f h -> Command h

  -- | Reset the solver state, forgetting all pushed frames and assertions
  resetCommand  :: f h -> Command h

  -- | Check if the current set of assumption is satisfiable. May
  -- require multiple commands. The intial commands require an ack. The
  -- last one does not.
  checkCommands  :: f h -> [Command h]

  -- | Check if a collection of assumptions is satisfiable in the current context.
  --   The assumptions must be given as the names of literals already in scope.
  checkWithAssumptionsCommands :: f h -> [Text] -> [Command h]

  -- | Ask the solver to return an unsatisfiable core from among the assumptions
  --   passed into the previous "check with assumptions" command.
  getUnsatAssumptionsCommand :: f h -> Command h

  -- | Ask the solver to return an unsatisfiable core from among the named assumptions
  --   previously asserted using the `assertNamedCommand` after an unsatisfiable
  --   `checkCommand`.
  getUnsatCoreCommand :: f h -> Command h

  -- | Set an option/parameter.
  setOptCommand :: f h -> Text -> Text -> Command h

  -- | Declare a new symbol with the given name, arguments types, and result type.
  declareCommand :: f h
                 -> Text
                 -> Ctx.Assignment TypeMap args
                 -> TypeMap rtp
                 -> Command h

  -- | Define a new symbol with the given name, arguments, result type, and
  -- associated expression.
  --
  -- The argument contains the variable name and the type of the variable.
  defineCommand :: f h
                -> Text -- ^ Name of variable
                -> [(Text, Some TypeMap)]
                -> TypeMap rtp
                -> Term h
                -> Command h

  -- | Declare a struct datatype if is has not been already given the number of
  -- arguments in the struct.
  declareStructDatatype :: WriterConn t h -> Ctx.Assignment TypeMap args -> IO ()

  -- | Build a struct term with the given types and fields
  structCtor :: Ctx.Assignment TypeMap args -> [Term h] -> Term h

  -- | Project a field from a struct with the given types
  structProj :: Ctx.Assignment TypeMap args -> Ctx.Index args tp -> Term h -> Term h

  -- | Produce a term representing a string literal
  stringTerm :: ByteString -> Term h

  -- | Compute the length of a term
  stringLength :: Term h -> Term h

  -- | @stringIndexOf s t i@ computes the first index following or at i
  --   where @t@ appears within @s@ as a substring, or -1 if no such
  --   index exists
  stringIndexOf :: Term h -> Term h -> Term h -> Term h

  -- | Test if the first string contains the second string
  stringContains :: Term h -> Term h -> Term h

  -- | Test if the first string is a prefix of the second string
  stringIsPrefixOf :: Term h -> Term h -> Term h

  -- | Test if the first string is a suffix of the second string
  stringIsSuffixOf :: Term h -> Term h -> Term h

  -- | @stringSubstring s off len@ extracts the substring of @s@ starting at index @off@ and
  --   having length @len@.  The result of this operation is undefined if @off@ and @len@
  --   to not specify a valid substring of @s@; in particular, we must have @off+len <= length(s)@.
  stringSubstring :: Term h -> Term h -> Term h -> Term h

  -- | Append the given strings
  stringAppend :: [Term h] -> Term h

  -- | Forget all previously-declared struct types.
  resetDeclaredStructs :: WriterConn t h -> IO ()

  -- | Write a command to the connection.
  writeCommand :: WriterConn t h -> Command h -> IO ()

-- | Write a command to the connection along with position information
-- if it differs from the last position.
addCommand :: SMTWriter h => WriterConn t h -> Command h -> IO ()
addCommand conn cmd = do
  addCommandNoAck conn cmd
  runAckAction (consumeAcknowledgement conn) conn cmd

addCommandNoAck :: SMTWriter h => WriterConn t h -> Command h -> IO ()
addCommandNoAck conn cmd = do
  las <- withWriterState conn $ use lastPosition
  cur <- withWriterState conn $ use position

  -- If the position of the last command differs from the current position, then
  -- write the current position and update the last position.
  when (las /= cur) $ do
    writeCommand conn $ commentCommand conn $ Builder.fromText $ Text.pack $ show $ pretty cur
    withWriterState conn $ lastPosition .= cur

  writeCommand conn cmd

-- | Write a sequence of commands. All but the last should have
-- acknowledgement.
addCommands :: SMTWriter h => WriterConn t h -> [Command h] -> IO ()
addCommands _ [] = fail "internal: empty list in addCommands"
addCommands conn cmds = do
  mapM_ (addCommand conn) (init cmds)
  addCommandNoAck conn (last cmds)

-- | Create a new variable with the given name.
mkFreeVar :: SMTWriter h
          => WriterConn t h
          -> Ctx.Assignment TypeMap args
          -> TypeMap rtp
          -> IO Text
mkFreeVar conn arg_types return_type = do
  var <- withWriterState conn $ freshVarName
  traverseFC_ (declareTypes conn) arg_types
  declareTypes conn return_type
  addCommand conn $ declareCommand conn var arg_types return_type
  return var

mkFreeVar' :: SMTWriter h => WriterConn t h -> TypeMap tp -> IO (SMTExpr h tp)
mkFreeVar' conn tp = SMTName tp <$> mkFreeVar conn Ctx.empty tp

-- | Consider the bound variable as free within the current assumption frame.
bindVarAsFree :: SMTWriter h
              => WriterConn t h
              -> ExprBoundVar t tp
              -> IO ()
bindVarAsFree conn var = do
  cacheLookupExpr conn (bvarId var) >>= \case
    Just _ -> fail $ "Internal error in SMTLIB exporter: bound variables cannot be made free."
                ++ show (bvarId var) ++ " defined at "
                ++ show (plSourceLoc (bvarLoc var)) ++ "."
    Nothing -> do
      smt_type <- runOnLiveConnection conn $ do
        checkVarTypeSupport var
        getBaseSMT_Type var
      var_name <- getSymbolName conn (VarSymbolBinding var)
      declareTypes conn smt_type
      addCommand conn $ declareCommand conn var_name Ctx.empty smt_type
      cacheValueExpr conn (bvarId var) DeleteOnPop $ SMTName smt_type var_name

-- | Assume that the given formula holds.
assumeFormula :: SMTWriter h => WriterConn t h -> Term h -> IO ()
assumeFormula c p = addCommand c (assertCommand c p)

assumeFormulaWithName :: SMTWriter h => WriterConn t h -> Term h -> Text -> IO ()
assumeFormulaWithName conn p nm =
  do unless (supportedFeatures conn `hasProblemFeature` useUnsatCores) $
       fail $ show $ text (smtWriterName conn) <+> text "is not configured to produce UNSAT cores"
     addCommand conn (assertNamedCommand conn p nm)

assumeFormulaWithFreshName :: SMTWriter h => WriterConn t h -> Term h -> IO Text
assumeFormulaWithFreshName conn p =
  do var <- withWriterState conn $ freshVarName
     assumeFormulaWithName conn p var
     return var

-- | Perform any necessary declarations to ensure that the mentioned type map
--   sorts exist in the solver environment.
declareTypes ::
  SMTWriter h =>
  WriterConn t h ->
  TypeMap tp ->
  IO ()
declareTypes conn = \case
  BoolTypeMap -> return ()
  NatTypeMap  -> return ()
  IntegerTypeMap -> return ()
  RealTypeMap    -> return ()
  BVTypeMap _ -> return ()
  FloatTypeMap _ -> return ()
  Char8TypeMap -> return ()
  ComplexToStructTypeMap -> declareStructDatatype conn (Ctx.Empty Ctx.:> RealTypeMap Ctx.:> RealTypeMap)
  ComplexToArrayTypeMap  -> return ()
  PrimArrayTypeMap args ret ->
    do traverseFC_ (declareTypes conn) args
       declareTypes conn ret
  FnArrayTypeMap args ret ->
    do traverseFC_ (declareTypes conn) args
       declareTypes conn ret
  StructTypeMap flds ->
    do traverseFC_ (declareTypes conn) flds
       declareStructDatatype conn flds


data DefineStyle
  = FunctionDefinition
  | EqualityDefinition
 deriving (Eq, Show)

-- | Create a variable name eqivalent to the given expression.
defineSMTVar :: SMTWriter h
             => WriterConn t h
             -> DefineStyle
             -> Text
                -- ^ Name of variable to define
                -- Should not be defined or declared in the current SMT context
             -> [(Text, Some TypeMap)]
                -- ^ Names of variables in term and associated type.
             -> TypeMap rtp -- ^ Type of expression.
             -> Term h
             -> IO ()
defineSMTVar conn defSty var args return_type expr
  | supportFunctionDefs conn && defSty == FunctionDefinition = do
    mapM_ (viewSome (declareTypes conn) . snd) args
    declareTypes conn return_type
    addCommand conn $ defineCommand conn var args return_type expr
  | otherwise = do
    when (not (null args)) $ do
      fail $ smtWriterName conn ++ " interface does not support defined functions."
    declareTypes conn return_type
    addCommand conn $ declareCommand conn var Ctx.empty return_type
    assumeFormula conn $ fromText var .== expr

-- | Create a variable name eqivalent to the given expression.
freshBoundVarName :: SMTWriter h
                  => WriterConn t h
                  -> DefineStyle
                  -> [(Text, Some TypeMap)]
                     -- ^ Names of variables in term and associated type.
                  -> TypeMap rtp -- ^ Type of expression.
                  -> Term h
                  -> IO Text
freshBoundVarName conn defSty args return_type expr = do
  var <- withWriterState conn $ freshVarName
  defineSMTVar conn defSty var args return_type expr
  return var

-- | Function for create a new name given a base type.
data FreshVarFn h = FreshVarFn (forall tp . TypeMap tp -> IO (SMTExpr h tp))

-- | The state of a side collector monad
--
-- This has predicate for introducing new bound variables
data SMTCollectorState t h
  = SMTCollectorState
    { scConn :: !(WriterConn t h)
    , freshBoundTermFn :: !(forall rtp . Text -> [(Text, Some TypeMap)] -> TypeMap rtp -> Term h -> IO ())
      -- ^ 'freshBoundTerm nm args ret_type ret' will record that 'nm(args) = ret'
      -- 'ret_type' should be the type of 'ret'.
    , freshConstantFn  :: !(Maybe (FreshVarFn h))
    , recordSideCondFn :: !(Maybe (Term h -> IO ()))
      -- ^ Called when we need to need to assert a predicate about some
      -- variables.
    }

-- | The SMT term collector
type SMTCollector t h = ReaderT (SMTCollectorState t h) IO

-- | Create a fresh constant
freshConstant :: String -- ^ The name of the constant based on its reaon.
               -> TypeMap tp -- ^ Type of the constant.
               -> SMTCollector t h (SMTExpr h tp)
freshConstant nm tpr = do
  mf <- asks freshConstantFn
  case mf of
   Nothing -> do
     conn <- asks scConn
     liftIO $ do
     loc <- withWriterState conn $ use position
     fail $ "Cannot create the free constant within a function needed to define the "
       ++ nm ++ " term created at " ++ show loc ++ "."
   Just (FreshVarFn f) ->
    liftIO $ f tpr

data BaseTypeError = ComplexTypeUnsupported
                   | ArrayUnsupported
                   | StringTypeUnsupported (Some StringInfoRepr)

-- | Given a solver connection and a base type repr, 'typeMap' attempts to
-- find the best encoding for a variable of that type supported by teh solver.
typeMap :: WriterConn t h  -> BaseTypeRepr tp -> Either BaseTypeError (TypeMap tp)
typeMap conn tp0 = do
  case typeMapFirstClass conn tp0 of
    Right tm -> Right tm
    -- Recover from array unsupported if possible.
    Left ArrayUnsupported
      | supportFunctionDefs conn
      , BaseArrayRepr idxTp eltTp <- tp0 ->
        FnArrayTypeMap <$> traverseFC (typeMapFirstClass conn) idxTp
                       <*> typeMapFirstClass conn eltTp
    -- Pass other functions on.
    Left e -> Left e

-- | This is a helper function for 'typeMap' that only returns values that can
-- be passed as arguments to a function.
typeMapFirstClass :: WriterConn t h -> BaseTypeRepr tp -> Either BaseTypeError (TypeMap tp)
typeMapFirstClass conn tp0 = do
  let feat = supportedFeatures conn
  case tp0 of
    BaseBoolRepr -> Right BoolTypeMap
    BaseBVRepr w -> Right $! BVTypeMap w
    BaseFloatRepr fpp -> Right $! FloatTypeMap fpp
    BaseRealRepr -> Right RealTypeMap
    BaseNatRepr  -> Right NatTypeMap
    BaseIntegerRepr -> Right IntegerTypeMap
    BaseStringRepr Char8Repr -> Right Char8TypeMap
    BaseStringRepr si -> Left (StringTypeUnsupported (Some si))
    BaseComplexRepr
      | feat `hasProblemFeature` useStructs        -> Right ComplexToStructTypeMap
      | feat `hasProblemFeature` useSymbolicArrays -> Right ComplexToArrayTypeMap
      | otherwise -> Left ComplexTypeUnsupported
    BaseArrayRepr idxTp eltTp -> do
      -- This is a proxy for the property we want, because we assume that EITHER
      -- the solver uses symbolic arrays, OR functions are first-class objects
      let mkArray = if feat `hasProblemFeature` useSymbolicArrays
                    then PrimArrayTypeMap
                    else FnArrayTypeMap
      mkArray <$> traverseFC (typeMapFirstClass conn) idxTp
              <*> typeMapFirstClass conn eltTp
    BaseStructRepr flds ->
      StructTypeMap <$> traverseFC (typeMapFirstClass conn) flds

getBaseSMT_Type :: ExprBoundVar t tp -> SMTCollector t h (TypeMap tp)
getBaseSMT_Type v = do
  conn <- asks scConn
  let errMsg typename =
        show
          $   text (show (bvarName v))
          <+> text "is a"
          <+> text typename
          <+> text "variable, and we do not support this with"
          <+> text (smtWriterName conn ++ ".")
  case typeMap conn (bvarType v) of
    Left  (StringTypeUnsupported (Some si)) -> fail $ errMsg ("string " ++ show si)
    Left  ComplexTypeUnsupported -> fail $ errMsg "complex"
    Left  ArrayUnsupported       -> fail $ errMsg "array"
    Right smtType                -> return smtType

-- | Create a fresh bound term from the SMT expression with the given name.
freshBoundFn :: [(Text, Some TypeMap)] -- ^ Arguments expected for function.
             -> TypeMap rtp -- ^ Type of result
             -> Term h   -- ^ Result of function
             -> SMTCollector t h Text
freshBoundFn args tp t = do
  conn <- asks scConn
  f <- asks freshBoundTermFn
  liftIO $ do
    var <- withWriterState conn $ freshVarName
    f var args tp t
    return var

-- | Create a fresh bound term from the SMT expression with the given name.
freshBoundTerm :: TypeMap tp -> Term h -> SMTCollector t h (SMTExpr h tp)
freshBoundTerm tp t = SMTName tp <$> freshBoundFn [] tp t

-- | Create a fresh bound term from the SMT expression with the given name.
freshBoundTerm' :: SupportTermOps (Term h) => SMTExpr h tp -> SMTCollector t h (SMTExpr h tp)
freshBoundTerm' t = SMTName tp <$> freshBoundFn [] tp (asBase t)
  where tp = smtExprType t

-- | Assert a predicate holds as a side condition to some formula.
addSideCondition ::
   String {- ^ Reason that condition is being added. -} ->
   Term h {- ^ Predicate that should hold. -} ->
   SMTCollector t h ()
addSideCondition nm t = do
  conn <- asks scConn
  mf <- asks recordSideCondFn
  loc <- liftIO $ withWriterState conn $ use position
  case mf of
   Just f ->
     liftIO $ f t
   Nothing -> do
     fail $ "Cannot add a side condition within a function needed to define the "
       ++ nm ++ " term created at " ++ show loc ++ "."

addPartialSideCond ::
  forall t h tp.
  SMTWriter h =>
  WriterConn t h ->
  Term h ->
  TypeMap tp ->
  Maybe (AbstractValue tp) ->
  SMTCollector t h ()

-- NB, nats have a side condition even if there is no abstract domain
addPartialSideCond _ t NatTypeMap Nothing =
  do addSideCondition "nat_range" $ t .>= 0

-- in all other cases, no abstract domain information means unconstrained values
addPartialSideCond _ _ _ Nothing = return ()

addPartialSideCond _ t BoolTypeMap (Just abv) =
  case abv of
    Nothing -> return ()
    Just b  -> addSideCondition "bool_val" $ t .== boolExpr b

addPartialSideCond _ t NatTypeMap (Just rng) =
  do addSideCondition "nat_range" $ t .>= integerTerm (toInteger (natRangeLow rng))
     case natRangeHigh rng of
       Unbounded -> return ()
       Inclusive hi -> addSideCondition "nat_range" $ t .<= integerTerm (toInteger hi)

addPartialSideCond _ t IntegerTypeMap (Just rng) =
  do case rangeLowBound rng of
       Unbounded -> return ()
       Inclusive lo -> addSideCondition "int_range" $ t .>= integerTerm lo
     case rangeHiBound rng of
       Unbounded -> return ()
       Inclusive hi -> addSideCondition "int_range" $ t .<= integerTerm hi

addPartialSideCond _ t RealTypeMap (Just rng) =
  do case rangeLowBound (ravRange rng) of
       Unbounded -> return ()
       Inclusive lo -> addSideCondition "real_range" $ t .>= rationalTerm lo
     case rangeHiBound (ravRange rng) of
       Unbounded -> return ()
       Inclusive hi -> addSideCondition "real_range" $ t .<= rationalTerm hi

addPartialSideCond _ t (BVTypeMap w) (Just rng) = mapM_ assertRange (BVD.ranges w rng)
 where
 assertRange (lo,hi) =
   do when (lo > 0)
           (addSideCondition "bv_range" $ bvULe (bvTerm w lo) t)
      when (hi < maxUnsigned w)
           (addSideCondition "bv_range" $ bvULe t (bvTerm w hi))

addPartialSideCond _ t (Char8TypeMap) (Just (StringAbs len)) =
  do case natRangeLow len of
       0 -> return ()
       lo -> addSideCondition "string length low range" $
               integerTerm (toInteger lo) .<= stringLength @h t
     case natRangeHigh len of
       Unbounded -> return ()
       Inclusive hi ->
         addSideCondition "string length high range" $
           stringLength @h t .<= integerTerm (toInteger hi)

addPartialSideCond _ _ (FloatTypeMap _) (Just ()) = return ()

addPartialSideCond conn t ComplexToStructTypeMap (Just (realRng :+ imagRng)) =
  do let r = arrayComplexRealPart @h t
     let i = arrayComplexImagPart @h t
     addPartialSideCond conn r RealTypeMap (Just realRng)
     addPartialSideCond conn i RealTypeMap (Just imagRng)

addPartialSideCond conn t ComplexToArrayTypeMap (Just (realRng :+ imagRng)) =
  do let r = arrayComplexRealPart @h t
     let i = arrayComplexImagPart @h t
     addPartialSideCond conn r RealTypeMap (Just realRng)
     addPartialSideCond conn i RealTypeMap (Just imagRng)

addPartialSideCond conn t (StructTypeMap ctx) (Just abvs) =
     Ctx.forIndex (Ctx.size ctx)
        (\start i ->
            do start
               addPartialSideCond conn
                 (structProj @h ctx i t)
                 (ctx Ctx.! i)
                 (Just (unwrapAV (abvs Ctx.! i))))
        (return ())

addPartialSideCond _ _t (PrimArrayTypeMap _idxTp _resTp) (Just _abv) =
  fail "SMTWriter.addPartialSideCond: bounds on array values not supported"
addPartialSideCond _ _t (FnArrayTypeMap _idxTp _resTp) (Just _abv) =
  fail "SMTWriter.addPartialSideCond: bounds on array values not supported"


-- | This runs the collector on the connection
runOnLiveConnection :: SMTWriter h => WriterConn t h -> SMTCollector t h a -> IO a
runOnLiveConnection conn coll = runReaderT coll s
  where s = SMTCollectorState
              { scConn = conn
              , freshBoundTermFn = defineSMTVar conn FunctionDefinition
              , freshConstantFn  = Just $! FreshVarFn (mkFreeVar' conn)
              , recordSideCondFn = Just $! assumeFormula conn
              }

prependToRefList :: IORef [a] -> a -> IO ()
prependToRefList r a = seq a $ modifyIORef' r (a:)

freshSandboxBoundTerm :: SupportTermOps v
                      => IORef [(Text, v)]
                      -> Text -- ^ Name to define.
                      -> [(Text, Some TypeMap)] -- Argument name and types.
                      -> TypeMap rtp
                      -> v
                      -> IO ()
freshSandboxBoundTerm ref var [] _ t = do
  prependToRefList ref (var,t)
freshSandboxBoundTerm ref var args _ t = do
  case lambdaTerm of
    Nothing -> do
      fail $ "Cannot create terms with arguments inside defined functions."
    Just lambdaFn -> do
      let r = lambdaFn args t
      seq r $ prependToRefList ref (var, r)

freshSandboxConstant :: WriterConn t h
                     -> IORef [(Text, Some TypeMap)]
                     -> TypeMap tp
                     -> IO (SMTExpr h tp)
freshSandboxConstant conn ref tp = do
  var <- withWriterState conn $ freshVarName
  prependToRefList ref (var, Some tp)
  return $! SMTName tp var

-- | This describes the result that was collected from the solver.
data CollectorResults h a =
  CollectorResults { crResult :: !a
                     -- ^ Result from sandboxed computation.
                   , crBindings :: !([(Text, Term h)])
                     -- ^ List of bound variables.
                   , crFreeConstants :: !([(Text, Some TypeMap)])
                     -- ^ Constants added during generation.
                   , crSideConds :: !([Term h])
                     -- ^ List of Boolean predicates asserted by collector.
                   }

-- | Create a forall expression from a CollectorResult.
forallResult :: forall h
             .  SMTWriter h
             => CollectorResults h (Term h)
             -> Term h
forallResult cr =
  forallExpr @h (crFreeConstants cr) $
    letExpr (crBindings cr) $
      impliesAllExpr (crSideConds cr) (crResult cr)

-- | @impliesAllExpr l r@ returns an expression equivalent to
-- forall l implies r.
impliesAllExpr :: SupportTermOps v => [v] -> v -> v
impliesAllExpr l r = orAll ((notExpr <$> l) ++ [r])

-- | Create a forall expression from a CollectorResult.
existsResult :: forall h
             .  SMTWriter h
             => CollectorResults h (Term h)
             -> Term h
existsResult cr =
  existsExpr @h (crFreeConstants cr) $
    letExpr (crBindings cr) $
      andAll (crSideConds cr ++ [crResult cr])

-- | This runs the side collector and collects the results.
runInSandbox :: SupportTermOps (Term h)
             => WriterConn t h
             -> SMTCollector t h a
             -> IO (CollectorResults h a)
runInSandbox conn sc = do
  -- A list of bound terms.
  boundTermRef    <- newIORef []
  -- A list of free constants
  freeConstantRef <- (newIORef [] :: IO (IORef [(Text, Some TypeMap)]))
  -- A list of references to side conditions.
  sideCondRef     <- newIORef []

  let s = SMTCollectorState
          { scConn = conn
          , freshBoundTermFn = freshSandboxBoundTerm boundTermRef
          , freshConstantFn  = Just $! FreshVarFn (freshSandboxConstant conn freeConstantRef)
          , recordSideCondFn = Just $! prependToRefList sideCondRef
          }
  r <- runReaderT sc s

  boundTerms    <- readIORef boundTermRef
  freeConstants <- readIORef freeConstantRef
  sideConds     <- readIORef sideCondRef
  return $! CollectorResults { crResult = r
                             , crBindings = reverse boundTerms
                             , crFreeConstants = reverse freeConstants
                             , crSideConds = reverse sideConds
                             }

-- | Cache the result of writing an Expr named by the given nonce.
cacheWriterResult :: Nonce t tp
                     -- ^ Nonce to associate term with
                  -> TermLifetime
                     -- ^ Lifetime of term
                  -> SMTCollector t h (SMTExpr h tp)
                     -- ^ Action to create term.
                  -> SMTCollector t h (SMTExpr h tp)
cacheWriterResult n lifetime fallback = do
  c <- asks scConn
  (liftIO $ cacheLookupExpr c n) >>= \case
    Just x -> return x
    Nothing -> do
      x <- fallback
      liftIO $ cacheValueExpr c n lifetime x
      return x

-- | Associate a bound variable with the givne SMT Expression until
-- the a
bindVar :: ExprBoundVar t tp
        -- ^ Variable to bind
        -> SMTExpr h tp
        -- ^ SMT Expression to bind to var.
        -> SMTCollector t h ()
bindVar v x  = do
  let n = bvarId v
  c <- asks scConn
  liftIO $ do
    whenM (isJust <$> cacheLookupExpr c n) $ fail "Variable is already bound."
    cacheValueExpr c n DeleteOnPop x

------------------------------------------------------------------------
-- Evaluate applications.

-- @bvIntTerm w x@ builds an integer term that has the same value as
-- the unsigned integer value of the bitvector @x@.  This is done by
-- explicitly decomposing the positional notation of the bitvector
-- into a sum of powers of 2.
bvIntTerm :: forall v w
           . (SupportTermOps v, 1 <= w)
          => NatRepr w
          -> v
          -> v
bvIntTerm w x = sumExpr ((\i -> digit (i-1)) <$> [1..natValue w])
 where digit :: Natural -> v
       digit d = ite (bvTestBit w d x)
                     (fromInteger (2^d))
                     0

sbvIntTerm :: SupportTermOps v
           => NatRepr w
           -> v
           -> v
sbvIntTerm w0 x0 = sumExpr (signed_offset : go w0 x0 (natValue w0 - 2))
 where signed_offset = ite (bvTestBit w0 (natValue w0 - 1) x0)
                           (fromInteger (negate (2^(widthVal w0 - 1))))
                           0
       go :: SupportTermOps v => NatRepr w -> v -> Natural -> [v]
       go w x n
        | n > 0     = digit w x n : go w x (n-1)
        | n == 0    = [digit w x 0]
        | otherwise = [] -- this branch should only be called in the degenerate case
                         -- of length 1 signed bitvectors

       digit :: SupportTermOps v => NatRepr w -> v -> Natural -> v
       digit w x d = ite (bvTestBit w d x)
                         (fromInteger (2^d))
                         0

unsupportedTerm  :: Monad m => Expr t tp -> m a
unsupportedTerm e =
  fail $ show $
    text "Cannot generate solver output for term generated at"
      <+> pretty (plSourceLoc (exprLoc e)) <> text ":" <$$>
    indent 2 (pretty e)

-- | Checks whether a variable is supported.
--
-- Returns the SMT type of the variable and a predicate (if needed) that the variable
-- should be assumed to hold.  This is used for Natural number variables.
checkVarTypeSupport :: ExprBoundVar n tp -> SMTCollector n h ()
checkVarTypeSupport var = do
  let t = BoundVarExpr var
  case bvarType var of
    BaseNatRepr     -> checkIntegerSupport t
    BaseIntegerRepr -> checkIntegerSupport t
    BaseRealRepr    -> checkLinearSupport t
    BaseComplexRepr -> checkLinearSupport t
    BaseStringRepr _ -> checkStringSupport t
    BaseFloatRepr _  -> checkFloatSupport t
    BaseBVRepr _     -> checkBitvectorSupport t
    _ -> return ()

theoryUnsupported :: Monad m => WriterConn t h -> String -> Expr t tp -> m a
theoryUnsupported conn theory_name t =
  fail $ show $
    text (smtWriterName conn) <+> text "does not support the" <+> text theory_name
    <+> text "term generated at" <+> pretty (plSourceLoc (exprLoc t)) <> text ":" <$$>
    indent 2 (pretty t)


checkIntegerSupport :: Expr t tp -> SMTCollector t h ()
checkIntegerSupport t = do
  conn <- asks scConn
  unless (supportedFeatures conn `hasProblemFeature` useIntegerArithmetic) $ do
    theoryUnsupported conn "integer arithmetic" t

checkStringSupport :: Expr t tp -> SMTCollector t h ()
checkStringSupport t = do
  conn <- asks scConn
  unless (supportedFeatures conn `hasProblemFeature` useStrings) $ do
    theoryUnsupported conn "string" t

checkBitvectorSupport :: Expr t tp -> SMTCollector t h ()
checkBitvectorSupport t = do
  conn <- asks scConn
  unless (supportedFeatures conn `hasProblemFeature` useBitvectors) $ do
    theoryUnsupported conn "bitvectors" t

checkFloatSupport :: Expr t tp -> SMTCollector t h ()
checkFloatSupport t = do
  conn <- asks scConn
  unless (supportedFeatures conn `hasProblemFeature` useFloatingPoint) $ do
    theoryUnsupported conn "floating-point arithmetic" t

checkLinearSupport :: Expr t tp -> SMTCollector t h ()
checkLinearSupport t = do
  conn <- asks scConn
  unless (supportedFeatures conn `hasProblemFeature` useLinearArithmetic) $ do
    theoryUnsupported conn "linear arithmetic" t

checkNonlinearSupport :: Expr t tp -> SMTCollector t h ()
checkNonlinearSupport t = do
  conn <- asks scConn
  unless (supportedFeatures conn `hasProblemFeature` useNonlinearArithmetic) $ do
    theoryUnsupported conn "non-linear arithmetic" t

checkComputableSupport :: Expr t tp -> SMTCollector t h ()
checkComputableSupport t = do
  conn <- asks scConn
  unless (supportedFeatures conn `hasProblemFeature` useComputableReals) $ do
    theoryUnsupported conn "computable arithmetic" t

checkQuantifierSupport :: String -> Expr t p -> SMTCollector t h ()
checkQuantifierSupport nm t = do
  conn <- asks scConn
  when (supportQuantifiers conn == False) $ do
    theoryUnsupported conn nm t

-- | Check that the types can be passed to functions.
checkArgumentTypes :: WriterConn t h -> Ctx.Assignment TypeMap args -> IO ()
checkArgumentTypes conn types = do
  forFC_ types $ \tp -> do
    case tp of
      FnArrayTypeMap{} | supportFunctionArguments conn == False -> do
          fail $ show $ text (smtWriterName conn)
             <+> text  "does not allow arrays encoded as functions to be function arguments."
      _ ->
        return ()

-- | This generates an error message from a solver and a type error.
--
-- It issed for error reporting
type SMTSource = String -> BaseTypeError -> Doc

ppBaseTypeError :: BaseTypeError -> Doc
ppBaseTypeError ComplexTypeUnsupported = text "complex values"
ppBaseTypeError ArrayUnsupported = text "arrays encoded as a functions"
ppBaseTypeError (StringTypeUnsupported (Some si)) = text ("string values " ++ show si)

eltSource :: Expr t tp -> SMTSource
eltSource e solver_name cause =
  text solver_name <+>
  text "does not support" <+> ppBaseTypeError cause <>
  text ", and cannot interpret the term generated at" <+>
  pretty (plSourceLoc (exprLoc e)) <> text ":" <$$>
  indent 2 (pretty e) <> text "."

fnSource :: SolverSymbol -> ProgramLoc -> SMTSource
fnSource fn_name loc solver_name cause =
  text solver_name <+>
  text "does not support" <+> ppBaseTypeError cause <>
  text ", and cannot interpret the function" <+> text (show fn_name) <+>
  text "generated at" <+> pretty (plSourceLoc loc) <> text "."

-- | Evaluate a base type repr as a first class SMT type.
--
-- First class types are those that can be passed as function arguments and
-- returned by functions.
evalFirstClassTypeRepr :: Monad m
                       => WriterConn t h
                       -> SMTSource
                       -> BaseTypeRepr tp
                       -> m (TypeMap tp)
evalFirstClassTypeRepr conn src base_tp =
  case typeMapFirstClass conn base_tp of
    Left e -> fail $ show $ src (smtWriterName conn) e
    Right smt_ret -> return smt_ret

withConnEntryStack :: WriterConn t h -> IO a -> IO a
withConnEntryStack conn = bracket_ (pushEntryStack conn) (popEntryStack conn)

-- | Convert structure to list.
mkIndexLitTerm :: SupportTermOps v
               => IndexLit tp
               -> v
mkIndexLitTerm (NatIndexLit i) = fromIntegral i
mkIndexLitTerm (BVIndexLit w i) = bvTerm w i

-- | Convert structure to list.
mkIndexLitTerms :: SupportTermOps v
                => Ctx.Assignment IndexLit ctx
                -> [v]
mkIndexLitTerms = toListFC mkIndexLitTerm

-- | Create index arguments with given type.
--
-- Returns the name of the argument and the type.
createTypeMapArgsForArray :: forall t h args
                          .  WriterConn t h
                          -> Ctx.Assignment TypeMap args
                          -> IO [(Text, Some TypeMap)]
createTypeMapArgsForArray conn types = do
  -- Create names for index variables.
  let mkIndexVar :: TypeMap utp -> IO (Text, Some TypeMap)
      mkIndexVar base_tp = do
        i_nm <- withWriterState conn $ freshVarName' "i!"
        return (i_nm, Some base_tp)
  -- Get SMT arguments.
  sequence $ toListFC mkIndexVar types

smt_array_select :: forall h idxl idx tp
                 .  SMTWriter h
                 => SMTExpr h (BaseArrayType (idxl Ctx.::> idx) tp)
                 -> [Term h]
                 -> SMTExpr h tp
smt_array_select aexpr idxl =
  case smtExprType aexpr of
    PrimArrayTypeMap _ res_type ->
      SMTExpr res_type $ arraySelect @h (asBase aexpr) idxl
    FnArrayTypeMap _ res_type ->
      SMTExpr res_type $ smtFnApp (asBase aexpr) idxl

-- | Get name associated with symbol binding if defined, creating it if needed.
getSymbolName :: WriterConn t h -> SymbolBinding t -> IO Text
getSymbolName conn b =
  case lookupSymbolOfBinding b (varBindings conn) of
    Just sym -> return $! solverSymbolAsText sym
    Nothing -> withWriterState conn $ freshVarName

-- | 'defineSMTFunction conn var action' will introduce a function
--
-- It returns the return type of the value.
-- Note: This function is declared at a global scope.  It bypasses
-- any subfunctions.  We need to investigate how to support nested
-- functions.
defineSMTFunction :: SMTWriter h
                  => WriterConn t h
                  -> Text
                  -> (FreshVarFn h -> SMTCollector t h (SMTExpr h ret))
                     -- ^ Action to generate
                  -> IO (TypeMap ret)
defineSMTFunction conn var action =
  withConnEntryStack conn $ do
    -- A list of bound terms.
    freeConstantRef <- (newIORef [] :: IO (IORef [(Text, Some TypeMap)]))
    boundTermRef    <- newIORef []
    let s = SMTCollectorState { scConn = conn
                              , freshBoundTermFn = freshSandboxBoundTerm boundTermRef
                              , freshConstantFn  = Nothing
                              , recordSideCondFn = Nothing
                              }
    -- Associate a variable with each bound variable
    let varFn = FreshVarFn (freshSandboxConstant conn freeConstantRef)
    pair <- flip runReaderT s (action varFn)

    args       <- readIORef freeConstantRef
    boundTerms <- readIORef boundTermRef

    let res = letExpr (reverse boundTerms) (asBase pair)

    defineSMTVar conn FunctionDefinition var (reverse args) (smtExprType pair) res
    return $! smtExprType pair

------------------------------------------------------------------------
-- Mutually recursive functions for translating What4 expressions to SMTLIB definitions.

-- | Convert an expression into a SMT Expression.
mkExpr :: forall h t tp. SMTWriter h => Expr t tp -> SMTCollector t h (SMTExpr h tp)
mkExpr (BoolExpr b _) =
  return (SMTExpr BoolTypeMap (boolExpr b))
mkExpr t@(SemiRingLiteral SR.SemiRingNatRepr n _) = do
  checkLinearSupport t
  return (SMTExpr NatTypeMap (fromIntegral n))
mkExpr t@(SemiRingLiteral SR.SemiRingIntegerRepr i _) = do
  checkLinearSupport t
  return (SMTExpr IntegerTypeMap (fromIntegral i))
mkExpr t@(SemiRingLiteral SR.SemiRingRealRepr r _) = do
  checkLinearSupport t
  return (SMTExpr RealTypeMap (rationalTerm r))
mkExpr t@(SemiRingLiteral (SR.SemiRingBVRepr _flv w) x _) = do
  checkLinearSupport t
  return $ SMTExpr (BVTypeMap w) $ bvTerm w x
mkExpr t@(StringExpr l _) =
  case l of
    Char8Literal bs -> do
      checkStringSupport t
      return $ SMTExpr Char8TypeMap $ stringTerm @h bs
    _ -> do
      conn <- asks scConn
      theoryUnsupported conn ("strings " ++ show (stringLiteralInfo l)) t

mkExpr (NonceAppExpr ea) =
  cacheWriterResult (nonceExprId ea) DeleteOnPop $
    predSMTExpr ea
mkExpr (AppExpr ea) =
  cacheWriterResult (appExprId ea) DeleteOnPop $ do
    appSMTExpr ea
mkExpr (BoundVarExpr var) = do
  case bvarKind var of
   QuantifierVarKind -> do
     conn <- asks scConn
     mr <- liftIO $ cacheLookupExpr conn (bvarId var)
     case mr of
      Just x -> return x
      Nothing -> do
        fail $ "Internal error in SMTLIB exporter due to unbound variable "
            ++ show (bvarId var) ++ " defined at "
            ++ show (plSourceLoc (bvarLoc var)) ++ "."
   LatchVarKind ->
     fail $ "SMTLib exporter does not support the latch defined at "
            ++ show (plSourceLoc (bvarLoc var)) ++ "."
   UninterpVarKind -> do
     conn <- asks scConn
     cacheWriterResult (bvarId var) DeleteNever $ do
       checkVarTypeSupport var
       -- Use predefined var name if it has not been defined.
       var_name <- liftIO $ getSymbolName conn (VarSymbolBinding var)

       smt_type <- getBaseSMT_Type var

       liftIO $
         do declareTypes conn smt_type
            addCommand conn $ declareCommand conn var_name Ctx.empty smt_type

       -- Add assertion based on var type.
       addPartialSideCond conn (fromText var_name) smt_type (bvarAbstractValue var)

       -- Return variable name
       return $ SMTName smt_type var_name

-- | Convert an element to a base expression.
mkBaseExpr :: SMTWriter h => Expr t tp -> SMTCollector t h (Term h)
mkBaseExpr e = asBase <$> mkExpr e

-- | Convert structure to list.
mkIndicesTerms :: SMTWriter h
               => Ctx.Assignment (Expr t) ctx
               -> SMTCollector t h [Term h]
mkIndicesTerms = foldrFC (\e r -> (:) <$> mkBaseExpr e <*> r) (pure [])

predSMTExpr :: forall t h tp
             . SMTWriter h
            => NonceAppExpr t tp
            -> SMTCollector t h (SMTExpr h tp)
predSMTExpr e0 = do
  conn <- asks scConn
  let i = NonceAppExpr e0
  h <- asks scConn
  liftIO $ updateProgramLoc h (nonceExprLoc e0)
  case nonceExprApp e0 of
    Forall var e -> do
      checkQuantifierSupport "universal quantifier" i
      cr <- liftIO $ withConnEntryStack conn $ do
        runInSandbox conn $ do
          checkVarTypeSupport var
          smtType <- getBaseSMT_Type var

          Just (FreshVarFn f) <- asks freshConstantFn
          t <- liftIO $ f smtType
          bindVar var t

          addPartialSideCond conn (asBase t) smtType (bvarAbstractValue var)
          mkBaseExpr e
      freshBoundTerm BoolTypeMap $ forallResult cr
    Exists var e -> do
      checkQuantifierSupport "existential quantifiers" i
      cr <- liftIO $ withConnEntryStack conn $ do
        runInSandbox conn $ do
          checkVarTypeSupport var
          smtType <- getBaseSMT_Type var

          Just (FreshVarFn f) <- asks freshConstantFn
          t <- liftIO $ f smtType
          bindVar var t

          addPartialSideCond conn (asBase t) smtType (bvarAbstractValue var)
          mkBaseExpr e
      freshBoundTerm BoolTypeMap $ existsResult cr

    ArrayFromFn f -> do
      -- Evaluate arg types
      smt_arg_types <-
        traverseFC (evalFirstClassTypeRepr conn (eltSource i))
                   (symFnArgTypes f)
      -- Evaluate simple function
      (smt_f, ret_tp) <- liftIO $ getSMTSymFn conn f smt_arg_types

      let array_tp = FnArrayTypeMap smt_arg_types ret_tp
      return $! SMTName array_tp smt_f

    MapOverArrays f idx_types arrays -> do
      -- :: Ctx.Assignment (ArrayResultWrapper (Expr t) (idx Ctx.::> itp)) ctx)  -> do
      -- Evaluate arg types for indices.

      smt_idx_types <- traverseFC (evalFirstClassTypeRepr conn (eltSource i)) idx_types

      let evalArray :: forall idx itp etp
                     . ArrayResultWrapper (Expr t) (idx Ctx.::> itp) etp
                     -> SMTCollector t h (ArrayResultWrapper (SMTExpr h) (idx Ctx.::> itp) etp)
          evalArray (ArrayResultWrapper a) = ArrayResultWrapper <$> mkExpr a

      smt_arrays <- traverseFC evalArray arrays

      liftIO $ do

      -- Create name of function to reutrn.
      nm <- liftIO $ withWriterState conn $ freshVarName

      ret_type <-
        defineSMTFunction conn nm $ \(FreshVarFn freshVar) -> do
          -- Create type for indices.
          smt_indices <- traverseFC (\tp -> liftIO (freshVar tp)) smt_idx_types

          let idxl = toListFC asBase smt_indices
          let select :: forall  idxl idx etp
                     .  ArrayResultWrapper (SMTExpr h) (idxl Ctx.::> idx) etp
                     -> SMTExpr h etp
              select (ArrayResultWrapper a) = smt_array_select a idxl
          let array_vals = fmapFC select smt_arrays

          (smt_f, ret_type) <- liftIO $ getSMTSymFn conn f (fmapFC smtExprType array_vals)

          return $ SMTExpr ret_type $ smtFnApp (fromText smt_f) (toListFC asBase array_vals)


      let array_tp = FnArrayTypeMap smt_idx_types ret_type
      return $! SMTName array_tp nm

    ArrayTrueOnEntries{} -> do
      fail $ "SMTWriter does not yet support ArrayTrueOnEntries.\n" ++ show i

    FnApp f args -> do
      smt_args <- traverseFC mkExpr args
      (smt_f, ret_type) <- liftIO $ getSMTSymFn conn f (fmapFC smtExprType smt_args)
      freshBoundTerm ret_type $! smtFnApp (fromText smt_f) (toListFC asBase smt_args)


appSMTExpr :: forall t h tp
            . SMTWriter h
           => AppExpr t tp
           -> SMTCollector t h (SMTExpr h tp)
appSMTExpr ae = do
  conn <- asks scConn
  let i = AppExpr ae
  liftIO $ updateProgramLoc conn (appExprLoc ae)
  case appExprApp ae of

    BaseEq _ x y ->
      do xe <- mkExpr x
         ye <- mkExpr y

         let xtp = smtExprType xe
         let ytp = smtExprType ye

         let checkArrayType z (FnArrayTypeMap{}) = do
               fail $ show $ text (smtWriterName conn) <+>
                 text "does not support checking equality for the array generated at"
                 <+> pretty (plSourceLoc (exprLoc z)) <> text ":" <$$>
                 indent 2 (pretty z)
             checkArrayType _ _ = return ()

         checkArrayType x xtp
         checkArrayType y ytp

         when (xtp /= ytp) $ do
           fail $ unwords ["Type representations are not equal:", show xtp, show ytp]

         freshBoundTerm BoolTypeMap $ asBase xe .== asBase ye

    BaseIte btp _ c x y -> do
      let errMsg typename =
           show
             $   text "we do not support if/then/else expressions at type"
             <+> text typename
             <+> text "with solver"
             <+> text (smtWriterName conn ++ ".")
      case typeMap conn btp of
        Left  (StringTypeUnsupported (Some si)) -> fail $ errMsg ("string " ++ show si)
        Left  ComplexTypeUnsupported -> fail $ errMsg "complex"
        Left  ArrayUnsupported       -> fail $ errMsg "array"
        Right FnArrayTypeMap{}       -> fail $ errMsg "function-backed array"
        Right tym ->
          do cb <- mkBaseExpr c
             xb <- mkBaseExpr x
             yb <- mkBaseExpr y
             freshBoundTerm tym $ ite cb xb yb

    SemiRingLe _sr x y -> do
      xb <- mkBaseExpr x
      yb <- mkBaseExpr y
      freshBoundTerm BoolTypeMap $ xb .<= yb

    RealIsInteger r -> do
      rb <- mkBaseExpr r
      freshBoundTerm BoolTypeMap $! realIsInteger rb

    BVTestBit n xe -> do
      x <- mkBaseExpr xe
      let this_bit = bvExtract (bvWidth xe) n 1 x
          one = bvTerm (knownNat :: NatRepr 1) 1
      freshBoundTerm BoolTypeMap $ this_bit .== one
    BVSlt xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm BoolTypeMap $ x `bvSLt` y
    BVUlt xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm BoolTypeMap $ x `bvULt` y

    IntDiv xe ye -> do
      case ye of
        SemiRingLiteral _ _ _ -> return ()
        _ -> checkNonlinearSupport i

      x <- mkBaseExpr xe
      y <- mkBaseExpr ye

      freshBoundTerm IntegerTypeMap (intDiv x y)

    IntMod xe ye -> do
      case ye of
        SemiRingLiteral _ _ _ -> return ()
        _ -> checkNonlinearSupport i

      x <- mkBaseExpr xe
      y <- mkBaseExpr ye

      freshBoundTerm IntegerTypeMap (intMod x y)

    IntAbs xe -> do
      x <- mkBaseExpr xe
      freshBoundTerm IntegerTypeMap (intAbs x)

    IntDivisible xe k -> do
      x <- mkBaseExpr xe
      freshBoundTerm BoolTypeMap (intDivisible x k)

    NatDiv xe ye -> do
      case ye of
        SemiRingLiteral _ _ _ -> return ()
        _ -> checkNonlinearSupport i

      x <- mkBaseExpr xe
      y <- mkBaseExpr ye

      freshBoundTerm NatTypeMap (intDiv x y)

    NatMod xe ye -> do
      case ye of
        SemiRingLiteral _ _ _ -> return ()
        _ -> checkNonlinearSupport i

      x <- mkBaseExpr xe
      y <- mkBaseExpr ye

      freshBoundTerm NatTypeMap (intMod x y)

    NotPred x -> freshBoundTerm BoolTypeMap . notExpr =<< mkBaseExpr x

    DisjPred xs ->
      let pol (x,Positive) = mkBaseExpr x
          pol (x,Negative) = notExpr <$> mkBaseExpr x
      in
      case BM.viewBoolMap xs of
        BM.BoolMapUnit ->
          return $ SMTExpr BoolTypeMap $ boolExpr False
        BM.BoolMapDualUnit ->
          return $ SMTExpr BoolTypeMap $ boolExpr True
        BM.BoolMapTerms (t:|[]) ->
          SMTExpr BoolTypeMap <$> pol t
        BM.BoolMapTerms (t:|ts) ->
          do cnj <- orAll <$> mapM pol (t:ts)
             freshBoundTerm BoolTypeMap cnj

    ConjPred xs ->
      let pol (x,Positive) = mkBaseExpr x
          pol (x,Negative) = notExpr <$> mkBaseExpr x
      in
      case BM.viewBoolMap xs of
        BM.BoolMapUnit ->
          return $ SMTExpr BoolTypeMap $ boolExpr True
        BM.BoolMapDualUnit ->
          return $ SMTExpr BoolTypeMap $ boolExpr False
        BM.BoolMapTerms (t:|[]) ->
          SMTExpr BoolTypeMap <$> pol t
        BM.BoolMapTerms (t:|ts) ->
          do cnj <- andAll <$> mapM pol (t:ts)
             freshBoundTerm BoolTypeMap cnj

    ------------------------------------------
    -- Real operations.

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          do pd' <- WSum.prodEvalM (\a b -> pure (bvMul a b)) mkBaseExpr pd
             maybe (return $ SMTExpr (BVTypeMap w) $ bvTerm w 1)
                   (freshBoundTerm (BVTypeMap w))
                   pd'

        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          do pd' <- WSum.prodEvalM (\a b -> pure (bvAnd a b)) mkBaseExpr pd
             maybe (return $ SMTExpr (BVTypeMap w) $ bvTerm w (maxUnsigned w))
                   (freshBoundTerm (BVTypeMap w))
                   pd'
        sr ->
          do checkNonlinearSupport i
             pd' <- WSum.prodEvalM (\a b -> pure (a * b)) mkBaseExpr pd
             maybe (return $ SMTExpr (semiRingTypeMap sr) $ integerTerm 1)
                   (freshBoundTerm (semiRingTypeMap sr))
                   pd'

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingNatRepr ->
          let smul c e
                | c ==  1   = (:[]) <$> mkBaseExpr e
                | otherwise = (:[]) . (integerTerm (toInteger c) *) <$> mkBaseExpr e
              cnst 0 = []
              cnst x = [integerTerm (toInteger x)]
          in
          freshBoundTerm NatTypeMap . sumExpr
            =<< WSum.evalM (\x y -> pure (x++y)) smul (pure . cnst) s

        SR.SemiRingIntegerRepr ->
          let smul c e
                | c ==  1   = (:[]) <$> mkBaseExpr e
                | c == -1   = (:[]) . negate <$> mkBaseExpr e
                | otherwise = (:[]) . (integerTerm c *) <$> mkBaseExpr e
              cnst 0 = []
              cnst x = [integerTerm x]
          in
          freshBoundTerm IntegerTypeMap . sumExpr
            =<< WSum.evalM (\x y -> pure (x++y)) smul (pure . cnst) s

        SR.SemiRingRealRepr ->
          let smul c e
                | c ==  1 = (:[]) <$> mkBaseExpr e
                | c == -1 = (:[]) . negate <$> mkBaseExpr e
                | otherwise = (:[]) . (rationalTerm c *) <$> mkBaseExpr e
              cnst 0 = []
              cnst x = [rationalTerm x]
          in
          freshBoundTerm RealTypeMap . sumExpr
            =<< WSum.evalM (\x y -> pure (x++y)) smul (pure . cnst) s

        SR.SemiRingBVRepr SR.BVArithRepr w ->
          let smul c e
                | c ==  1   = (:[]) <$> mkBaseExpr e
                | c == -1   = (:[]) . bvNeg <$> mkBaseExpr e
                | otherwise = (:[]) <$> (bvMul (bvTerm w c)) <$> mkBaseExpr e
              cnst 0 = []
              cnst x = [bvTerm w x]
           in
           freshBoundTerm (BVTypeMap w) . bvSumExpr w
             =<< WSum.evalM (\x y -> pure (x++y)) smul (pure . cnst) s

        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          let smul c e
                | c == maxUnsigned w = (:[]) <$> mkBaseExpr e
                | otherwise          = (:[]) <$> (bvAnd (bvTerm w c)) <$> mkBaseExpr e
              cnst 0 = []
              cnst x = [bvTerm w x]

              xorsum [] = bvTerm w 0
              xorsum xs = foldr1 bvXor xs
           in
           freshBoundTerm (BVTypeMap w) . xorsum
             =<< WSum.evalM (\x y -> pure (x++y)) smul (pure . cnst) s

    RealDiv xe ye -> do
      x <- mkBaseExpr xe
      case ye of
        SemiRingLiteral SR.SemiRingRealRepr r _ -> do
          freshBoundTerm RealTypeMap $ x * rationalTerm (recip r)
        _ -> do
          checkNonlinearSupport i
          y <- mkBaseExpr ye
          r <- freshConstant "real divison" RealTypeMap
          addSideCondition "real division" $ (y * asBase r) .== x .|| y .== 0
          return r

    RealSqrt xe -> do
      checkNonlinearSupport i

      x <- mkBaseExpr xe
      nm <- freshConstant "real sqrt" RealTypeMap
      let v = asBase nm
      -- assert v*v = x | x < 0
      addSideCondition "real sqrt" $ v * v .== x .|| x .< 0
      -- assert v >= 0
      addSideCondition "real sqrt" $ v .>= 0
      -- Return variable
      return nm
    Pi -> do
      unsupportedTerm i
    RealSin xe -> do
      checkComputableSupport i
      x <- mkBaseExpr xe
      freshBoundTerm RealTypeMap $ realSin x
    RealCos xe -> do
      checkComputableSupport i
      x <- mkBaseExpr xe
      freshBoundTerm RealTypeMap $ realCos x
    RealATan2 xe ye -> do
      checkComputableSupport i
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm RealTypeMap $ realATan2 x y
    RealSinh xe -> do
      checkComputableSupport i
      x <- mkBaseExpr xe
      freshBoundTerm RealTypeMap $ realSinh x
    RealCosh xe -> do
      checkComputableSupport i
      x <- mkBaseExpr xe
      freshBoundTerm RealTypeMap $ realCosh x
    RealExp xe -> do
      checkComputableSupport i
      x <- mkBaseExpr xe
      freshBoundTerm RealTypeMap $ realExp x
    RealLog xe -> do
      checkComputableSupport i
      x <- mkBaseExpr xe
      freshBoundTerm RealTypeMap $ realLog x

    ------------------------------------------
    -- Bitvector operations

    BVUnaryTerm t -> do
      let w = UnaryBV.width t
      let entries = UnaryBV.unsignedRanges t

      nm <- freshConstant "unary term" (BVTypeMap w)
      let nm_s = asBase nm
      forM_ entries $ \(pr,l,u) -> do
        -- Add assertion that for all values v in l,u, the predicate
        -- q is equivalent to v being less than or equal to the result
        -- of this term (denoted by nm)
        q <- mkBaseExpr pr
        addSideCondition "unary term" $ q .== nm_s `bvULe` (bvTerm w l)
        addSideCondition "unary term" $ q .== nm_s `bvULe` (bvTerm w u)

      case entries of
        (_, l, _):_ | l > 0 -> do
          addSideCondition "unary term" $ bvTerm w l `bvULe` nm_s
        _ ->
          return ()
      return nm

    BVOrBits pd ->
      case WSum.prodRepr pd of
        SR.SemiRingBVRepr _ w ->
          do pd' <- WSum.prodEvalM (\a b -> pure (bvOr a b)) mkBaseExpr pd
             maybe (return $ SMTExpr (BVTypeMap w) $ bvTerm w 0)
                   (freshBoundTerm (BVTypeMap w))
                   pd'

    BVConcat w xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm (BVTypeMap w) $ bvConcat x y

    BVSelect idx n xe -> do
      x <- mkBaseExpr xe
      freshBoundTerm (BVTypeMap n) $ bvExtract (bvWidth xe) (natValue idx) (natValue n) x

    BVUdiv w xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm (BVTypeMap w) $ bvUDiv x y

    BVUrem w xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm (BVTypeMap w) $ bvURem x y

    BVSdiv w xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm (BVTypeMap w) $ bvSDiv x y

    BVSrem w xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm (BVTypeMap w) $ bvSRem x y

    BVShl w xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm (BVTypeMap w) $ bvShl x y

    BVLshr w xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm (BVTypeMap w) $ bvLshr x y

    BVAshr w xe ye -> do
      x <- mkBaseExpr xe
      y <- mkBaseExpr ye
      freshBoundTerm (BVTypeMap w) $ bvAshr x y

    BVRol w xe ye -> do
      x  <- mkBaseExpr xe
      y  <- mkBaseExpr ye

      let w' = bvTerm w (intValue w)
      y' <- asBase <$> (freshBoundTerm (BVTypeMap w) $ bvURem y w')

      let lo = bvLshr x (bvSub w' y')
      let hi = bvShl x y'

      freshBoundTerm (BVTypeMap w) $ bvXor hi lo

    BVRor w xe ye -> do
      x  <- mkBaseExpr xe
      y  <- mkBaseExpr ye

      let w' = bvTerm w (intValue w)
      y' <- asBase <$> (freshBoundTerm (BVTypeMap w) $ bvURem y w')

      let lo = bvLshr x y'
      let hi = bvShl x (bvSub w' y')

      freshBoundTerm (BVTypeMap w) $ bvXor hi lo

    BVZext w' xe -> do
      let w = bvWidth xe
      x <- mkBaseExpr xe
      let n = intValue w' - intValue w
      case someNat n of
        Just (Some w2) | Just LeqProof <- isPosNat w' -> do
          let zeros = bvTerm w2 0
          freshBoundTerm (BVTypeMap w') $ bvConcat zeros x
        _ -> fail "invalid zero extension"

    BVSext w' xe -> do
      let w = bvWidth xe
      x <- mkBaseExpr xe
      let n = intValue w' - intValue w
      case someNat n of
        Just (Some w2) | Just LeqProof <- isPosNat w' -> do
          let zeros = bvTerm w2 0
          let ones  = bvTerm w2 (maxUnsigned w2)
          let sgn = bvTestBit w (natValue w - 1) x
          freshBoundTerm (BVTypeMap w') $ bvConcat (ite sgn ones zeros) x
        _ -> fail "invalid sign extension"

    BVFill w xe ->
      do x <- mkBaseExpr xe
         let zeros = bvTerm w 0
         let ones  = bvTerm w (maxUnsigned w)
         freshBoundTerm (BVTypeMap w) $ ite x ones zeros

    BVPopcount w xe ->
      do x <- mkBaseExpr xe
         let zs = [ ite (bvTestBit w idx x) (bvTerm w 1) (bvTerm w 0)
                  | idx <- [ 0 .. natValue w - 1 ]
                  ]
         freshBoundTerm (BVTypeMap w) $! bvSumExpr w zs

    BVCountLeadingZeros w xe ->
      do x <- mkBaseExpr xe
         freshBoundTerm (BVTypeMap w) $! go 0 x
     where
     go !idx x
       | idx < natValue w = ite (bvTestBit w (natValue w - idx - 1) x) (bvTerm w (toInteger idx)) (go (idx+1) x)
       | otherwise = bvTerm w (intValue w)

    BVCountTrailingZeros w xe ->
      do x <- mkBaseExpr xe
         freshBoundTerm (BVTypeMap w) $! go 0 x
     where
     go !idx x
       | idx < natValue w = ite (bvTestBit w idx x) (bvTerm w (toInteger idx)) (go (idx+1) x)
       | otherwise = bvTerm w (intValue w)

    ------------------------------------------
    -- String operations

    StringLength xe -> do
      case stringInfo xe of
        Char8Repr -> do
          checkStringSupport i
          x <- mkBaseExpr xe
          freshBoundTerm NatTypeMap $ stringLength @h x
        si -> fail ("Unsupported symbolic string length operation " ++  show si)

    StringIndexOf xe ye ke ->
      case stringInfo xe of
        Char8Repr -> do
          checkStringSupport i
          x <- mkBaseExpr xe
          y <- mkBaseExpr ye
          k <- mkBaseExpr ke
          freshBoundTerm IntegerTypeMap $ stringIndexOf @h x y k
        si -> fail ("Unsupported symbolic string index-of operation " ++  show si)

    StringSubstring _ xe offe lene ->
      case stringInfo xe of
        Char8Repr -> do
          checkStringSupport i
          x <- mkBaseExpr xe
          off <- mkBaseExpr offe
          len <- mkBaseExpr lene
          freshBoundTerm Char8TypeMap $ stringSubstring @h x off len
        si -> fail ("Unsupported symbolic string substring operation " ++  show si)

    StringContains xe ye ->
      case stringInfo xe of
        Char8Repr -> do
          checkStringSupport i
          x <- mkBaseExpr xe
          y <- mkBaseExpr ye
          freshBoundTerm BoolTypeMap $ stringContains @h x y
        si -> fail ("Unsupported symbolic string contains operation " ++  show si)

    StringIsPrefixOf xe ye ->
      case stringInfo xe of
        Char8Repr -> do
          checkStringSupport i
          x <- mkBaseExpr xe
          y <- mkBaseExpr ye
          freshBoundTerm BoolTypeMap $ stringIsPrefixOf @h x y
        si -> fail ("Unsupported symbolic string is-prefix-of operation " ++  show si)

    StringIsSuffixOf xe ye ->
      case stringInfo xe of
        Char8Repr -> do
          checkStringSupport i
          x <- mkBaseExpr xe
          y <- mkBaseExpr ye
          freshBoundTerm BoolTypeMap $ stringIsSuffixOf @h x y
        si -> fail ("Unsupported symbolic string is-suffix-of operation " ++  show si)

    StringAppend si xes ->
      case si of
        Char8Repr -> do
          checkStringSupport i
          xs <- mapM (either (return . stringTerm @h . fromChar8Lit) mkBaseExpr) $ SSeq.toList xes
          freshBoundTerm Char8TypeMap $ stringAppend @h xs

        _ -> fail ("Unsupported symbolic string append operation " ++  show si)

    ------------------------------------------
    -- Floating-point operations
    FloatPZero fpp ->
      freshBoundTerm (FloatTypeMap fpp) $ floatPZero fpp
    FloatNZero fpp ->
      freshBoundTerm (FloatTypeMap fpp) $ floatNZero fpp
    FloatNaN fpp ->
      freshBoundTerm (FloatTypeMap fpp) $ floatNaN fpp
    FloatPInf fpp ->
      freshBoundTerm (FloatTypeMap fpp) $ floatPInf fpp
    FloatNInf fpp ->
      freshBoundTerm (FloatTypeMap fpp) $ floatNInf fpp
    FloatNeg fpp x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp) $ floatNeg xe
    FloatAbs fpp x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp) $ floatAbs xe
    FloatSqrt fpp r x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp) $ floatSqrt r xe
    FloatAdd fpp r x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm (FloatTypeMap fpp) $ floatAdd r xe ye
    FloatSub fpp r x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm (FloatTypeMap fpp) $ floatSub r xe ye
    FloatMul fpp r x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm (FloatTypeMap fpp) $ floatMul r xe ye
    FloatDiv fpp r x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm (FloatTypeMap fpp) $ floatDiv r xe ye
    FloatRem fpp x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm (FloatTypeMap fpp) $ floatRem xe ye
    FloatMin fpp x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm (FloatTypeMap fpp) $ floatMin xe ye
    FloatMax fpp x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm (FloatTypeMap fpp) $ floatMax xe ye
    FloatFMA fpp r x y z -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      ze <- mkBaseExpr z
      freshBoundTerm (FloatTypeMap fpp) $ floatFMA r xe ye ze
    FloatFpEq x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm BoolTypeMap $ floatFpEq xe ye
    FloatFpNe x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm BoolTypeMap $
        notExpr (floatEq xe ye)
        .&& notExpr (floatIsNaN xe)
        .&& notExpr (floatIsNaN ye)
    FloatLe x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm BoolTypeMap $ floatLe xe ye
    FloatLt x y -> do
      xe <- mkBaseExpr x
      ye <- mkBaseExpr y
      freshBoundTerm BoolTypeMap $ floatLt xe ye
    FloatIsNaN x -> do
      xe <- mkBaseExpr x
      freshBoundTerm BoolTypeMap $ floatIsNaN xe
    FloatIsInf x -> do
      xe <- mkBaseExpr x
      freshBoundTerm BoolTypeMap $ floatIsInf xe
    FloatIsZero x -> do
      xe <- mkBaseExpr x
      freshBoundTerm BoolTypeMap $ floatIsZero xe
    FloatIsPos x -> do
      xe <- mkBaseExpr x
      freshBoundTerm BoolTypeMap $ floatIsPos xe
    FloatIsNeg x -> do
      xe <- mkBaseExpr x
      freshBoundTerm BoolTypeMap $ floatIsNeg xe
    FloatIsSubnorm x -> do
      xe <- mkBaseExpr x
      freshBoundTerm BoolTypeMap $ floatIsSubnorm xe
    FloatIsNorm x -> do
      xe <- mkBaseExpr x
      freshBoundTerm BoolTypeMap $ floatIsNorm xe
    FloatCast fpp r x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp) $
        floatCast fpp r xe
    FloatRound fpp r x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp)$ floatRound r xe
    FloatToBinary fpp@(FloatingPointPrecisionRepr eb sb) x -> do
      xe <- mkBaseExpr x
      val <- asBase <$> (freshConstant "float_binary" $ BVTypeMap $ addNat eb sb)
      -- (assert (= ((_ to_fp eb sb) val) xe))
      addSideCondition "float_binary" $
        floatFromBinary fpp val .== xe
      -- qnan: 0b0 0b1..1 0b10..0
      let qnan = bvTerm (addNat eb sb) $ shiftL
                  (2 ^ (natValue eb + 1) - 1)
                  (fromIntegral (natValue sb - 2))
      -- return (ite (fp.isNaN xe) qnan val)
      freshBoundTerm (BVTypeMap $ addNat eb sb) $ ite (floatIsNaN xe) qnan val
    FloatFromBinary fpp x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp) $
        floatFromBinary fpp xe
    BVToFloat fpp r x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp) $
        bvToFloat fpp r xe
    SBVToFloat fpp r x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp) $
        sbvToFloat fpp r xe
    RealToFloat fpp r x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (FloatTypeMap fpp) $
        realToFloat fpp r xe
    FloatToBV w r x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (BVTypeMap w) $ floatToBV (natValue w) r xe
    FloatToSBV w r x -> do
      xe <- mkBaseExpr x
      freshBoundTerm (BVTypeMap w) $ floatToSBV (natValue w) r xe
    FloatToReal x -> do
      xe <- mkBaseExpr x
      freshBoundTerm RealTypeMap $ floatToReal xe

    ------------------------------------------------------------------------
    -- Array Operations

    ArrayMap _ _ elts def -> do
      base_array <- mkExpr def
      elt_exprs <- traverse mkBaseExpr (Hash.hashedMap elts)
      let array_type = smtExprType base_array
      case array_type of
        PrimArrayTypeMap{} -> do
          let set_at_index :: Term h
                           -> Ctx.Assignment IndexLit ctx
                           -> Term h
                           -> Term h
              set_at_index ma idx elt =
                arrayUpdate @h ma (mkIndexLitTerms idx) elt
          freshBoundTerm array_type $
            Map.foldlWithKey set_at_index (asBase base_array) elt_exprs

        FnArrayTypeMap idx_types resType -> do
          case smtFnUpdate of
            Just updateFn -> do

              let set_at_index :: Term h
                               -> Ctx.Assignment IndexLit ctx
                               -> Term h
                               -> Term h
                  set_at_index ma idx elt =
                    updateFn ma (toListFC mkIndexLitTerm idx) elt
              freshBoundTerm array_type $
                Map.foldlWithKey set_at_index (asBase base_array) elt_exprs
            Nothing -> do
              -- Supporting arrays as functons requires that we can create
              -- function definitions.
              when (not (supportFunctionDefs conn)) $ do
                fail $ show $ text (smtWriterName conn) <+>
                  text "does not support arrays as functions."
              -- Create names for index variables.
              args <- liftIO $ createTypeMapArgsForArray conn idx_types
              -- Get list of terms for arguments.
              let idx_terms = fromText . fst <$> args
              -- Return value at index in base_array.
              let base_lookup = smtFnApp (asBase base_array) idx_terms
              -- Return if-then-else structure for next elements.
              let set_at_index prev_value idx_lits elt =
                    let update_idx = toListFC mkIndexLitTerm idx_lits
                        cond = andAll (zipWith (.==) update_idx idx_terms)
                     in ite cond elt prev_value
              -- Get final expression for definition.
              let expr = Map.foldlWithKey set_at_index base_lookup elt_exprs
              -- Add command
              SMTName array_type <$> freshBoundFn args resType expr

    ConstantArray idxRepr _bRepr ve -> do
      v <- mkExpr ve
      let value_type = smtExprType v
          feat = supportedFeatures conn
          mkArray = if feat `hasProblemFeature` useSymbolicArrays
                    then PrimArrayTypeMap
                    else FnArrayTypeMap
      idx_types <- liftIO $
        traverseFC (evalFirstClassTypeRepr conn (eltSource i)) idxRepr
      case arrayConstant @h of
        Just constFn
          | otherwise -> do
            let idx_smt_types = toListFC Some idx_types
            let tp = mkArray idx_types value_type
            freshBoundTerm tp $!
              constFn idx_smt_types (Some value_type) (asBase v)
        Nothing -> do
          when (not (supportFunctionDefs conn)) $ do
            fail $ show $ text (smtWriterName conn) <+>
              text "cannot encode constant arrays."
          -- Constant functions use unnamed variables.
          let array_type = mkArray idx_types value_type
          -- Create names for index variables.
          args <- liftIO $ createTypeMapArgsForArray conn idx_types
          SMTName array_type <$> freshBoundFn args value_type (asBase v)

    SelectArray _bRepr a idx -> do
      aexpr <- mkExpr a
      idxl <- mkIndicesTerms idx
      freshBoundTerm' $ smt_array_select aexpr idxl

    UpdateArray _bRepr _ a_elt idx ve -> do
      a <- mkExpr a_elt
      updated_idx <- mkIndicesTerms idx
      value <- asBase <$> mkExpr ve
      let array_type = smtExprType a
      case array_type of
        PrimArrayTypeMap _ _ -> do
            freshBoundTerm array_type $
              arrayUpdate @h (asBase a) updated_idx value
        FnArrayTypeMap idxTypes resType  -> do
          case smtFnUpdate of
            Just updateFn -> do
              freshBoundTerm array_type $ updateFn (asBase a) updated_idx value
            Nothing -> do
              -- Return value at index in base_array.
              args <- liftIO $ createTypeMapArgsForArray conn idxTypes

              let idx_terms = fromText . fst <$> args
              let base_array_value = smtFnApp (asBase a) idx_terms
              let cond = andAll (zipWith (.==) updated_idx idx_terms)
              let expr = ite cond value base_array_value
              SMTName array_type <$> freshBoundFn args resType expr

    ------------------------------------------------------------------------
    -- Conversions.

    NatToInteger xe -> do
      x <- mkExpr xe
      return $ case x of
                 SMTName _ n -> SMTName IntegerTypeMap n
                 SMTExpr _ e -> SMTExpr IntegerTypeMap e
    IntegerToNat x -> do
      v <- mkExpr x
      -- We don't add a side condition here as 'IntegerToNat' is undefined
      -- when 'x' is negative.
      -- addSideCondition "integer to nat" (asBase v .>= 0)
      return $ case v of
                 SMTName _ n -> SMTName NatTypeMap n
                 SMTExpr _ e -> SMTExpr NatTypeMap e

    IntegerToReal xe -> do
      x <- mkExpr xe
      return $ SMTExpr RealTypeMap (termIntegerToReal (asBase x))
    RealToInteger xe -> do
      checkIntegerSupport i
      x <- mkBaseExpr xe
      return $ SMTExpr IntegerTypeMap (termRealToInteger x)

    RoundReal xe -> do
      checkIntegerSupport i
      x <- mkBaseExpr xe
      nm <- freshConstant "round" IntegerTypeMap
      let r = termIntegerToReal (asBase nm)
      -- Round always rounds away from zero, so we
      -- first split "r = round(x)" into two cases
      -- depending on if "x" is non-negative.
      let posExpr = (2*x - 1 .<  2*r) .&& (2*r .<= 2*x + 1)
      let negExpr = (2*x - 1 .<= 2*r) .&& (2*r .<  2*x + 1)
      -- Add formula
      addSideCondition "round" $ x .<  0 .|| posExpr
      addSideCondition "round" $ x .>= 0 .|| negExpr
      return nm

    FloorReal xe -> do
      checkIntegerSupport i
      x <- mkBaseExpr xe
      nm <- freshConstant "floor" IntegerTypeMap
      let floor_r = termIntegerToReal (asBase nm)
      addSideCondition "floor" $ (floor_r .<= x) .&& (x .< floor_r + 1)
      return nm

    CeilReal xe -> do
      checkIntegerSupport i
      x <- asBase <$> mkExpr xe
      nm <- freshConstant "ceiling" IntegerTypeMap
      let r = termIntegerToReal (asBase nm)
      addSideCondition "ceiling" $ (x .<= r) .&& (r .< x + 1)
      return nm

    BVToNat xe -> do
      checkLinearSupport i
      x <- mkExpr xe
      freshBoundTerm NatTypeMap $ bvIntTerm (bvWidth xe) (asBase x)

    BVToInteger xe -> do
      checkLinearSupport i
      x <- mkExpr xe
      freshBoundTerm IntegerTypeMap $ bvIntTerm (bvWidth xe) (asBase x)

    SBVToInteger xe -> do
      checkLinearSupport i
      x <- mkExpr xe
      freshBoundTerm IntegerTypeMap $ sbvIntTerm (bvWidth xe) (asBase x)

    IntegerToBV xe w -> do
      checkLinearSupport i

      x <- mkExpr xe
      let xb = asBase x

      res <- freshConstant "integerToBV" (BVTypeMap w)
      bvint <- freshBoundTerm IntegerTypeMap $ bvIntTerm w (asBase res)

      addSideCondition "integerToBV" $
         (intDivisible (xb - (asBase bvint)) (2^natValue w))
      return res

    Cplx c -> do
      (rl :+ img) <- traverse mkExpr c

      feat <- asks (supportedFeatures . scConn)
      case () of
        _ | feat `hasProblemFeature` useStructs -> do
            let tp = ComplexToStructTypeMap
            let tm = structCtor @h (Ctx.Empty Ctx.:> RealTypeMap Ctx.:> RealTypeMap) [asBase rl, asBase img]
            freshBoundTerm tp tm

          | feat `hasProblemFeature` useSymbolicArrays -> do
            let tp = ComplexToArrayTypeMap
            let r' = asBase rl
            let i' = asBase img
            ra <-
              case arrayConstant @h of
                Just constFn  ->
                  return (constFn [Some BoolTypeMap] (Some RealTypeMap) r')
                Nothing -> do
                  a <- asBase <$> freshConstant "complex lit" tp
                  return $! arrayUpdate @h a [boolExpr False] r'
            freshBoundTerm tp $! arrayUpdate @h ra [boolExpr True] i'

          | otherwise ->
            theoryUnsupported conn "complex literals" i

    RealPart e -> do
      c <- mkExpr e
      case smtExprType c of
        ComplexToStructTypeMap ->
          do let prj = structComplexRealPart @h (asBase c)
             freshBoundTerm RealTypeMap prj
        ComplexToArrayTypeMap ->
          freshBoundTerm RealTypeMap $ arrayComplexRealPart @h (asBase c)
    ImagPart e -> do
      c <- mkExpr e
      case smtExprType c of
        ComplexToStructTypeMap ->
          do let prj = structComplexImagPart @h (asBase c)
             freshBoundTerm RealTypeMap prj
        ComplexToArrayTypeMap ->
          freshBoundTerm RealTypeMap $ arrayComplexImagPart @h (asBase c)

    --------------------------------------------------------------------
    -- Structures

    StructCtor _ vals -> do
      -- Make sure a struct with the given number of elements has been declared.
      exprs <- traverseFC mkExpr vals
      let fld_types = fmapFC smtExprType exprs

      liftIO $ declareStructDatatype conn fld_types
      let tm = structCtor @h fld_types (toListFC asBase exprs)
      freshBoundTerm (StructTypeMap fld_types) tm

    StructField s idx _tp -> do
      expr <- mkExpr s
      case smtExprType expr of
       StructTypeMap flds -> do
         let tp = flds Ctx.! idx
         let tm = structProj @h flds idx (asBase expr)
         freshBoundTerm tp tm

defineFn :: SMTWriter h
         => WriterConn t h
         -> Text
         -> Ctx.Assignment (ExprBoundVar t) a
         -> Expr t r
         -> Ctx.Assignment TypeMap a
         -> IO (TypeMap r)
defineFn conn nm arg_vars return_value arg_types =
  -- Define the SMT function
  defineSMTFunction conn nm $ \(FreshVarFn freshVar) -> do
    -- Create SMT expressions and bind them to vars
    Ctx.forIndexM (Ctx.size arg_vars) $ \i -> do
      let v = arg_vars Ctx.! i
      let smtType = arg_types Ctx.! i
      checkVarTypeSupport v
      x <- liftIO $ freshVar smtType
      bindVar v x
    -- Evaluate return value
    mkExpr return_value

-- | Create a SMT symbolic function from the ExprSymFn.
--
-- Returns the return type of the function.
--
-- This is only called by 'getSMTSymFn'.
mkSMTSymFn :: SMTWriter h
           => WriterConn t h
           -> Text
           -> ExprSymFn t args ret
           -> Ctx.Assignment TypeMap args
           -> IO (TypeMap ret)
mkSMTSymFn conn nm f arg_types =
  case symFnInfo f of
    UninterpFnInfo _ return_type -> do
      let fnm = symFnName f
      let l = symFnLoc f
      smt_ret <- evalFirstClassTypeRepr conn (fnSource fnm l) return_type
      traverseFC_ (declareTypes conn) arg_types
      declareTypes conn smt_ret
      addCommand conn $
        declareCommand conn nm arg_types smt_ret
      return $! smt_ret
    DefinedFnInfo arg_vars return_value _ -> do
      defineFn conn nm arg_vars return_value arg_types
    MatlabSolverFnInfo _ arg_vars return_value -> do
      defineFn conn nm arg_vars return_value arg_types

-- | Generate a SMTLIB function for a ExprBuilder function.
--
-- Since SimpleBuilder different simple builder values with the same type may
-- have different SMTLIB types (particularly arrays), getSMTSymFn requires the
-- argument types to call the function with.  This is enforced to be compatible
-- with the argument types expected by the simplebuilder.
--
-- This function caches the result, and we currently generate the function based
-- on the argument types provided the first time getSMTSymFn is called with a
-- particular simple builder function.  In subsequent calls, we validate that
-- the same argument types are provided.  In principal, a function could be
-- called with one type of arguments, and then be called with a different type
-- and this check would fail.  However, due to limitations in the solvers we
-- expect to support, this should never happen as the only time these may differ
-- when arrays are used and one array is encoded using the theory of arrays, while
-- the other uses a defined function.  However, SMTLIB2 does not allow functions
-- to be passed to other functions; yices does, but always encodes arrays as functions.
--
-- Returns the name of the function and the type of the result.
getSMTSymFn :: SMTWriter h
            => WriterConn t h
            -> ExprSymFn t args ret -- ^ Function to
            -> Ctx.Assignment TypeMap args
            -> IO (Text, TypeMap ret)
getSMTSymFn conn fn arg_types = do
  let n = symFnId fn
  cacheLookupFn conn n >>= \case
    Just (SMTSymFn nm param_types ret) -> do
      when (arg_types /= param_types) $ do
        fail $ "Illegal arguments to function " ++ Text.unpack nm ++ ".\n"
              ++ "\tExpected arguments: " ++ show param_types ++"\n"
              ++ "\tActual arguments: " ++ show arg_types
      return (nm, ret)
    Nothing -> do
      -- Check argument types can be passed to a function.
      checkArgumentTypes conn arg_types
      -- Generate name.
      nm <- getSymbolName conn (FnSymbolBinding fn)
      ret_type <- mkSMTSymFn conn nm fn arg_types
      cacheValueFn conn n DeleteNever $! SMTSymFn nm arg_types ret_type
      return (nm, ret_type)

------------------------------------------------------------------------
-- Writer high-level interface.

-- | Write a expression to SMT
mkSMTTerm :: SMTWriter h => WriterConn t h -> Expr t tp -> IO (Term h)
mkSMTTerm conn p = runOnLiveConnection conn $ mkBaseExpr p

-- | Write a logical expression.
mkFormula :: SMTWriter h => WriterConn t h -> BoolExpr t -> IO (Term h)
mkFormula = mkSMTTerm

mkAtomicFormula :: SMTWriter h => WriterConn t h -> BoolExpr t -> IO Text
mkAtomicFormula conn p = runOnLiveConnection conn $
  mkExpr p >>= \case
    SMTName _ nm  -> return nm
    SMTExpr ty tm -> freshBoundFn [] ty tm

-- | Write assume formula predicates for asserting predicate holds.
assume :: SMTWriter h => WriterConn t h -> BoolExpr t -> IO ()
assume c p = do
  forM_ (asConjunction p) $ \(v,pl) -> do
    f <- mkFormula c v
    updateProgramLoc c (exprLoc v)
    case pl of
      BM.Positive -> assumeFormula c f
      BM.Negative -> assumeFormula c (notExpr f)

type SMTEvalBVArrayFn h w v =
    (1 <= w,
     1 <= v)
  => NatRepr w
  -> NatRepr v
  -> Term h
  -> IO (Maybe (GroundArray (Ctx.SingleCtx (BaseBVType w)) (BaseBVType v)))

newtype SMTEvalBVArrayWrapper h =
  SMTEvalBVArrayWrapper { unEvalBVArrayWrapper :: forall w v. SMTEvalBVArrayFn h w v }

data SMTEvalFunctions h
   = SMTEvalFunctions { smtEvalBool :: Term h -> IO Bool
                        -- ^ Given a SMT term for a Boolean value, this should
                        -- whether the term is assigned true or false.
                      , smtEvalBV   :: Int -> Term h -> IO Integer
                        -- ^ Given a bitwidth, and a SMT term for a bitvector
                        -- with that bitwidth, this should return an unsigned
                        -- integer with the value of that bitvector.
                      , smtEvalReal :: Term h -> IO Rational
                        -- ^ Given a SMT term for real value, this should
                        -- return a rational value for that term.
                      , smtEvalFloat :: Term h -> IO Integer
                        -- ^ Given a SMT term for a floating-point value,
                        -- this returns an unsigned integer with the bits
                        -- of the IEEE-754 representation.
                      , smtEvalBvArray :: Maybe (SMTEvalBVArrayWrapper h)
                        -- ^ If 'Just', a function to read arrays whose domain
                        -- and codomain are both bitvectors. If 'Nothing',
                        -- signifies that we should fall back to index-selection
                        -- representation of arrays.
                      , smtEvalString :: Term h -> IO ByteString
                        -- ^ Given a SMT term representing as sequence of bytes,
                        -- return the value as a bytestring.
                      }

-- | Used when we need two way communication with the solver.
class SMTWriter h => SMTReadWriter h where
  -- | Get functions for parsing values out of the solver.
  smtEvalFuns ::
    WriterConn t h -> Streams.InputStream Text -> SMTEvalFunctions h

  -- | Parse a set result from the solver's response.
  smtSatResult :: f h -> Streams.InputStream Text -> IO (SatResult () ())

  -- | Parse a list of names of assumptions that form an unsatisfiable core.
  --   These correspond to previously-named assertions.
  smtUnsatCoreResult :: f h -> Streams.InputStream Text -> IO [Text]

  -- | Parse a list of names of assumptions that form an unsatisfiable core.
  --   The boolean indicates the polarity of the atom: true for an ordinary
  --   atom, false for a negated atom.
  smtUnsatAssumptionsResult :: f h -> Streams.InputStream Text -> IO [(Bool,Text)]


-- | Return the terms associated with the given ground index variables.
smtIndicesTerms :: forall v idx
                .  SupportTermOps v
                => Ctx.Assignment TypeMap idx
                -> Ctx.Assignment GroundValueWrapper  idx
                -> [v]
smtIndicesTerms tps vals = Ctx.forIndexRange 0 sz f []
  where sz = Ctx.size tps
        f :: Ctx.Index idx tp -> [v] -> [v]
        f i l = (r:l)
         where GVW v = vals Ctx.! i
               r = case tps Ctx.! i of
                      NatTypeMap -> rationalTerm (fromIntegral v)
                      BVTypeMap w -> bvTerm w v
                      _ -> error "Do not yet support other index types."

getSolverVal :: forall h t tp
             .  SMTWriter h
             => WriterConn t h
             -> SMTEvalFunctions h
             -> TypeMap tp
             -> Term h
             -> IO (GroundValue tp)
getSolverVal _ smtFns BoolTypeMap   tm = smtEvalBool smtFns tm
getSolverVal _ smtFns (BVTypeMap w) tm = smtEvalBV smtFns (widthVal w) tm
getSolverVal _ smtFns RealTypeMap   tm = smtEvalReal smtFns tm
getSolverVal _ smtFns (FloatTypeMap _) tm = smtEvalFloat smtFns tm
getSolverVal _ smtFns Char8TypeMap tm = Char8Literal <$> smtEvalString smtFns tm
getSolverVal _ smtFns NatTypeMap    tm = do
  r <- smtEvalReal smtFns tm
  when (denominator r /= 1 && numerator r < 0) $ do
    fail $ "Expected natural number from solver."
  return (fromInteger (numerator r))
getSolverVal _ smtFns IntegerTypeMap tm = do
  r <- smtEvalReal smtFns tm
  when (denominator r /= 1) $ fail "Expected integer value."
  return (numerator r)
getSolverVal _ smtFns ComplexToStructTypeMap tm =
  (:+) <$> smtEvalReal smtFns (structComplexRealPart @h tm)
       <*> smtEvalReal smtFns (structComplexImagPart @h tm)
getSolverVal _ smtFns ComplexToArrayTypeMap tm =
  (:+) <$> smtEvalReal smtFns (arrayComplexRealPart @h tm)
       <*> smtEvalReal smtFns (arrayComplexImagPart @h tm)
getSolverVal conn smtFns (PrimArrayTypeMap idx_types eltTp) tm
  | Just (SMTEvalBVArrayWrapper evalBVArray) <- smtEvalBvArray smtFns
  , Ctx.Empty Ctx.:> (BVTypeMap w) <- idx_types
  , BVTypeMap v <- eltTp =
      fromMaybe byIndex <$> evalBVArray w v tm
  | otherwise = return byIndex
  where byIndex = ArrayMapping $ \i -> do
          let res = arraySelect @h tm (smtIndicesTerms idx_types i)
          getSolverVal conn smtFns eltTp res
getSolverVal conn smtFns (FnArrayTypeMap idx_types eltTp) tm = return $ ArrayMapping $ \i -> do
  let term = smtFnApp tm (smtIndicesTerms idx_types i)
  getSolverVal conn smtFns eltTp term
getSolverVal conn smtFns (StructTypeMap flds0) tm =
          Ctx.traverseWithIndex (f flds0) flds0
        where f :: Ctx.Assignment TypeMap ctx
                -> Ctx.Index ctx utp
                -> TypeMap utp
                -> IO (GroundValueWrapper utp)
              f flds i tp = GVW <$> getSolverVal conn smtFns tp v
                where v = structProj @h flds i tm

-- | The function creates a function for evaluating elts to concrete values
-- given a connection to an SMT solver along with some functions for evaluating
-- different types of terms to concrete values.
smtExprGroundEvalFn :: forall t h
                     . SMTWriter h
                    => WriterConn t h
                       -- ^ Connection to SMT solver.
                    -> SMTEvalFunctions h
                    -> IO (GroundEvalFn t)
smtExprGroundEvalFn conn smtFns = do
  -- Get solver features
  groundCache <- newIdxCache

  let cachedEval :: Expr t tp -> IO (GroundValue tp)
      cachedEval e =
        case exprMaybeId e of
          Nothing -> evalGroundExpr cachedEval e
          Just e_id -> fmap unGVW $ idxCacheEval' groundCache e_id $ fmap GVW $ do
            -- See if we have bound the Expr e to a SMT expression.
            me <- cacheLookupExpr conn e_id
            case me of
              -- Otherwise, try the evalGroundExpr function to evaluate a ground element.
              Nothing -> evalGroundExpr cachedEval e

              -- If so, try asking the solver for the value of SMT expression.
              Just (SMTName tp nm) ->
                getSolverVal conn smtFns tp (fromText nm)

              Just (SMTExpr tp expr) ->
                runMaybeT (tryEvalGroundExpr cachedEval e) >>= \case
                  Just x  -> return x
                  -- If we cannot compute the value ourself, query the
                  -- value from the solver directly instead.
                  Nothing -> getSolverVal conn smtFns tp expr


  return $ GroundEvalFn cachedEval
