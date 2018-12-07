------------------------------------------------------------------------
-- |
-- Module           : What4.Protocol.SMTLib2
-- Description      : Interface for solvers that consume SMTLib2
-- Copyright        : (c) Galois, Inc 2014-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module defines operations for producing SMTLib2-compatible
-- queries useful for interfacing with solvers that accecpt SMTLib2 as
-- an input language.
------------------------------------------------------------------------
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module What4.Protocol.SMTLib2
  ( -- SMTLib special purpose exports
    Writer
  , SMTLib2Tweaks(..)
  , newWriter
  , writeCheckSat
  , writeExit
  , writeGetValue
  , runCheckSat
  , asSMT2Type
  , setOption
  , setProduceModels
    -- * Logic
  , SMT2.Logic(..)
  , SMT2.qf_bv
  , SMT2.allSupported
  , all_supported
  , setLogic
    -- * Type
  , SMT2.Sort(..)
  , SMT2.arraySort
  , structSort
    -- * Term
  , Term(..)
  , arrayConst
  , What4.Protocol.SMTLib2.arraySelect
  , arrayStore
    -- * Solvers and External interface
  , Session(..)
  , SMTLib2GenericSolver(..)
  , writeDefaultSMT2
  , startSolver
  , shutdownSolver
  , smtAckResult
  , SMTLib2Exception(..)
    -- * Re-exports
  , SMTWriter.WriterConn
  , SMTWriter.assume
  ) where

import           Control.Applicative
import           Control.Exception
import           Control.Monad.State.Strict
import           Data.Bits (bit, setBit, shiftL)
import           Data.Char (digitToInt)
import           Data.IORef
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Lazy
import qualified Data.Map.Strict as Map
import           Data.Monoid
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.Builder.Int as Builder
import           Numeric (readDec, readHex, readInt)
import qualified System.Exit as Exit
import qualified System.IO as IO
import qualified System.IO.Streams as Streams
import qualified System.IO.Streams.Attoparsec.Text as Streams
import qualified System.Process as Process

import           Prelude hiding (writeFile)

import           What4.BaseTypes
import qualified What4.Expr.Builder as B
import           What4.Expr.GroundEval
import qualified What4.Interface as I
import           What4.ProblemFeatures
import           What4.Protocol.Online
import           What4.Protocol.ReadDecimal
import           What4.Protocol.SExp
import           What4.Protocol.SMTLib2.Syntax (Term, term_app, un_app, bin_app)

import qualified What4.Protocol.SMTLib2.Syntax as SMT2 hiding (Term)
import qualified What4.Protocol.SMTWriter as SMTWriter
import           What4.Protocol.SMTWriter hiding (assume, Term)
import           What4.SatResult
import           What4.Utils.HandleReader
import           What4.Utils.Process
import           What4.Solver.Adapter

-- | Set the logic to all supported logics.
all_supported :: SMT2.Logic
all_supported = SMT2.allSupported
{-# DEPRECATED all_supported "Use allSupported" #-}

------------------------------------------------------------------------
-- Floating point

data SMTFloatPrecision =
  SMTFloatPrecision { smtFloatExponentBits :: !Integer
                      -- ^ Number of bits in exponent
                    , smtFloatSignificandBits :: !Integer
                      -- ^ Number of bits in the significand.
                    }
  deriving (Eq, Ord)

asSMTFloatPrecision :: FloatPrecisionRepr fpp -> SMTFloatPrecision
asSMTFloatPrecision (FloatingPointPrecisionRepr eb sb) =
  SMTFloatPrecision { smtFloatExponentBits = natValue eb
                    , smtFloatSignificandBits = natValue sb
                    }

mkFloatSymbol :: Builder -> SMTFloatPrecision -> Builder
mkFloatSymbol nm (SMTFloatPrecision eb sb) =
  "(_ "
    <> nm
    <> " "
    <> fromString (show eb)
    <> " "
    <> fromString (show sb)
    <> ")"

------------------------------------------------------------------------
-- SMTLib2Tweaks

-- | Select a valued from a nested array
nestedArrayUpdate :: Term
                  -> (Term, [Term])
                  -> Term
                  -> Term
nestedArrayUpdate a (h,[]) v  = SMT2.store a h v
nestedArrayUpdate a (h,i:l) v = SMT2.store a h sub_a'
  where sub_a' = nestedArrayUpdate (SMT2.select a h) (i,l) v

arrayConst :: SMT2.Sort -> SMT2.Sort -> Term -> Term
arrayConst = SMT2.arrayConst

arraySelect :: Term -> Term -> Term
arraySelect = SMT2.select

arrayStore :: Term -> Term -> Term -> Term
arrayStore = SMT2.store

-- | This class exists so that solvers supporting the SMTLib2 format can support
--   features that go slightly beyond the standard.
--
-- In particular, there is no standardized syntax for constant arrays (arrays
-- which map every index to the same value).  Solvers that support the theory of
-- arrays and have custom syntax for constant arrays should implement
-- `smtlib2arrayConstant`.  In addition, solvers may override the default
-- representation of complex numbers if necessary.  The default is to represent
-- complex numbers as "(Array Bool Real)" and to build instances by updating a
-- constant array.
class SMTLib2Tweaks a where
  smtlib2tweaks :: a

  -- | Return a representation of the type associated with a (multi-dimensional) symbolic
  -- array.
  --
  -- By default, we encode symbolic arrays using a nested representation.  If the solver,
  -- supports tuples/structs it may wish to change this.
  smtlib2arrayType :: [SMT2.Sort] -> SMT2.Sort -> SMT2.Sort
  smtlib2arrayType l r = foldr (\i v -> SMT2.arraySort i v) r l

  smtlib2arrayConstant :: Maybe ([SMT2.Sort] -> SMT2.Sort -> Term -> Term)
  smtlib2arrayConstant = Nothing

  smtlib2arraySelect :: Term -> [Term] -> Term
  smtlib2arraySelect a [] = a
  smtlib2arraySelect a (h:l) = smtlib2arraySelect @a (What4.Protocol.SMTLib2.arraySelect a h) l

  smtlib2arrayUpdate :: Term -> [Term] -> Term -> Term
  smtlib2arrayUpdate a i v =
    case i of
      [] -> error "arrayUpdate given empty list"
      i1:ir -> nestedArrayUpdate a (i1, ir) v

-- | A struct with the given fields.
--
-- This uses SMTLIB2 datatypes and are not primitive to the language.
structSort :: [SMT2.Sort] -> SMT2.Sort
structSort flds = SMT2.Sort $ "(Struct" <> Builder.decimal n <> foldMap f flds <> ")"
  where f :: SMT2.Sort -> Builder
        f (SMT2.Sort s) = " " <> s
        n = length flds

asSMT2Type :: forall a tp . SMTLib2Tweaks a => TypeMap tp -> SMT2.Sort
asSMT2Type BoolTypeMap    = SMT2.boolSort
asSMT2Type NatTypeMap     = SMT2.intSort
asSMT2Type IntegerTypeMap = SMT2.intSort
asSMT2Type RealTypeMap    = SMT2.realSort
asSMT2Type (BVTypeMap w)  = SMT2.bvSort (natValue w)
asSMT2Type (FloatTypeMap fpp) = SMT2.Sort $ mkFloatSymbol "FloatingPoint" (asSMTFloatPrecision fpp)
asSMT2Type ComplexToStructTypeMap =
  structSort [ SMT2.realSort, SMT2.realSort ]
asSMT2Type ComplexToArrayTypeMap =
  smtlib2arrayType @a [SMT2.boolSort] SMT2.realSort
asSMT2Type (PrimArrayTypeMap i r) =
  smtlib2arrayType @a (toListFC (asSMT2Type @a) i) (asSMT2Type @a r)
asSMT2Type (FnArrayTypeMap _ _) =
  error "SMTLIB backend does not support function types as first class."
asSMT2Type (StructTypeMap f) =
  structSort (toListFC (asSMT2Type @a) f)

-- Default instance.
instance SMTLib2Tweaks () where
  smtlib2tweaks = ()

------------------------------------------------------------------------
readBin :: Num a => ReadS a
readBin = readInt 2 (`elem` ("01" :: String)) digitToInt

------------------------------------------------------------------------
-- Type

mkRoundingOp :: Builder -> RoundingMode -> Builder
mkRoundingOp op r = op <> " " <> fromString (show r)

------------------------------------------------------------------------
-- Writer

newtype Writer a = Writer { declaredTuples :: IORef (Set Int) }

type instance SMTWriter.Term (Writer a) = Term

instance Num Term where
  x + y = SMT2.add [x, y]
  x - y = SMT2.sub x [y]
  x * y = SMT2.mul [x, y]
  negate x = SMT2.negate x
  abs x    = SMT2.ite (SMT2.ge [x, SMT2.numeral 0]) x (SMT2.negate x)
  signum x =
    SMT2.ite (SMT2.ge [x, SMT2.numeral 0])
             (SMT2.ite (SMT2.eq [x, SMT2.numeral 0]) (SMT2.numeral 0) (SMT2.numeral 1))
             (SMT2.negate (SMT2.numeral 1))
  fromInteger = SMT2.numeral

varBinding :: forall a . SMTLib2Tweaks a => (Text, Some TypeMap) -> (Text, SMT2.Sort)
varBinding (nm, Some tp) = (nm, asSMT2Type @a tp)

-- The SMTLIB2 exporter uses the datatypes theory for representing structures.
--
-- Note about structs:
--
-- For each length XX associated to some structure with that length in the
-- formula, the SMTLIB2 backend defines a datatype "StructXX" with the
-- constructor "mk-structXX", and projection operations "structXX-projII"
-- for II an natural number less than XX.
instance SupportTermOps Term where
  boolExpr b = if b then SMT2.true else SMT2.false
  notExpr = SMT2.not

  andAll = SMT2.and
  orAll  = SMT2.or

  x .== y = SMT2.eq [x,y]
  x ./= y = SMT2.distinct [x,y]

  letExpr = SMT2.letBinder

  ite = SMT2.ite

  sumExpr = SMT2.add

  termIntegerToReal = SMT2.toReal
  termRealToInteger = SMT2.toInt

  integerTerm = SMT2.numeral
  intDiv x y = SMT2.div x [y]
  intMod = SMT2.mod
  intAbs     = SMT2.abs

  intDivisible x 0 = x .== integerTerm 0
  intDivisible x k = intMod x (integerTerm (toInteger k)) .== 0

  rationalTerm r | d == 1    = SMT2.decimal n
                 | otherwise = (SMT2.decimal n) SMT2../ [SMT2.decimal d]
    where n = numerator r
          d = denominator r

  x .<  y = SMT2.lt [x,y]
  x .<= y = SMT2.le [x,y]
  x .>  y = SMT2.gt [x,y]
  x .>= y = SMT2.ge [x,y]

  bvTerm w u = SMT2.bvdecimal u (natValue w)

  bvNeg = SMT2.bvneg
  bvAdd x y = SMT2.bvadd x [y]
  bvSub = SMT2.bvsub
  bvMul x y = SMT2.bvmul x [y]

  bvSLe = SMT2.bvsle
  bvULe = SMT2.bvule

  bvSLt = SMT2.bvslt
  bvULt = SMT2.bvult

  bvUDiv = SMT2.bvudiv
  bvURem = SMT2.bvurem
  bvSDiv = SMT2.bvsdiv
  bvSRem = SMT2.bvsrem

  bvNot = SMT2.bvnot
  bvAnd x y = SMT2.bvand x [y]
  bvOr  x y = SMT2.bvor  x [y]
  bvXor x y = SMT2.bvxor x [y]

  bvShl  = SMT2.bvshl
  bvLshr = SMT2.bvlshr
  bvAshr = SMT2.bvashr

  bvConcat = SMT2.concat

  bvExtract _ b n x | n > 0 = SMT2.extract (b+n-1) b x
                    | otherwise = error $ "bvExtract given non-positive width " ++ show n

  floatPZero fpp = term_app (mkFloatSymbol "+zero" (asSMTFloatPrecision fpp)) []
  floatNZero fpp = term_app (mkFloatSymbol "-zero" (asSMTFloatPrecision fpp)) []
  floatNaN fpp   = term_app (mkFloatSymbol "NaN"   (asSMTFloatPrecision fpp)) []
  floatPInf fpp  = term_app (mkFloatSymbol "+oo"   (asSMTFloatPrecision fpp)) []
  floatNInf fpp  = term_app (mkFloatSymbol "-oo"   (asSMTFloatPrecision fpp)) []

  floatNeg  = un_app "fp.neg"
  floatAbs  = un_app "fp.abs"
  floatSqrt r = un_app $ mkRoundingOp "fp.sqrt " r

  floatAdd r = bin_app $ mkRoundingOp "fp.add" r
  floatSub r = bin_app $ mkRoundingOp "fp.sub" r
  floatMul r = bin_app $ mkRoundingOp "fp.mul" r
  floatDiv r = bin_app $ mkRoundingOp "fp.div" r
  floatRem = bin_app "fp.rem"
  floatMin = bin_app "fp.min"
  floatMax = bin_app "fp.max"

  floatFMA r x y z = term_app (mkRoundingOp "fp.fma" r) [x, y, z]

  floatEq x y  = SMT2.eq [x,y]
  floatFpEq = bin_app "fp.eq"
  floatLe   = bin_app "fp.leq"
  floatLt   = bin_app "fp.lt"

  floatIsNaN      = un_app "fp.isNaN"
  floatIsInf      = un_app "fp.isInfinite"
  floatIsZero     = un_app "fp.isZero"
  floatIsPos      = un_app "fp.isPositive"
  floatIsNeg      = un_app "fp.isNegative"
  floatIsSubnorm  = un_app "fp.isSubnormal"
  floatIsNorm     = un_app "fp.isNormal"

  floatCast fpp r = un_app $ mkRoundingOp (mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)) r
  floatRound r = un_app $ mkRoundingOp "fp.roundToIntegral" r
  floatFromBinary fpp = un_app $ mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)
  bvToFloat fpp r =
    un_app $ mkRoundingOp (mkFloatSymbol "to_fp_unsigned" (asSMTFloatPrecision fpp)) r
  sbvToFloat fpp r = un_app $ mkRoundingOp (mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)) r
  realToFloat fpp r = un_app $ mkRoundingOp (mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)) r

  floatToBV w r =
    un_app $ mkRoundingOp ("(fp.to_ubv " <> fromString (show w) <> ")") r
  floatToSBV w r =
    un_app $ mkRoundingOp ("(fp.to_sbv " <> fromString (show w) <> ")") r

  floatToReal = un_app "fp.to_real"

  realIsInteger = SMT2.isInt

  realSin = un_app "sin"
  realCos = un_app "cos"
  realATan2 = bin_app "atan2"
  realSinh = un_app "sinh"
  realCosh = un_app "cosh"
  realExp = un_app "exp"
  realLog = un_app "log"

  structCtor args = term_app nm args
    where nm = "mk-struct" <> Builder.decimal (length args)

  structFieldSelect n a i = term_app nm [a]
    where nm = "struct" <> Builder.decimal n <> "-proj" <> Builder.decimal i

  smtFnApp nm args = term_app (SMT2.renderTerm nm) args

  fromText t = SMT2.T (Builder.fromText t)

------------------------------------------------------------------------
-- Writer

newWriter :: a
          -> Streams.OutputStream Text
          -> AcknowledgementAction t (Writer a)
             -- ^ Action to run for consuming acknowledgement messages
          -> String
             -- ^ Name of solver for reporting purposes.
          -> Bool
             -- ^ Flag indicating if it is permitted to use
             -- "define-fun" when generating SMTLIB
          -> ProblemFeatures
             -- ^ Indicates what level of arithmetic is supported by solver.
          -> Bool
             -- ^ Indicates if quantifiers are supported.
          -> B.SymbolVarBimap t
             -- ^ Variable bindings for names.
          -> IO (WriterConn t (Writer a))
newWriter _ h ack solver_name permitDefineFun arithOption quantSupport bindings = do
  r <- newIORef Set.empty
  let initWriter =
        Writer
        { declaredTuples = r
        }
  conn <- newWriterConn h ack solver_name arithOption bindings initWriter
  return $! conn { supportFunctionDefs = permitDefineFun
                 , supportQuantifiers = quantSupport
                 }

type instance Command (Writer a) = SMT2.Command

instance SMTLib2Tweaks a => SMTWriter (Writer a) where
  forallExpr vars t = SMT2.forall (varBinding @a <$> vars) t
  existsExpr vars t = SMT2.exists (varBinding @a <$> vars) t

  arrayConstant =
    case smtlib2arrayConstant @a of
      Just f -> Just $ \idxTypes (Some retType) c ->
        f ((\(Some itp) -> asSMT2Type @a itp) <$> idxTypes) (asSMT2Type @a retType) c
      Nothing -> Nothing
  arraySelect = smtlib2arraySelect @a
  arrayUpdate = smtlib2arrayUpdate @a

  commentCommand _ b = SMT2.Cmd ("; " <> b)

  assertCommand _ e = SMT2.assert e

  assertNamedCommand _ e nm = SMT2.assertNamed e nm

  pushCommand _  = SMT2.push 1
  popCommand _   = SMT2.pop 1
  resetCommand _ = SMT2.resetAssertions

  checkCommand _ = SMT2.checkSat
  checkWithAssumptionsCommand _ = SMT2.checkSatWithAssumptions

  getUnsatAssumptionsCommand _ = SMT2.getUnsatAssumptions
  getUnsatCoreCommand _ = SMT2.getUnsatCore
  setOptCommand _ = SMT2.setOption

  declareCommand _proxy v argTypes retType =
    SMT2.declareFun v (toListFC (asSMT2Type @a) argTypes) (asSMT2Type @a retType)

  defineCommand _proxy f args return_type e =
    let resolveArg (var, Some tp) = (var, asSMT2Type @a tp)
     in SMT2.defineFun f (resolveArg <$> args) (asSMT2Type @a return_type) e

  declareStructDatatype conn n = do
    let r = declaredTuples (connState conn)
    s <- readIORef r
    when (Set.notMember n s) $ do
      let type_name i = fromString ('T' : show i)
      let params = builder_list $ type_name  <$> [1..n]
      let n_str = fromString (show n)
      let tp = "Struct" <> n_str
      let ctor = "mk-struct" <> n_str
      let field_def i = app field_nm [type_name i]
            where field_nm = "struct" <> n_str <> "-proj" <> fromString (show (i-1))
      let fields = field_def <$> [1..n]
      let decl = app tp [app ctor fields]
      let decls = "(" <> decl <> ")"
      let cmd = SMT2.Cmd $ app "declare-datatypes" [ params, decls ]
      addCommand conn cmd

      writeIORef r $! Set.insert n s

  writeCommand conn (SMT2.Cmd cmd) =
    do let cmdout = Lazy.toStrict (Builder.toLazyText cmd)
       Streams.write (Just (cmdout <> "\n")) (connHandle conn)
       -- force a flush
       Streams.write (Just "") (connHandle conn)

-- | Write check sat command
writeCheckSat :: SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
writeCheckSat w = addCommandNoAck w SMT2.checkSat

writeExit :: forall a t. SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
writeExit w = addCommand w SMT2.exit

setLogic :: SMTLib2Tweaks a => WriterConn t (Writer a) -> SMT2.Logic -> IO ()
setLogic w l = addCommand w $ SMT2.setLogic l

setOption :: SMTLib2Tweaks a => WriterConn t (Writer a) -> Text -> Text -> IO ()
setOption w nm val = addCommand w $ SMT2.setOption nm val

-- | Set the produce models option (We typically want this)
setProduceModels :: SMTLib2Tweaks a => WriterConn t (Writer a) -> Bool -> IO ()
setProduceModels w b = addCommand w $ SMT2.setProduceModels b

writeGetValue :: SMTLib2Tweaks a => WriterConn t (Writer a) -> [Term] -> IO ()
writeGetValue w l = addCommandNoAck w $ SMT2.getValue l

parseBoolSolverValue :: Monad m => SExp -> m Bool
parseBoolSolverValue (SAtom "true")  = return True
parseBoolSolverValue (SAtom "false") = return False
parseBoolSolverValue s = fail $ "Could not parse solver value: " ++ show s

parseRealSolverValue :: (Applicative m, Monad m) => SExp -> m Rational
parseRealSolverValue (SAtom v) | Just (r,"") <- readDecimal (Text.unpack v) =
  return r
parseRealSolverValue (SApp ["-", x]) = do
  negate <$> parseRealSolverValue x
parseRealSolverValue (SApp ["/", x , y]) = do
  (/) <$> parseRealSolverValue x
      <*> parseRealSolverValue y
parseRealSolverValue s = fail $ "Could not parse solver value: " ++ show s

parseBvSolverValue :: Monad m => Int -> SExp -> m Integer
parseBvSolverValue _ s
  | (n, _) <- parseBVLitHelper s = return n
  | otherwise = fail $ "Could not parse solver value: " ++ show s

parseBVLitHelper :: SExp -> (Integer, Int)
parseBVLitHelper (SAtom (Text.unpack -> ('#' : 'b' : n_str))) | [(n, "")] <- readBin n_str =
  (n, length n_str)
parseBVLitHelper (SAtom (Text.unpack -> ('#' : 'x' : n_str))) | [(n, "")] <- readHex n_str =
  (n, length n_str * 4)
parseBVLitHelper (SApp ["_", SAtom (Text.unpack -> ('b' : 'v' : n_str)), SAtom (Text.unpack -> w_str)])
  | [(n, "")] <- readDec n_str, [(w, "")] <- readDec w_str = (n, w)
parseBVLitHelper _ = (0, 0)

parseFloatSolverValue :: Monad m => SExp -> m Integer
parseFloatSolverValue (SApp ["fp", sign_s, exponent_s, significant_s])
  | (sign_n, 1) <- parseBVLitHelper sign_s
  , (exponent_n, eb) <- parseBVLitHelper exponent_s
  , 2 <= eb
  , (significant_n, sb) <- parseBVLitHelper significant_s
  , 1 <= sb
  = return $ (((sign_n `shiftL` eb) + exponent_n) `shiftL` sb) + significant_n
parseFloatSolverValue
  s@(SApp ["_", SAtom (Text.unpack -> nm), SAtom (Text.unpack -> eb_s), SAtom (Text.unpack -> sb_s)])

  | [(eb, "")] <- readDec eb_s, [(sb, "")] <- readDec sb_s = case nm of
    "+oo"   -> return $ ones eb `shiftL` (sb - 1)
    "-oo"   -> return $ setBit (ones eb `shiftL` (sb - 1)) (eb + sb - 1)
    "+zero" -> return 0
    "-zero" -> return $ bit (eb + sb - 1)
    "NaN"   -> return $ ones (eb + sb - 1)
    _       -> fail $ "Could not parse float solver value: " ++ show s
parseFloatSolverValue s =
  fail $ "Could not parse float solver value: " ++ show s

ones :: Int -> Integer
ones n = foldl setBit 0 [0..(n - 1)]

parseBvArraySolverValue :: (Monad m,
                            1 <= w,
                            1 <= v)
                        => NatRepr w
                        -> NatRepr v
                        -> SExp
                        -> m (Maybe (GroundArray (Ctx.SingleCtx (BaseBVType w)) (BaseBVType v)))
parseBvArraySolverValue _ v (SApp [SApp ["as", "const", _], c]) = do
  c' <- parseBvSolverValue (widthVal v) c
  return . Just $ ArrayConcrete c' Map.empty
parseBvArraySolverValue w v (SApp ["store", arr, idx, val]) = do
  arr' <- parseBvArraySolverValue w v arr
  case arr' of
    Just (ArrayConcrete base m) -> do
      idx' <- B.BVIndexLit w <$> parseBvSolverValue (widthVal w) idx
      val' <- parseBvSolverValue (widthVal v) val
      return . Just $ ArrayConcrete base (Map.insert (Ctx.empty Ctx.:> idx') val' m)
    _ -> return Nothing
parseBvArraySolverValue _ _ _ = return Nothing

------------------------------------------------------------------------
-- Session

-- | This is an interactive session with an SMT solver
data Session t a = Session
  { sessionWriter   :: !(WriterConn t (Writer a))
  , sessionResponse :: !(Streams.InputStream Text)
  }

-- | Get a value from a solver (must be called after checkSat)
runGetValue :: SMTLib2Tweaks a
            => Session t a
            -> Term
            -> IO SExp
runGetValue s e = do
  writeGetValue (sessionWriter s) [ e ]
  msexp <- try $ Streams.parseFromStream parseSExp (sessionResponse s)
  case msexp of
    Left Streams.ParseException{} -> fail $ "Could not parse solver value."
    Right (SApp [SApp [_, b]]) -> return b
    Right sexp -> fail $ "Could not parse solver value:\n  " ++ show sexp

-- | This function runs a check sat command
runCheckSat :: forall b t a.
               SMTLib2Tweaks b
            => Session t b
            -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
               -- ^ Function for evaluating model.
               -- The evaluation should be complete before
            -> IO a
runCheckSat s doEval =
  do let w = sessionWriter s
         r = sessionResponse s
     addCommandNoAck w (checkCommand w)
     res <- smtSatResult w r
     case res of
       Unsat x -> doEval (Unsat x)
       Unknown -> doEval Unknown
       Sat _ ->
         do evalFn <- smtExprGroundEvalFn w (smtEvalFuns w r)
            doEval (Sat (evalFn, Nothing))

instance SMTLib2Tweaks a => SMTReadWriter (Writer a) where
  smtEvalFuns w s = smtLibEvalFuns Session { sessionWriter = w
                                           , sessionResponse = s }

  smtSatResult p s =
    do mb <- try (Streams.parseFromStream parseNextWord s)
       case mb of
         Left (SomeException e) ->
            fail $ unlines [ "Could not parse check_sat result."
                           , "*** Exception: " ++ displayException e
                           ]
         Right "unsat" -> return (Unsat ())
         Right "sat" -> return (Sat ())
         Right "unknown" -> return Unknown
         Right res -> throw $ SMTLib2ParseError (checkCommand p) (Text.pack (show res))

  smtUnsatAssumptionsResult p s =
    do mb <- try (Streams.parseFromStream parseSExp s)
       let cmd = getUnsatAssumptionsCommand p
       case mb of
         Right (asNegAtomList -> Just as) -> return as
         Right (SApp [SAtom "error", SString msg]) -> throw (SMTLib2Error cmd msg)
         Right res -> throw (SMTLib2ParseError cmd (Text.pack (show res)))
         Left (SomeException e) -> throw $ SMTLib2ParseError cmd $ Text.pack $
                 unlines [ "Could not parse unsat assumptions result."
                         , "*** Exception: " ++ displayException e
                         ]

  smtUnsatCoreResult p s =
    do mb <- try (Streams.parseFromStream parseSExp s)
       let cmd = getUnsatCoreCommand p
       case mb of
         Right (asAtomList -> Just nms) -> return nms
         Right (SApp [SAtom "error", SString msg]) -> throw (SMTLib2Error cmd msg)
         Right res -> throw (SMTLib2ParseError cmd (Text.pack (show res)))
         Left (SomeException e) -> throw $ SMTLib2ParseError cmd $ Text.pack $
                 unlines [ "Could not parse unsat core result."
                         , "*** Exception: " ++ displayException e
                         ]

data SMTLib2Exception
  = SMTLib2Unsupported SMT2.Command
  | SMTLib2Error SMT2.Command Text
  | SMTLib2ParseError SMT2.Command Text

instance Show SMTLib2Exception where
  show (SMTLib2Unsupported (SMT2.Cmd cmd)) =
     unlines
       [ "unsupported command:"
       , "  " ++ Lazy.unpack (Builder.toLazyText cmd)
       ]
  show (SMTLib2Error (SMT2.Cmd cmd) msg) =
     unlines
       [ "Solver reported an error:"
       , "  " ++ Text.unpack msg
       , "in response to command:"
       , "  " ++ Lazy.unpack (Builder.toLazyText cmd)
       ]
  show (SMTLib2ParseError (SMT2.Cmd cmd) msg) =
     unlines
       [ "Could not parse solver response:"
       , "  " ++ Text.unpack msg
       , "in response to command:"
       , "  " ++ Lazy.unpack (Builder.toLazyText cmd)
       ]

instance Exception SMTLib2Exception

smtAckResult :: Streams.InputStream Text -> AcknowledgementAction t (Writer a)
smtAckResult resp = AckAction $ \_conn cmd ->
  do mb <- try (Streams.parseFromStream parseSExp resp)
     case mb of
       Right (SAtom "success") -> return ()
       Right (SAtom "unsupported") -> throw (SMTLib2Unsupported cmd)
       Right (SApp [SAtom "error", SString msg]) -> throw (SMTLib2Error cmd msg)
       Right res -> throw (SMTLib2ParseError cmd (Text.pack (show res)))
       Left (SomeException e) -> throw $ SMTLib2ParseError cmd $ Text.pack $
               unlines [ "Could not parse acknowledgement result."
                       , "*** Exception: " ++ displayException e
                       ]

smtLibEvalFuns ::
  forall t a. SMTLib2Tweaks a => Session t a -> SMTEvalFunctions (Writer a)
smtLibEvalFuns s = SMTEvalFunctions
                  { smtEvalBool = evalBool
                  , smtEvalBV = evalBV
                  , smtEvalReal = evalReal
                  , smtEvalFloat = evalFloat
                  , smtEvalBvArray = Just (SMTEvalBVArrayWrapper evalBvArray)
                  }
  where
  evalBool tm = parseBoolSolverValue =<< runGetValue s tm
  evalBV w tm = parseBvSolverValue w =<< runGetValue s tm
  evalReal tm = parseRealSolverValue =<< runGetValue s tm
  evalFloat tm = parseFloatSolverValue =<< runGetValue s tm

  evalBvArray :: SMTEvalBVArrayFn (Writer a) w v
  evalBvArray w v tm = parseBvArraySolverValue w v =<< runGetValue s tm


class (SMTLib2Tweaks a, Show a) => SMTLib2GenericSolver a where
  defaultSolverPath :: a -> B.ExprBuilder t st fs -> IO FilePath

  defaultSolverArgs :: a -> B.ExprBuilder t st fs -> IO [String]

  defaultFeatures :: a -> ProblemFeatures

  setDefaultLogicAndOptions :: WriterConn t (Writer a) -> IO()

  newDefaultWriter
    :: a ->
       AcknowledgementAction t (Writer a) ->
       ProblemFeatures ->
       B.ExprBuilder t st fs ->
       Streams.OutputStream Text ->
       IO (WriterConn t (Writer a))
  newDefaultWriter solver ack feats sym h =
    newWriter solver h ack (show solver) True feats True
      =<< B.getSymbolVarBimap sym

  -- | Run the solver in a session.
  withSolver
    :: a
    -> AcknowledgementAction t (Writer a)
    -> ProblemFeatures
    -> B.ExprBuilder t st fs
    -> FilePath
      -- ^ Path to solver executable
    -> LogData
    -> (Session t a -> IO b)
      -- ^ Action to run
    -> IO b
  withSolver solver ack feats sym path logData action = do
    args <- defaultSolverArgs solver sym
    withProcessHandles path args Nothing $
      \(in_h, out_h, err_h, ph) -> do

        (in_stream, out_stream, err_reader) <-
          demuxProcessHandles in_h out_h err_h
            (fmap (\x -> ("; ", x)) $ logHandle logData)

        writer <- newDefaultWriter solver ack feats sym in_stream
        let s = Session
              { sessionWriter   = writer
              , sessionResponse = out_stream
              }

        -- Set solver logic and solver-specific options
        setDefaultLogicAndOptions writer

        -- Run action with session.
        r <- action s
        -- Tell solver to exit
        writeExit writer

        ec <- Process.waitForProcess ph
        stopHandleReader err_reader
        case ec of
          Exit.ExitSuccess -> return r
          Exit.ExitFailure exit_code -> fail $
            show solver ++ " exited with unexpected code: " ++ show exit_code

  runSolverInOverride
    :: a
    -> AcknowledgementAction t (Writer a)
    -> ProblemFeatures
    -> B.ExprBuilder t st fs
    -> LogData
    -> [B.BoolExpr t]
    -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO b)
    -> IO b
  runSolverInOverride solver ack feats sym logData predicates cont = do
    I.logSolverEvent sym
      I.SolverStartSATQuery
        { I.satQuerySolverName = show solver
        , I.satQueryReason     = logReason logData
        }
    path <- defaultSolverPath solver sym
    withSolver solver ack feats sym path (logData{logVerbosity=2}) $ \session -> do
      -- Assume the predicates hold.
      forM_ predicates (SMTWriter.assume (sessionWriter session))
      -- Run check SAT and get the model back.
      runCheckSat session $ \result -> do
        I.logSolverEvent sym
          I.SolverEndSATQuery
            { I.satQueryResult = forgetModelAndCore result
            , I.satQueryError  = Nothing
            }
        cont result

-- | A default method for writing SMTLib2 problems without any
--   solver-specific tweaks.
writeDefaultSMT2 :: SMTLib2Tweaks a
                 => a
                 -> AcknowledgementAction t (Writer a)
                 -> String
                    -- ^ Name of solver for reporting.
                 -> ProblemFeatures
                    -- ^ Features supported by solver
                 -> B.ExprBuilder t st fs
                 -> IO.Handle
                 -> [B.BoolExpr t]
                 -> IO ()
writeDefaultSMT2 a ack nm feat sym h ps = do
  bindings <- B.getSymbolVarBimap sym
  str <- Streams.encodeUtf8 =<< Streams.handleToOutputStream h
  c <- newWriter a str ack nm True feat True bindings
  setProduceModels c True
  forM_ ps (SMTWriter.assume c)
  writeCheckSat c
  writeExit c

startSolver
  :: SMTLib2GenericSolver a
  => a
  -> (Streams.InputStream Text -> AcknowledgementAction t (Writer a))
        -- ^ Action for acknowledging command responses
  -> (WriterConn t (Writer a) -> IO ()) -- ^ Action for setting start-up-time options and logic
  -> ProblemFeatures
  -> Maybe IO.Handle
  -> B.ExprBuilder t st fs
  -> IO (SolverProcess t (Writer a))
startSolver solver ack setup feats auxOutput sym = do
  path <- defaultSolverPath solver sym
  args <- defaultSolverArgs solver sym
  solver_process <- Process.createProcess $
    (Process.proc path args)
      { Process.std_in       = Process.CreatePipe
      , Process.std_out      = Process.CreatePipe
      , Process.std_err      = Process.CreatePipe
      , Process.create_group = True
      , Process.cwd          = Nothing
      }
  (in_h, out_h, err_h, ph) <- case solver_process of
    (Just in_h, Just out_h, Just err_h, ph) -> return (in_h, out_h, err_h, ph)
    _ -> fail "Internal error in startSolver: Failed to create handle."

  (in_stream, out_stream, err_reader) <-
     demuxProcessHandles in_h out_h err_h
       (fmap (\x -> ("; ", x)) auxOutput)

  -- Create writer
  writer <- newDefaultWriter solver (ack out_stream) feats sym in_stream

  -- Set solver logic and solver-specific options
  setup writer

  earlyUnsatRef <- newIORef Nothing

  return $! SolverProcess
    { solverConn     = writer
    , solverStdin    = in_stream
    , solverStderr   = err_reader
    , solverHandle   = ph
    , solverResponse = out_stream
    , solverEvalFuns = smtEvalFuns writer out_stream
    , solverLogFn    = I.logSolverEvent sym
    , solverName     = show solver
    , solverEarlyUnsat = earlyUnsatRef
    }

shutdownSolver
  :: SMTLib2GenericSolver a => a -> SolverProcess t (Writer a) -> IO (Exit.ExitCode, Lazy.Text)
shutdownSolver _solver p = do
  -- Tell solver to exit
  writeExit (solverConn p)
  txt <- readAllLines (solverStderr p)
  ec <- Process.waitForProcess (solverHandle p)
  stopHandleReader (solverStderr p)
  return (ec,txt)
