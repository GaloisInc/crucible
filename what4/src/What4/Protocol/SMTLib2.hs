------------------------------------------------------------------------
-- |
-- Module           : What4.Protocol.SMTLib2
-- Description      : Inteface for solvers that consume SMTLib2
-- Copyright        : (c) Galois, Inc 2014-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module defines operations for producing SMTLib2-compatible queries
-- useful for interfacing with solvers that accecpt SMTLib2 as an input language.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.Protocol.SMTLib2
  ( -- SMTLib special purpose exports
    Writer
  , SMTLib2Tweaks(..)
  , newWriter
  , writeCheckSat
  , writeExit
  , Expr
  , writeGetValue
  , runCheckSat
  , unType
  , arraySelect1
  , arrayUpdate1
  , arrayType1
    -- * Logic
  , Logic(..)
  , qf_bv
  , all_supported
  , setLogic
    -- * Option
  , Option(..)
  , produceModels
  , ppDecimal
  , setOption
    -- * Solvers and External interface
  , Session(..)
  , writeDefaultSMT2
    -- * Re-exports
  , SMTWriter.WriterConn
  , SMTWriter.assume
  ) where

import           Control.Applicative
import           Control.Exception
import           Control.Monad.State.Strict
import           Data.Char(digitToInt)
import           Data.IORef
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.Map.Strict as Map
import           Data.Monoid
import           Data.Parameterized.NatRepr
import qualified Data.Parameterized.Context as Ctx
import           Data.Ratio
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import           Data.Text.Lazy.Builder.Int (decimal)
import           Numeric (readDec, readHex, readInt)
import qualified System.IO as IO
import qualified System.IO.Streams as Streams
import qualified System.IO.Streams.Attoparsec as Streams

import           Prelude hiding (writeFile)

import           What4.BaseTypes
import           What4.SatResult
import qualified What4.Expr.Builder as B
import           What4.Expr.GroundEval
import           What4.ProblemFeatures
import           What4.Protocol.ReadDecimal
import           What4.Protocol.SExp
import qualified What4.Protocol.SMTWriter as SMTWriter
import           What4.Protocol.SMTWriter hiding (assume)


------------------------------------------------------------------------
readBin :: Num a => ReadS a
readBin = readInt 2 (`elem` ("01" :: String)) digitToInt

------------------------------------------------------------------------
-- Logic

newtype Logic = Logic Builder

qf_bv :: Logic
qf_bv = Logic "QF_BV"

-- | Set the logic to all supported logics.
all_supported :: Logic
all_supported = Logic "ALL_SUPPORTED"

------------------------------------------------------------------------
-- Type

arrayType1 :: SMTLib2Tweaks a => a -> SMT_Type -> Builder -> Builder
arrayType1 tweaks i v = "(Array " <> unType tweaks i <> " " <> v <> ")"

unType :: SMTLib2Tweaks a => a -> SMT_Type -> Builder
unType _ SMT_BoolType    = "Bool"
unType _ (SMT_BVType w)  =  "(_ BitVec " <> fromString (show w) <> ")"
unType _ SMT_IntegerType = "Int"
unType _ SMT_RealType    = "Real"
unType a (SMT_ArrayType i e) = smtlib2arrayType a i e
unType a (SMT_StructType flds) = "(Struct" <> decimal n <> foldMap f flds <> ")"
  where f :: SMT_Type -> Builder
        f tp = " " <> unType a tp
        n = length flds
unType _ SMT_FnType{} =
  error "SMTLIB backend does not support function types as first class."

------------------------------------------------------------------------
-- Expr

newtype Writer a = Writer { declaredTuples :: IORef (Set Int) }

type Expr a = Term (Writer a)

instance IsString (Term (Writer a)) where
  fromString = T . fromString

instance SMTLib2Tweaks a => Num (Expr a) where
  (+) = bin_app "+"
  (-) = bin_app "-"
  (*) = bin_app "*"
  negate x = term_app "-" [x]
  abs x    = ite (x .>= 0) x (negate x)
  signum x = ite (x .== 0) 0 (ite (x .> 0) 1 (negate 1))
  fromInteger i | i >= 0 = T $ decimal i
                | otherwise = negate (T (decimal (negate i)))

varBinding :: SMTLib2Tweaks a => a -> Text -> SMT_Type -> Builder
varBinding a nm tp = app_list (Builder.fromText nm) [unType a tp]

letBinding :: Text -> Term h -> Builder
letBinding nm t = app_list (Builder.fromText nm) [renderTerm t]

binder_app :: Builder -> [Builder] -> Term h -> Term h
binder_app _  []    t = t
binder_app nm (h:r) t = T (app nm [app_list h r, renderTerm t])

arraySelect1 :: Expr a -> Expr a -> Expr a
arraySelect1 = bin_app "select"

arrayUpdate1 :: Expr a -> Expr a -> Expr a -> Expr a
arrayUpdate1 a i v = term_app "store" [a,i,v]

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
  smtlib2arrayType :: a -> [SMT_Type] -> SMT_Type -> Builder
  smtlib2arrayType a i r = foldr (arrayType1 a) (unType a r) i

  smtlib2arrayConstant :: Maybe ([SMT_Type] -> SMT_Type -> Expr a -> Expr a)
  smtlib2arrayConstant = Nothing

  smtlib2arraySelect :: Term (Writer a) -> [Term (Writer a)] -> Term (Writer a)
  smtlib2arraySelect a [] = a
  smtlib2arraySelect a (h:l) = smtlib2arraySelect (arraySelect1 a h) l

  smtlib2arrayUpdate :: Term (Writer a) -> [Term (Writer a)] -> Expr a -> Term (Writer a)
  smtlib2arrayUpdate a i v =
    case i of
      [] -> error "arrayUpdate given empty list"
      i1:ir -> nestedArrayUpdate  a (i1,ir) v

-- Default instance.
instance SMTLib2Tweaks () where
  smtlib2tweaks = ()

toIntegerTerm :: SMTLib2Tweaks a => Integer -> Expr a
toIntegerTerm x | x >= 0    = T $ decimal x
                | otherwise = negate (T (decimal (negate x)))

toRealTerm :: SMTLib2Tweaks a => Integer -> Expr a
toRealTerm x | x >= 0    = T $ decimal x <> ".0"
             | otherwise = negate (T (decimal (negate x) <> ".0"))

-- | Select a valued from a nested array
nestedArrayUpdate :: Expr a -> (Expr a, [Expr a]) -> Expr a -> Expr a
nestedArrayUpdate a (h,[]) v = arrayUpdate1 a h v
nestedArrayUpdate a (h,i:l) v = arrayUpdate1 a h sub_a'
  where sub_a' = nestedArrayUpdate (arraySelect1 a h) (i,l) v

exprTweaks :: SMTLib2Tweaks a => f (Writer a) -> a
exprTweaks _ = smtlib2tweaks

-- The SMTLIB2 exporter uses the datatypes theory for representing structures.
--
-- Note about structs:
--
-- For each length XX associated to some structure with that length in the
-- formula, the SMTLIB2 backend defines a datatype "StructXX" with the
-- constructor "mk-structXX", and projection operations "structXX-projII"
-- for II an natural number less than XX.
instance SMTLib2Tweaks a => SupportTermOps (Expr a) where
  boolExpr b = T $ if b then "true" else "false"
  notExpr x = term_app "not" [x]

  andAll [] = T "true"
  andAll [x] = x
  andAll xs = term_app "and" xs

  orAll [] = T "false"
  orAll [x] = x
  orAll xs = term_app "or" xs

  (.==) = bin_app "="
  (./=) = bin_app "distinct"

  forallExpr vars t  =
    binder_app "forall" (uncurry (varBinding (exprTweaks t)) <$> vars) t
  existsExpr vars t  =
    binder_app "exists" (uncurry (varBinding (exprTweaks t)) <$> vars) t
  letExpr [] r = r
  letExpr ((nm,t):vars) r =
    T (app "let" [app_list (letBinding nm t) [], renderTerm (letExpr vars r)])

  ite c x y = term_app "ite" [c, x, y]

  sumExpr [] = 0
  sumExpr [e] = e
  sumExpr l = term_app "+" l

  termIntegerToReal x = term_app "to_real" [x]
  termRealToInteger x = term_app "to_int"  [x]

  integerTerm i = toIntegerTerm i

  rationalTerm r | d == 1 = toRealTerm n
                 | otherwise = term_app "/" [toRealTerm n, toRealTerm d]
    where n = numerator r
          d = denominator r

  (.<)  = bin_app "<"
  (.<=) = bin_app "<="
  (.>)  = bin_app ">"
  (.>=) = bin_app ">="

  bvTerm w u = bin_app "_" (fromString ("bv" ++ show d)) (fromString (show w))
    where d | u >= 0 = u
            | otherwise = 2^(widthVal w) + u

  bvNeg x = term_app "bvneg" [x]
  bvAdd = bin_app "bvadd"
  bvSub = bin_app "bvsub"
  bvMul = bin_app "bvmul"

  bvSLe = bin_app "bvsle"
  bvULe = bin_app "bvule"

  bvSLt = bin_app "bvslt"
  bvULt = bin_app "bvult"

  bvUDiv = bin_app "bvudiv"
  bvURem = bin_app "bvurem"
  bvSDiv = bin_app "bvsdiv"
  bvSRem = bin_app "bvsrem"

  bvAnd  = bin_app "bvand"
  bvOr   = bin_app "bvor"
  bvXor  = bin_app "bvxor"

  bvNot x = term_app "bvnot" [x]

  bvShl  = bin_app "bvshl"
  bvLshr = bin_app "bvlshr"
  bvAshr = bin_app "bvashr"

  bvConcat = bin_app "concat"

  bvExtract _ b n x = assert (n > 0) $
    let -- Get index of bit to end at (least-significant bit has index 0)
        end =  b+n-1
        -- Get index of bit to start at (least-significant bit has index 0)
        begin = b
        e = "(_ extract " <> decimal end <> " " <> decimal begin <> ")"
     in  term_app e [x]

  arrayConstant = smtlib2arrayConstant
  arraySelect   = smtlib2arraySelect
  arrayUpdate   = smtlib2arrayUpdate


  structCtor args = term_app nm args
    where nm = "mk-struct" <> decimal (length args)

  structFieldSelect n a i = term_app nm [a]
    where nm = "struct" <> decimal n <> "-proj" <> decimal i

  realIsInteger x = term_app "is_int" [x]

  realSin x = term_app "sin" [x]
  realCos x = term_app "cos" [x]
  realATan2 = bin_app "atan2"
  realSinh x = term_app "sinh" [x]
  realCosh x = term_app "cosh" [x]
  realExp x = term_app "exp" [x]
  realLog x = term_app "log" [x]

  smtFnApp nm args = term_app (renderTerm nm) args

------------------------------------------------------------------------
-- Option

newtype Option = Option Builder

-- | Option to produce models.
produceModels :: Bool -> Option
produceModels b = Option (":produce-models " <> ppBool b)

ppDecimal :: Bool -> Option
ppDecimal b = Option (":pp.decimal " <> ppBool b)

ppBool :: Bool -> Builder
ppBool True  = "true"
ppBool False = "false"

------------------------------------------------------------------------
-- Command

set_logic :: Logic -> Command (Writer a)
set_logic (Logic nm) = Cmd $ app "set-logic" [nm]

setOptionCommand :: Option -> Command (Writer a)
setOptionCommand (Option nm) = Cmd $ app "set-option" [nm]

checkSatCommand :: Command (Writer a)
checkSatCommand = Cmd "(check-sat)"

getValueCommand :: [Expr a] -> Command (Writer a)
getValueCommand values = Cmd $ app "get-value" [builder_list (renderTerm <$> values)]

------------------------------------------------------------------------
-- Writer

newWriter :: a
          -> IO.Handle
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
newWriter _ h solver_name permitDefineFun arithOption quantSupport bindings = do
  r <- newIORef Set.empty
  let initWriter = Writer r
  conn <- newWriterConn h solver_name arithOption bindings initWriter
  return $! conn { supportFunctionDefs = permitDefineFun
                 , supportQuantifiers = quantSupport
                 }

instance SMTLib2Tweaks a => SMTWriter (Writer a) where
  commentCommand _ b = Cmd ("; " <> b)

  assertCommand _ e = Cmd $ app "assert" [renderTerm e]

  pushCommand _  = Cmd "(push 1)"
  popCommand _   = Cmd "(pop 1)"
  checkCommand _ = checkSatCommand
  setOptCommand _ x y = setOptionCommand (Option opt)
    where opt = Builder.fromText x <> Builder.fromText " " <> y

  declareCommand proxy v argTypes retType = Cmd $
    app "declare-fun" [ Builder.fromText v
                      , builder_list (unType (exprTweaks proxy) <$> argTypes)
                      , unType (exprTweaks proxy) retType
                      ]

  defineCommand f args return_type e =
    let resolveArg (var, tp) = app (Builder.fromText var) [unType (exprTweaks e) tp]
     in Cmd $ app "define-fun" [ Builder.fromText f
                               , builder_list (resolveArg <$> args)
                               , unType (exprTweaks e) return_type
                               , renderTerm e
                               ]

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
      let cmd = Cmd $ app "declare-datatypes" [ params, decls ]
      addCommand conn cmd

      writeIORef r $! Set.insert n s

-- | Write check sat command
writeCheckSat :: SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
writeCheckSat w = addCommand w checkSatCommand

writeExit :: SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
writeExit w = addCommand w (Cmd "(exit)")

setLogic :: SMTLib2Tweaks a => WriterConn t (Writer a) -> Logic -> IO ()
setLogic w l = addCommand w (set_logic l)

setOption :: SMTLib2Tweaks a => WriterConn t (Writer a) -> Option -> IO ()
setOption w o = addCommand w (setOptionCommand o)

writeGetValue :: SMTLib2Tweaks a => WriterConn t (Writer a) -> [Expr a] -> IO ()
writeGetValue w l = addCommand w (getValueCommand l)

parseBoolSolverValue :: Monad m => SExp -> m Bool
parseBoolSolverValue (SAtom "true")  = return True
parseBoolSolverValue (SAtom "false") = return False
parseBoolSolverValue s = fail $ "Could not parse solver value: " ++ show s

parseRealSolverValue :: (Applicative m, Monad m) => SExp -> m Rational
parseRealSolverValue (SAtom v) | Just (r,"") <- readDecimal v =
  return r
parseRealSolverValue (SApp ["-", x]) = do
  negate <$> parseRealSolverValue x
parseRealSolverValue (SApp ["/", x , y]) = do
  (/) <$> parseRealSolverValue x
      <*> parseRealSolverValue y
parseRealSolverValue s = fail $ "Could not parse solver value: " ++ show s

parseBvSolverValue :: Monad m => Int -> SExp -> m Integer
parseBvSolverValue _ (SAtom ('#':'x':v)) | [(r,"")] <- readHex v =
  return r
parseBvSolverValue _ (SAtom ('#':'b':v)) | [(r,"")] <- readBin v =
  return r

parseBvSolverValue _ (SApp ["_", SAtom ('b':'v':n_str), SAtom _w_str])
  | [(n,"")] <- readDec n_str = do
    return n
parseBvSolverValue _ s = fail $ "Could not parse solver value: " ++ show s

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
  , sessionResponse :: !(Streams.InputStream UTF8.ByteString)
  }

-- | Get a value from a solver (must be called after checkSat)
runGetValue :: SMTLib2Tweaks a
            => Session t a
            -> Expr a
            -> IO SExp
runGetValue s e = do
  writeGetValue (sessionWriter s) [ e ]
  msexp <- try $ Streams.parseFromStream parseSExp (sessionResponse s)
  case msexp of
    Left Streams.ParseException{} -> fail $ "Could not parse solver value."
    Right (SApp [SApp [_, b]]) -> return b
    Right sexp -> fail $ "Could not parse solver value: " ++ show sexp

-- | This function runs a check sat command
runCheckSat :: forall b t a.
               SMTLib2Tweaks b
            => Session t b
            -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) -> IO a)
               -- ^ Function for evaluating model.
               -- The evaluation should be complete before
            -> IO a
runCheckSat s doEval =
  do let w = sessionWriter s
         r = sessionResponse s
     addCommand w (checkCommand w)
     res <- smtSatResult w r
     case res of
       Unsat -> doEval Unsat
       Unknown -> doEval Unknown
       Sat _ ->
         do evalFn <- smtExprGroundEvalFn w (smtEvalFuns w r)
            doEval (Sat (evalFn, Nothing))

instance SMTLib2Tweaks a => SMTReadWriter (Writer a) where
  smtEvalFuns w s = smtLibEvalFuns Session { sessionWriter = w
                                           , sessionResponse = s }


  smtSatResult _ s =
    do mb <- try (Streams.parseFromStream parseNextWord s)
       case mb of
         Left (SomeException e) ->
            fail $ unlines [ "Could not parse check_sat result."
                           , "*** Exception: " ++ displayException e
                           ]
         Right "unsat" -> return Unsat
         Right "sat" -> return (Sat ())
         Right "unknown" -> return Unknown
         Right res -> fail ("Could not interpret result from solver: " ++ res)



smtLibEvalFuns ::
  forall t a. SMTLib2Tweaks a => Session t a -> SMTEvalFunctions (Writer a)
smtLibEvalFuns s = SMTEvalFunctions
                  { smtEvalBool = evalBool
                  , smtEvalBV = evalBV
                  , smtEvalReal = evalReal
                  , smtEvalBvArray = Just (SMTEvalBVArrayWrapper evalBvArray)
                  }
  where
  evalBool tm = parseBoolSolverValue =<< runGetValue s tm
  evalBV w tm = parseBvSolverValue w =<< runGetValue s tm
  evalReal tm = parseRealSolverValue =<< runGetValue s tm

  evalBvArray :: SMTEvalBVArrayFn (Writer a) w v
  evalBvArray w v tm = parseBvArraySolverValue w v =<< runGetValue s tm



-- | A default method for writing SMTLib2 problems without any
--   solver-specific tweaks.
writeDefaultSMT2 :: SMTLib2Tweaks a
                 => a
                 -> String
                    -- ^ Name of solver for reporting.
                 -> ProblemFeatures
                    -- ^ Features supported by solver
                 -> B.ExprBuilder t st
                 -> IO.Handle
                 -> B.BoolExpr t
                 -> IO ()
writeDefaultSMT2 a nm feat sym h p = do
  bindings <- B.getSymbolVarBimap sym
  c <- newWriter a h nm True feat True bindings
  setOption c (produceModels True)
  SMTWriter.assume c p
  writeCheckSat c
  writeExit c
