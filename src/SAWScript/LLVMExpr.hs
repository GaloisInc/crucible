{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.LLVMExpr
  (-- * LLVM Expressions
    LLVMExprF(..)
  , LLVMExpr
  , ProtoLLVMExpr(..)
  , parseProtoLLVMExpr
  , ppProtoLLVMExpr
  , ppLLVMExpr
  , lssTypeOfLLVMExpr
  , updateLLVMExprType
  , isPtrLLVMExpr
  , isArgLLVMExpr
    -- * Logic expressions
  , LogicExpr
  -- , logicExprLLVMExprs
  , useLogicExpr
  , mkLogicExpr
    -- * Mixed expressions
  , MixedExpr(..)
    -- * Actual type
  , LLVMActualType
  , lssTypeOfActual
  , isActualPtr
  , isPrimitiveType
  , logicTypeOfActual
  , cryptolTypeOfActual
  , ppActualType
  , SymbolLocation (..)
  ) where

-- Imports {{{2

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif
-- import Data.Set (Set)
import Data.Functor.Identity
import Text.Parsec as P
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))
import Text.Read

import qualified Verifier.LLVM.Codebase as LSS

import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.Utils

import qualified Cryptol.TypeCheck.AST as Cryptol

data SymbolLocation
   = Block LSS.SymBlockID
   | LineOffset Integer
   | LineExact Integer
  deriving (Show)

type Parser a = ParsecT String () Identity a

-- The result of parsing an LLVM expression, before type-checking
data ProtoLLVMExpr
  = PVar String
  | PArg Int
  | PDeref ProtoLLVMExpr
  | PField Int ProtoLLVMExpr
  | PReturn
  -- | PIndex ProtoLLVMExpr ProtoLLVMExpr
    deriving (Show)

ppProtoLLVMExpr :: ProtoLLVMExpr -> Doc
ppProtoLLVMExpr (PVar x) = text x
ppProtoLLVMExpr PReturn = text "return"
ppProtoLLVMExpr (PArg n) = PP.string "args[" <> int n <> PP.string "]"
ppProtoLLVMExpr (PDeref e) = PP.text "*" <> PP.parens (ppProtoLLVMExpr e)
ppProtoLLVMExpr (PField n e) =
  PP.parens (ppProtoLLVMExpr e) <> text "." <> int n
--ppProtoLLVMExpr (PIndex n e) =
--  ppProtoLLVMExpr e <> text "[" <> ppProtoLLVMExpr n <> text "]"

parseProtoLLVMExpr :: String
                   -> Either ParseError ProtoLLVMExpr
parseProtoLLVMExpr = runIdentity . runParserT (parseExpr <* eof) () "expr"
  where
    parseExpr = P.choice
                [ parseDerefField
                , parseDeref
                , parseDirectField
                , parseAExpr
                ]
    parseAExpr = P.choice
                 [ parseReturn
                 , parseArgs
                 , parseVar
                 , parseParens
                 ]
    alphaUnder = P.choice [P.letter, P.char '_']
    parseIdent = (:) <$> alphaUnder <*> many (P.choice [alphaUnder, P.digit])
    parseVar :: Parser ProtoLLVMExpr
    parseVar = PVar <$> try parseIdent
    parseParens :: Parser ProtoLLVMExpr
    parseParens = P.string "(" *> parseExpr <* P.string ")"
    parseReturn :: Parser ProtoLLVMExpr
    parseReturn = try (P.string "return") >> return PReturn
    parseDeref :: Parser ProtoLLVMExpr
    parseDeref = PDeref <$> (try (P.string "*") *> parseAExpr)
    parseArgs :: Parser ProtoLLVMExpr
    parseArgs = do
      _ <- try (P.string "args[")
      ns <- many1 digit
      e <- case readMaybe ns of
             Just (n :: Int) -> return (PArg n)
             Nothing ->
               unexpected $ "Using `args` with non-numeric parameter: " ++ ns
      _ <- P.string "]"
      return e
    parseDirectField :: Parser ProtoLLVMExpr
    parseDirectField = do
      e <- try (parseAExpr <* P.string ".")
      ns <- many1 digit
      case readMaybe ns of
        Just (n :: Int) -> return (PField n e)
        Nothing -> unexpected $
          "Attempting to apply . operation to non-integer field ID: " ++ ns
    parseDerefField :: Parser ProtoLLVMExpr
    parseDerefField = do
      re <- try (parseAExpr <* P.string "->")
      ns <- many1 digit
      case readMaybe ns of
        Just (n :: Int) -> return (PField n (PDeref re))
        Nothing -> unexpected $
          "Attempting to apply -> operation to non-integer field ID: " ++ ns

-- NB: the types listed in each of these should be the type of the
-- entire expression. So "Deref v tp" means "*v has type tp".
data LLVMExprF v
  = Arg Int LSS.Ident LLVMActualType
  | Global LSS.Symbol LLVMActualType
  | Deref v LLVMActualType
  -- | Index v v LLVMActualType
  | StructField v LSS.StructInfo Int LLVMActualType
  | ReturnValue LLVMActualType
  deriving (Functor, CC.Foldable, CC.Traversable)

instance CC.EqFoldable LLVMExprF where
  fequal (Arg i _ _)(Arg j _ _) = i == j
  fequal (Global x _)(Global y _) = x == y
  fequal (Deref e _) (Deref e' _) = e == e'
  fequal (StructField xr _ xi _) (StructField yr _ yi _) = xi == yi && (xr == yr)
  fequal (ReturnValue _) (ReturnValue _) = True
  fequal _ _ = False

instance CC.OrdFoldable LLVMExprF where
  Arg i _ _  `fcompare` Arg i' _ _   = i `compare` i'
  Arg _ _ _  `fcompare` _            = LT
  _          `fcompare` Arg _ _ _    = GT
  Global n _ `fcompare` Global n' _  = n `compare` n'
  Global _ _ `fcompare` _            = LT
  _          `fcompare` Global _ _   = GT
  Deref e _  `fcompare` Deref e' _   = e `compare` e'
  Deref _ _  `fcompare` _            = LT
  _          `fcompare` Deref _ _    = GT
  StructField r1 _ f1 _ `fcompare` StructField r2 _ f2 _ =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r
  StructField _ _ _ _ `fcompare` _           = LT
  _          `fcompare` StructField _ _ _ _ = GT
  (ReturnValue _) `fcompare` (ReturnValue _) = EQ

instance CC.ShowFoldable LLVMExprF where
  fshow (Arg _ nm _) = show nm
  fshow (Global nm _) = show nm
  fshow (Deref e _) = "*(" ++ show e ++ ")"
  fshow (StructField r _ f _) = show r ++ "." ++ show f
  fshow (ReturnValue _) = "return"

-- | Typechecked LLVMExpr
type LLVMExpr = CC.Term LLVMExprF

-- | Pretty print a LLVM expression.
ppLLVMExpr :: LLVMExpr -> Doc
ppLLVMExpr (CC.Term exprF) =
  case exprF of
    Arg _ nm _ -> LSS.ppIdent nm
    Global nm _ -> LSS.ppSymbol nm
    Deref e _ -> PP.char '*' <> PP.parens (ppLLVMExpr e)
    StructField r _ f _ -> ppLLVMExpr r <> PP.char '.' <> text (show f)
    ReturnValue _ -> text "return"

-- | Returns LSS Type of LLVMExpr
lssTypeOfLLVMExpr :: LLVMExpr -> LSS.MemType
lssTypeOfLLVMExpr (CC.Term exprF) =
  case exprF of
    Arg _ _ tp -> tp
    Global _ tp -> tp
    Deref _ tp -> tp
    StructField _ _ _ tp -> tp
    ReturnValue tp -> tp

updateLLVMExprType :: LLVMExpr -> LSS.MemType -> LLVMExpr
updateLLVMExprType (CC.Term exprF) tp = CC.Term $
  case exprF of
    Arg i n _ -> Arg i n tp
    Global n _ -> Global n tp
    Deref e _ -> Deref e tp
    StructField r si i _ -> StructField r si i tp
    ReturnValue _ -> ReturnValue tp

-- | Returns true if expression is a pointer.
isPtrLLVMExpr :: LLVMExpr -> Bool
isPtrLLVMExpr e =
  case lssTypeOfLLVMExpr e of
    LSS.PtrType _ -> True
    _ -> False

isArgLLVMExpr :: LLVMExpr -> Bool
isArgLLVMExpr (CC.Term (Arg _ _ _)) = True
isArgLLVMExpr _ = False

-- LogicExpr {{{1

newtype LogicExpr = LogicExpr (SharedTerm SAWCtx)
  deriving (Show)

mkLogicExpr :: SharedTerm SAWCtx -> LogicExpr
mkLogicExpr = LogicExpr

useLogicExpr :: SharedContext SAWCtx -> LogicExpr -> IO (SharedTerm SAWCtx)
useLogicExpr _ (LogicExpr t) = return t

-- MixedExpr {{{1

-- | A logic or LLVM expression.
data MixedExpr
  = LogicE LogicExpr
  | LLVME LLVMExpr
  deriving (Show)

-- | Identifies concrete type of a LLVM expression. We can use normal
-- LLVM types to encode precise, actual types.
type LLVMActualType = LSS.MemType

isPrimitiveType :: LLVMActualType -> Bool
isPrimitiveType (LSS.IntType _) = True
isPrimitiveType LSS.FloatType = True
isPrimitiveType LSS.DoubleType = True
isPrimitiveType _ = False

instance Eq LSS.MemType where
  (LSS.IntType bw) == (LSS.IntType bw') = bw == bw'
  (LSS.PtrType (LSS.MemType mt)) == (LSS.PtrType (LSS.MemType mt')) = mt == mt'
  LSS.FloatType == LSS.FloatType = True
  LSS.DoubleType == LSS.DoubleType = True
  (LSS.ArrayType n t) == (LSS.ArrayType n' t') = n == n' && (t == t')
  (LSS.VecType n t) == (LSS.VecType n' t') = n == n' && (t == t')
  (LSS.StructType si) == (LSS.StructType si') = si == si'
  _ == _ = False

-- FIXME: not sure this is really the right way to go
instance Eq LSS.StructInfo where
  si == si' = LSS.siFields si == LSS.siFields si'

instance Eq LSS.FieldInfo where
  fi == fi' = LSS.fiOffset fi == LSS.fiOffset fi' &&
              LSS.fiType fi == LSS.fiType fi' &&
              LSS.fiPadding fi == LSS.fiPadding fi'

-- | Returns true if this represents a reference.
isActualPtr :: LLVMActualType -> Bool
isActualPtr (LSS.PtrType _) = True
isActualPtr (LSS.ArrayType _ _) = True
isActualPtr _ = False

-- | Returns LLVM symbolic simulator type that actual type represents.
lssTypeOfActual :: LLVMActualType -> LSS.MemType
lssTypeOfActual = id

-- | Returns logical type of actual type if it is an array or primitive type.
logicTypeOfActual :: SharedContext s -> LLVMActualType
                  -> IO (Maybe (SharedTerm s))
logicTypeOfActual sc (LSS.IntType w) = do
  bType <- scBoolType sc
  lTm <- scNat sc (fromIntegral w)
  Just <$> scVecType sc lTm bType
logicTypeOfActual sc LSS.FloatType = Just <$> scPrelude_Float sc
logicTypeOfActual sc LSS.DoubleType = Just <$> scPrelude_Double sc
logicTypeOfActual sc (LSS.ArrayType n ty) = do
  melTyp <- logicTypeOfActual sc ty
  case melTyp of
    Just elTyp -> do
      lTm <- scNat sc (fromIntegral n)
      Just <$> scVecType sc lTm elTyp
    Nothing -> return Nothing
logicTypeOfActual sc (LSS.PtrType _) =
  -- TODO: this is hardcoded to 32-bit pointers
  Just <$> scBitvector sc (4 * 8)
logicTypeOfActual _ _ = return Nothing

-- | Returns Cryptol type of actual type if it is an array or primitive type.
cryptolTypeOfActual :: LLVMActualType -> Maybe Cryptol.Type
cryptolTypeOfActual (LSS.IntType w) =
  Just $ Cryptol.tSeq (Cryptol.tNum w) Cryptol.tBit
cryptolTypeOfActual (LSS.ArrayType n ty) = do
  elty <- cryptolTypeOfActual ty
  return $ Cryptol.tSeq (Cryptol.tNum n) elty
cryptolTypeOfActual (LSS.PtrType _) =
  -- TODO: this is hardcoded to 32-bit pointers
  Just $ Cryptol.tSeq (Cryptol.tNum (4 * 8 :: Integer)) Cryptol.tBit
cryptolTypeOfActual _ = Nothing

ppActualType :: LLVMActualType -> Doc
ppActualType = LSS.ppMemType
