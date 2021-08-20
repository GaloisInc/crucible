------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.QQ
-- Description      : QuasiQuoters for a subset of LLVM assembly syntax
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.LLVM.QQ
 ( llvmType
 , llvmDecl
 , llvmOvr
 ) where

import Control.Monad (void)
import qualified Data.Attoparsec.Text as AT
import Data.Char
import Data.Data
import Data.Int
import qualified Data.Text as T
import qualified Text.LLVM.AST as L

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import qualified Data.Parameterized.Context as Ctx
import           Lang.Crucible.Types
import qualified Lang.Crucible.LLVM.Intrinsics.Common as IC
import           Lang.Crucible.LLVM.Types

-- | This type closely mirrors the type syntax from llvm-pretty,
--   but adds several additional constructors to represent
--   quasiquoter metavariables.
data QQType
  = QQVar String     -- ^ This constructor represents a type metavariable, e.g. @$var@
  | QQIntVar String  -- ^ This constructor represents a integer type metavariable, e.g. @#var@
  | QQSizeT          -- ^ This constructor represents an integer type that is the same width as a pointer
  | QQSSizeT          -- ^ This constructor represents a signed integer type that is the same width as a pointer
  | QQPrim L.PrimType
  | QQPtrTo QQType
  | QQAlias L.Ident
  | QQArray Int32 QQType
  | QQFunTy QQType [QQType] Bool
  | QQStruct [QQType]
  | QQPackedStruct [QQType]
  | QQVector Int32 QQType
  | QQOpaque
 deriving (Show, Eq, Ord, Data)

-- | This type closely mirrors the function declaration syntax from llvm-pretty,
--   except that the types and the name of the declaration may be metavarables.
data QQDeclare =
  QQDeclare
  { qqDecRet     :: QQType
  , qqDecName    :: Either String L.Symbol -- ^ a @Left@ value is a metavariable; @Right@ is a symbol
  , qqDecArgs    :: [QQType]
  , qqDecVarArgs :: Bool
  }
 deriving (Show, Eq, Ord, Data)

parseIdent :: AT.Parser L.Ident
parseIdent = L.Ident <$> (AT.char '%' *> AT.choice
  [ T.unpack <$> AT.takeWhile1 isDigit
  , (:) <$> AT.satisfy (AT.inClass "-a-zA-Z$._")
        <*> (T.unpack <$> (AT.takeWhile (AT.inClass "-a-zA-Z$._0-9")))
  ])


parseSymbol :: AT.Parser L.Symbol
parseSymbol = L.Symbol <$> (AT.char '@' *>
  ( (:) <$> AT.satisfy (AT.inClass "-a-zA-Z$._")
        <*> (T.unpack <$> (AT.takeWhile (AT.inClass "-a-zA-Z$._0-9")))
  ))

parseFloatType :: AT.Parser L.FloatType
parseFloatType = AT.choice
  [ pure L.Half      <* AT.string "half"
  , pure L.Float     <* AT.string "float"
  , pure L.Double    <* AT.string "double"
  , pure L.Fp128     <* AT.string "fp128"
  , pure L.X86_fp80  <* AT.string "x86_fp80"
  , pure L.PPC_fp128 <* AT.string "ppc_fp128"
  ]

parsePrimType :: AT.Parser L.PrimType
parsePrimType = AT.choice
  [ pure L.Label    <* AT.string "label"
  , pure L.Void     <* AT.string "void"
  , pure L.Metadata <* AT.string "metadata"
  , pure L.X86mmx   <* AT.string "x86_mmx"
  , L.Integer <$> (AT.char 'i' *> AT.decimal)
  , L.FloatType <$> parseFloatType
  ]

parseSeqType ::
  Char ->
  Char ->
  (Int32 -> QQType -> QQType) ->
  AT.Parser QQType
parseSeqType start end cnstr =
  do void $ AT.char start
     AT.skipSpace
     n <- AT.decimal
     AT.skipSpace
     void $ AT.char 'x'
     AT.skipSpace
     tp <- parseType
     AT.skipSpace
     void $ AT.char end
     return $! cnstr n tp

parseCommaSeparatedTypes :: AT.Parser [QQType]
parseCommaSeparatedTypes = AT.choice
  [ do AT.skipSpace
       f  <- parseType
       fs <- AT.many' (AT.skipSpace *> AT.char ',' *> AT.skipSpace *> parseType)
       return (f:fs)
  , return []
  ]

parseStructType :: AT.Parser QQType
parseStructType =
  do void $ AT.char '{'
     fs <- parseCommaSeparatedTypes
     AT.skipSpace
     void $ AT.char '}'
     return $ QQStruct fs

parsePackedStructType :: AT.Parser QQType
parsePackedStructType =
  do void $ AT.string "<{"
     fs <- parseCommaSeparatedTypes
     AT.skipSpace
     void $ AT.string "}>"
     return $ QQPackedStruct fs

parseArgList :: AT.Parser ([QQType], Bool)
parseArgList =
  do void $ AT.char '('
     tps <- parseCommaSeparatedTypes
     AT.skipSpace
     varargs <- AT.choice
                [ do void $ AT.char ','
                     AT.skipSpace
                     void $ AT.string "..."
                     AT.skipSpace
                     void $ AT.char ')'
                     return True
                , do void $ AT.char ')'
                     return False
                ]
     return (tps, varargs)

parseVar :: AT.Parser String
parseVar = T.unpack <$> (AT.char '$' *> AT.takeWhile1 varChar)
 where
 varChar c = isAlpha c || isDigit c || c == '\'' || c == '_'

parseIntVar :: AT.Parser String
parseIntVar = T.unpack <$> (AT.char '#' *> AT.takeWhile1 varChar)
 where
 varChar c = isAlpha c || isDigit c || c == '\'' || c == '_'

parseType :: AT.Parser QQType
parseType =
  do base <- AT.choice
             [ parseSeqType '<' '>' QQVector
             , parseSeqType '[' ']' QQArray
             , parseStructType
             , parsePackedStructType
             , QQVar <$> parseVar
             , QQIntVar <$> parseIntVar
             , QQAlias <$> parseIdent
             , QQPrim <$> parsePrimType
             , pure QQOpaque <* AT.string "opaque"
             , pure QQSizeT  <* AT.string "size_t"
             , pure QQSSizeT  <* AT.string "ssize_t"
             ]
     base' <- AT.choice
              [ do AT.skipSpace
                   (args,varargs) <- parseArgList
                   return (QQFunTy base args varargs)
              , return base
              ]
     parseStars base'

  where
  parseStars x =
    AT.choice
    [ do AT.skipSpace
         void $ AT.char '*'
         parseStars (QQPtrTo x)
    , return x
    ]

parseDeclare :: AT.Parser QQDeclare
parseDeclare =
  do AT.skipSpace
     ret <- parseType
     AT.skipSpace
     sym <- AT.eitherP parseVar parseSymbol
     AT.skipSpace
     (args, varargs) <- parseArgList
     AT.skipSpace
     return
       QQDeclare
       { qqDecRet     = ret
       , qqDecName    = sym
       , qqDecArgs    = args
       , qqDecVarArgs = varargs
       }


liftQQType :: QQType -> Q Exp
liftQQType tp =
  case tp of
    QQVar nm     -> varE (mkName nm)
    QQIntVar nm  -> [| L.PrimType (L.Integer (fromInteger (intValue $(varE (mkName nm)) ))) |]
    QQSizeT      -> varE 'IC.llvmSizeT
    QQSSizeT      -> varE 'IC.llvmSSizeT
    QQAlias nm   -> [| L.Alias $(dataToExpQ (const Nothing) nm) |]
    QQPrim pt    -> [| L.PrimType $(dataToExpQ (const Nothing) pt) |]
    QQPtrTo t    -> [| L.PtrTo $(liftQQType t) |]
    QQArray n t  -> [| L.Array n $(liftQQType t) |]
    QQVector n t -> [| L.Vector n $(liftQQType t) |]
    QQStruct ts  -> [| L.Struct $(listE (map liftQQType ts)) |]
    QQPackedStruct ts -> [| L.PackedStruct $(listE (map liftQQType ts)) |]
    QQOpaque -> [| L.Opaque |]
    QQFunTy ret args varargs -> [| L.FunTy $(liftQQType ret) $(listE (map liftQQType args)) $(lift varargs) |]

liftQQDecl :: QQDeclare -> Q Exp
liftQQDecl (QQDeclare ret nm args varargs) =
   [| L.Declare
      { L.decLinkage = Nothing
      , L.decVisibility = Nothing
      , L.decRetType = $(liftQQType ret)
      , L.decName    = $(f nm)
      , L.decArgs    = $(listE (map liftQQType args))
      , L.decVarArgs = $(lift varargs)
      , L.decAttrs   = []
      , L.decComdat  = Nothing
      }
    |]
  where
  f (Left v)    = varE (mkName v)
  f (Right sym) = dataToExpQ (const Nothing) sym

liftKnownNat :: Integral a => a -> Q Exp
liftKnownNat n = [| knownNat @ $(litT (numTyLit (toInteger n))) |]

liftTypeRepr :: QQType -> Q Exp
liftTypeRepr t = case t of
    QQVar nm      -> varE (mkName (nm++"_repr"))
    QQIntVar nm   -> [| BVRepr $(varE (mkName nm)) |]
    QQSizeT       -> [| SizeT |]
    QQSSizeT      -> [| SSizeT |]
    QQPrim pt     -> liftPrim pt
    QQPtrTo _t    -> [| PtrRepr |]
    QQArray _ t'  -> [| VectorRepr $(liftTypeRepr t') |]
    QQVector _ t' -> [| VectorRepr $(liftTypeRepr t') |]
    QQStruct ts   -> [| StructRepr $(liftArgs ts False) |]
    QQPackedStruct ts -> [| StructRepr $(liftArgs ts False) |]
    QQAlias{} -> fail "Cannot lift alias type to repr"
    QQOpaque  -> fail "Cannot lift opaque type to repr"
    QQFunTy{} -> fail "Cannot lift function type to repr"
 where
  liftPrim pt = case pt of
    L.Void         -> [| UnitRepr |]
    L.Integer n    -> [| BVRepr $(liftKnownNat n) |]
    L.FloatType ft -> [| FloatRepr $(liftFloatType ft) |]
    L.Label    -> fail "Cannot lift label type to repr"
    L.X86mmx   -> fail "Cannot lift X86mmx type to repr"
    L.Metadata -> fail "Cannot lift metatata type to repr"

  liftFloatType ft = case ft of
    L.Half      -> [| HalfFloatRepr |]
    L.Float     -> [| SingleFloatRepr |]
    L.Double    -> [| DoubleFloatRepr |]
    L.Fp128     -> [| QuadFloatRepr |]
    L.X86_fp80  -> [| X86_80FloatRepr |]
    L.PPC_fp128 -> [| DoubleDoubleFloatRepr|]

liftArgs :: [QQType] -> Bool -> Q Exp
liftArgs = go [| Ctx.Empty |]
 where
 go :: Q Exp -> [QQType] -> Bool -> Q Exp
 go xs [] True  = [| $(xs) Ctx.:> VectorRepr AnyRepr |]
 go xs [] False = xs
 go xs (t:ts) varargs = go [| $(xs) Ctx.:> $(liftTypeRepr t) |] ts varargs


liftQQDeclToOverride :: QQDeclare -> Q Exp
liftQQDeclToOverride qqd@(QQDeclare ret _nm args varargs) =
  [| IC.LLVMOverride $(liftQQDecl qqd) $(liftArgs args varargs) $(liftTypeRepr ret) |]

-- | This quasiquoter parses values in LLVM type syntax, extended
--   with metavariables, and builds values of @Text.LLVM.AST.Type@.
--
--   Type metavariables start with a @$@ and splice in the named
--   program variable, which is expected to have type @Type@.
--
--   Numeric metavariables start with @#@ and splice in an integer
--   type whose width is given by the named program variable, which
--   is expected to be a @NatRepr@.
llvmType :: QuasiQuoter
llvmType =
  QuasiQuoter
  { quoteExp = \str ->
       do case AT.parseOnly parseType (T.pack str) of
            Left msg -> error msg
            Right x  -> liftQQType x

  , quotePat = error "llvmType cannot quasiquote a pattern"
  , quoteType = error "llvmType cannot quasiquote a Haskell type"
  , quoteDec = error "llvmType cannot quasiquote a declaration"
  }

-- | This quasiquoter parses values in LLVM function declaration syntax,
--   extended with metavariables, and builds values of @Text.LLVM.AST.Declare@.
--
--   Type metavariables start with a @$@ and splice in the named
--   program variable, which is expected to have type @Type@.
--
--   Numeric metavariables start with @#@ and splice in an integer
--   type whose width is given by the named program variable, which
--   is expected to be a @NatRepr@.
--
--   The name of the declaration may also be a @$@ metavariable, in which
--   case the named variable is expeted to be a @Symbol@.
llvmDecl :: QuasiQuoter
llvmDecl =
  QuasiQuoter
  { quoteExp = \str ->
       do case AT.parseOnly parseDeclare (T.pack str) of
            Left msg -> error msg
            Right x  -> liftQQDecl x

  , quotePat = error "llvmDecl cannot quasiquote a pattern"
  , quoteType = error "llvmDecl cannot quasiquote a Haskell type"
  , quoteDec = error "llvmDecl cannot quasiquote a declaration"
  }

-- | This quasiquoter parses values in LLVM function declaration syntax,
--   extended with metavariables, and partially applies the
--   @LLVMOverride@ constructor so that it expectes a single remaining
--   argument to populate the @llvmOverride_def@ field.
--
--   Type metavariables start with a @$@ and splice in the named
--   program variable, which is expected to have type @Type@.
--   In addition a related variable must be in scope to give the
--   crucible @TypeRepr@ associated.  For example variable @$x@
--   should be a LLVM @Type@ and @$x_repr@ should be a Crucible @TypeRepr@.
--
--   Numeric metavariables start with @#@ and splice in an integer
--   type whose width is given by the named program variable, which
--   is expected to be a @NatRepr@.  Both the LLVM type and the Crucible
--   @TypeRepr@ are built from the @NatRepr@.
--
--   The name of the declaration may also be a @$@ metavariable, in which
--   case the named variable is expeted to be a @Symbol@.
llvmOvr :: QuasiQuoter
llvmOvr =
  QuasiQuoter
  { quoteExp = \str ->
       do case AT.parseOnly parseDeclare (T.pack str) of
            Left msg -> error msg
            Right x  -> liftQQDeclToOverride x

  , quotePat = error "llvmOvr cannot quasiquote a pattern"
  , quoteType = error "llvmOvr cannot quasiquote a Haskell type"
  , quoteDec = error "llvmOvr cannot quasiquote a declaration"
  }
