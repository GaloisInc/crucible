{-# LANGUAGE LambdaCase, OverloadedStrings #-}
-- | Atoms used by the Crucible CFG concrete syntax.
module Lang.Crucible.Syntax.Atoms
  (
    -- * The atom datatype
    Atomic(..)
  , atom
    -- * Individual atoms
  , AtomName(..)
  , LabelName(..)
  , RegName(..)
  , FunName(..)
  , GlobalName(..)
  , Keyword(..)
  ) where

import Control.Applicative

import Data.Char
import Data.Functor
import Data.Ratio
import Data.Text (Text)
import qualified Data.Text as T

import Lang.Crucible.Syntax.SExpr
import Numeric

import Text.Megaparsec as MP hiding (many, some)
import Text.Megaparsec.Char

-- | The name of an atom (non-keyword identifier)
newtype AtomName = AtomName Text deriving (Eq, Ord, Show)
-- | The name of a label (identifier followed by colon)
newtype LabelName = LabelName Text deriving (Eq, Ord, Show)
-- | The name of a register (dollar sign followed by identifier)
newtype RegName = RegName Text deriving (Eq, Ord, Show)
-- | The name of a function (at-sign followed by identifier)
newtype FunName = FunName Text deriving (Eq, Ord, Show)
-- | The name of a global variable (two dollar signs followed by identifier)
newtype GlobalName = GlobalName Text deriving (Eq, Ord, Show)

-- | Individual language keywords (reserved identifiers)
data Keyword = Defun | DefBlock | DefGlobal
             | Registers
             | Start
             | SetGlobal
             | SetRef | DropRef_
             | Plus | Minus | Times | Div | Negate | Abs
             | Just_ | Nothing_ | FromJust
             | Inj | Proj
             | AnyT | UnitT | BoolT | NatT | IntegerT | RealT | ComplexRealT | CharT | StringT
             | BitvectorT | VectorT | FPT | FunT | MaybeT | VariantT | RefT
             | Half_ | Float_ | Double_ | Quad_ | X86_80_ | DoubleDouble_
             | Unicode_ | Char8_ | Char16_
             | The
             | Equalp | Integerp
             | If
             | Not_ | And_ | Or_ | Xor_
             | Mod
             | Lt | Le
             | Show
             | StringConcat_ | StringEmpty_ | StringLength_
             | ToAny | FromAny
             | VectorLit_ | VectorReplicate_ | VectorIsEmpty_ | VectorSize_
             | VectorGetEntry_ | VectorSetEntry_ | VectorCons_
             | Deref | Ref | EmptyRef
             | Jump_ | Return_ | Branch_ | MaybeBranch_ | TailCall_ | Error_ | Output_ | Case
             | Print_ | PrintLn_
             | Let | Fresh
             | Assert_ | Assume_
             | SetRegister
             | Funcall
             | Breakpoint_
             | BV | BVConcat_ | BVSelect_ | BVTrunc_
             | BVZext_ | BVSext_ | BVNonzero_ | BoolToBV_
             | BVCarry_ | BVSCarry_ | BVSBorrow_
             | BVNot_ | BVAnd_ | BVOr_ | BVXor_ | BVShl_ | BVLshr_ | BVAshr_
             | Sle | Slt | Sdiv | Smod | ZeroExt | SignExt
             | RNE_ | RNA_ | RTP_ | RTN_ | RTZ_
             | FPToUBV_ | FPToSBV_ | UBVToFP_ | SBVToFP_ | BinaryToFP_ | FPToBinary_
             | FPToReal_ | RealToFP_
  deriving (Eq, Ord)

keywords :: [(Text, Keyword)]
keywords =
    -- function/block defintion
  [ ("defun" , Defun)
  , ("start" , Start)
  , ("defblock", DefBlock)
  , ("defglobal", DefGlobal)
  , ("registers", Registers)

    -- statements
  , ("let", Let)
  , ("set-global!", SetGlobal)
  , ("set-ref!", SetRef)
  , ("drop-ref!", DropRef_)
  , ("fresh", Fresh)
  , ("jump" , Jump_)
  , ("case", Case)
  , ("return" , Return_)
  , ("branch" , Branch_)
  , ("maybe-branch" , MaybeBranch_)
  , ("tail-call" , TailCall_)
  , ("error", Error_)
  , ("output", Output_)
  , ("print" , Print_)
  , ("println" , PrintLn_)
  , ("Ref", RefT)
  , ("deref", Deref)
  , ("ref", Ref)
  , ("empty-ref", EmptyRef)
  , ("set-register!", SetRegister)
  , ("assert!", Assert_)
  , ("assume!", Assume_)
  , ("funcall", Funcall)
  , ("breakpoint", Breakpoint_)

    -- types
  , ("Any" , AnyT)
  , ("Unit" , UnitT)
  , ("Bool" , BoolT)
  , ("Nat" , NatT)
  , ("Integer" , IntegerT)
  , ("FP", FPT)
  , ("Real" , RealT)
  , ("ComplexReal" , ComplexRealT)
  , ("Char" , CharT)
  , ("String" , StringT)
  , ("Bitvector" , BitvectorT)
  , ("Vector", VectorT)
  , ("->", FunT)
  , ("Maybe", MaybeT)
  , ("Variant", VariantT)

    -- string sorts
  , ("Unicode", Unicode_)
  , ("Char16", Char16_)
  , ("Char8", Char8_)

    -- floating-point variants
  , ("Half", Half_)
  , ("Float", Float_)
  , ("Double", Double_)
  , ("Quad", Quad_)
  , ("X86_80", X86_80_)
  , ("DoubleDouble", DoubleDouble_)

    -- misc
  , ("the" , The)
  , ("equal?" , Equalp)
  , ("if" , If)

    -- ANY types
  , ("to-any", ToAny)
  , ("from-any", FromAny)

    -- booleans
  , ("not" , Not_)
  , ("and" , And_)
  , ("or" , Or_)
  , ("xor" , Xor_)

    -- arithmetic
  , ("+" , Plus)
  , ("-" , Minus)
  , ("*" , Times)
  , ("/" , Div)
  , ("<" , Lt)
  , ("<=" , Le)
  , ("<=$" , Sle)
  , ("<$" , Slt)
  , ("/$" , Sdiv)
  , ("smod", Smod)
  , ("negate", Negate)
  , ("abs", Abs)
  , ("mod" , Mod)
  , ("integer?" , Integerp)

    -- Variants
  , ("inj", Inj)
  , ("proj", Proj)

    -- Maybe
  , ("just" , Just_)
  , ("nothing" , Nothing_)
  , ("from-just" , FromJust)

    -- Vectors
  , ("vector", VectorLit_)
  , ("vector-replicate", VectorReplicate_)
  , ("vector-empty?", VectorIsEmpty_)
  , ("vector-size", VectorSize_)
  , ("vector-get", VectorGetEntry_)
  , ("vector-set", VectorSetEntry_)
  , ("vector-cons", VectorCons_)

    -- strings
  , ("show", Show)
  , ("string-concat", StringConcat_)
  , ("string-empty", StringEmpty_)
  , ("string-length", StringLength_)

    -- bitvector
  , ("bv", BV)
  , ("bv-concat", BVConcat_)
  , ("bv-select", BVSelect_)
  , ("bv-trunc", BVTrunc_)
  , ("zero-extend", BVZext_)
  , ("sign-extend", BVSext_)
  , ("bv-nonzero", BVNonzero_)
  , ("bool-to-bv", BoolToBV_)
  , ("bv-carry", BVCarry_)
  , ("bv-scarry", BVSCarry_)
  , ("bv-sborrow", BVSBorrow_)
  , ("bv-not", BVNot_)
  , ("bv-and", BVAnd_)
  , ("bv-or", BVOr_)
  , ("bv-xor", BVXor_)
  , ("shl", BVShl_)
  , ("lshr", BVLshr_)
  , ("ashr", BVAshr_)

    -- floating-point
  , ("fp-to-ubv", FPToUBV_)
  , ("fp-to-sbv", FPToSBV_)
  , ("ubv-to-fp", UBVToFP_)
  , ("sbv-to-fp", SBVToFP_)
  , ("fp-to-binary", FPToBinary_)
  , ("binary-to-fp", BinaryToFP_)
  , ("real-to-fp", RealToFP_)
  , ("fp-to-real", FPToReal_)
  , ("rne" , RNE_)
  , ("rna" , RNA_)
  , ("rtp" , RTP_)
  , ("rtn" , RTN_)
  , ("rtz" , RTZ_)
  ]

instance Show Keyword where
  show k = case [str | (str, k') <- keywords, k == k'] of
             [] -> "UNKNOWN KW"
             (s:_) -> T.unpack s


-- | The atoms of the language
data Atomic = Kw !Keyword -- ^ Keywords are all the built-in operators and expression formers
            | Lbl !LabelName -- ^ Labels, but not the trailing colon
            | At !AtomName -- ^ Atom names (which look like Scheme symbols)
            | Rg !RegName -- ^ Registers, whose names have a leading single $
            | Gl !GlobalName -- ^ Global variables, whose names have a leading double $$
            | Fn !FunName -- ^ Function names, minus the leading @
            | Int !Integer -- ^ Literal integers
            | Rat !Rational -- ^ Literal rational numbers
            | Bool !Bool   -- ^ Literal Booleans
            | StrLit !Text -- ^ Literal strings
  deriving (Eq, Ord, Show)


instance IsAtom Atomic where
  showAtom (Kw s) = T.pack (show s)
  showAtom (Lbl (LabelName l)) = l <> ":"
  showAtom (Rg (RegName r)) = "$" <> r
  showAtom (Gl (GlobalName r)) = "$$" <> r
  showAtom (At (AtomName a)) = a
  showAtom (Fn (FunName a)) = "@" <> a
  showAtom (Int i) = T.pack (show i)
  showAtom (Rat r) = T.pack (show (numerator r) ++ "/" ++ show (denominator r))
  showAtom (Bool b) = if b then "#t" else "#f"
  showAtom (StrLit s) = T.pack $ show s

-- | Parse an atom
atom :: Parser Atomic
atom =  try (Lbl . LabelName <$> identifier <* char ':')
    <|> Fn . FunName <$> (char '@' *> identifier)
    <|> (char '$' *> ((char '$' *> (Gl . GlobalName <$> identifier)) <|> Rg . RegName <$> identifier))
    <|> try (mkNum <$> signedPrefixedNumber <*> ((Just <$> (try (char '/') *> prefixedNumber)) <|> pure Nothing))
    <|> kwOrAtom
    <|> char '#' *>  ((char 't' <|> char 'T') $> Bool True <|> (char 'f' <|> char 'F') $> Bool False)
    <|> char '"' *> (StrLit . T.pack <$> stringContents)
  where
    mkNum x Nothing = Int x
    mkNum x (Just y) = Rat (x % y)

stringContents :: Parser [Char]
stringContents =  (char '\\' *> ((:) <$> escapeChar <*> stringContents))
              <|> (char '"' $> [])
              <|> ((:) <$> satisfy (const True) <*> stringContents)

escapeChar :: Parser Char
escapeChar =  (char '\\' *> pure '\\')
          <|> (char '"' *> pure '"')
          <|> (char 'n' *> pure '\n')
          <|> (char 't' *> pure '\t')
          <?> "valid escape character"

kwOrAtom :: Parser Atomic
kwOrAtom = do x <- identifier
              return $ maybe (At (AtomName x)) Kw (lookup x keywords)


signedPrefixedNumber :: (Eq a, Num a) => Parser a
signedPrefixedNumber =
  char '+' *> prefixedNumber <|>
  char '-' *> (negate <$> prefixedNumber) <|>
  prefixedNumber

prefixedNumber :: (Eq a, Num a) => Parser a
prefixedNumber = try (char '0' *> maybehex) <|> decimal
  where decimal = fromInteger . read <$> some (satisfy isDigit <?> "decimal digit")
        maybehex = char 'x' *> hex <|> return 0
        hex = reading $ readHex <$> some (satisfy (\c -> isDigit c || elem c ("abcdefABCDEF" :: String)) <?> "hex digit")
        reading p =
          p >>=
            \case
              [(x, "")] -> pure x
              _ -> empty
