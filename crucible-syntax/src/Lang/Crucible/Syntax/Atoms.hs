{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module Lang.Crucible.Syntax.Atoms where

import Control.Applicative

import Data.Char
import Data.Functor
import Data.Monoid
import Data.Ratio
import Data.Text (Text)
import qualified Data.Text as T

import Lang.Crucible.Syntax.SExpr
import Numeric

import Text.Megaparsec as MP hiding (many, some)
import Text.Megaparsec.Char


newtype AtomName = AtomName Text deriving (Eq, Ord, Show)
newtype LabelName = LabelName Text deriving (Eq, Ord, Show)
newtype RegName = RegName Text deriving (Eq, Ord, Show)
newtype FunName = FunName Text deriving (Eq, Ord, Show)
newtype GlobalName = GlobalName Text deriving (Eq, Ord, Show)

data Keyword = Defun | DefBlock | DefGlobal
             | Registers
             | Start
             | SetGlobal
             | SetRef | DropRef_
             | Unpack
             | Plus | Minus | Times | Div
             | Just_ | Nothing_ | FromJust
             | Inj
             | AnyT | UnitT | BoolT | NatT | IntegerT | RealT | ComplexRealT | CharT | StringT
             | BitVectorT | VectorT | FunT | MaybeT | VariantT | RefT
             | The
             | Equalp | Integerp
             | If
             | Pack
             | Not_ | And_ | Or_ | Xor_
             | Mod
             | Lt
             | Show
             | StringAppend
             | ToAny | FromAny
             | VectorLit_ | VectorReplicate_ | VectorIsEmpty_ | VectorSize_
             | VectorGetEntry_ | VectorSetEntry_ | VectorCons_
             | Deref | Ref | EmptyRef
             | Jump_ | Return_ | Branch_ | MaybeBranch_ | TailCall_ | Error_ | Output_ | Case
             | Print_
             | Let
             | Assert_
             | SetRegister
             | Funcall
  deriving (Eq, Ord)

keywords :: [(Text, Keyword)]
keywords =
  [ ("defun" , Defun)
  , ("defblock", DefBlock)
  , ("defglobal", DefGlobal)
  , ("registers", Registers)
  , ("let", Let)
  , ("set-global!", SetGlobal)
  , ("set-ref!", SetRef)
  , ("drop-ref!", DropRef_)
  , ("start" , Start)
  , ("unpack" , Unpack)
  , ("+" , Plus)
  , ("-" , Minus)
  , ("*" , Times)
  , ("/" , Div)
  , ("<" , Lt)
  , ("show", Show)
  , ("inj", Inj)
  , ("just" , Just_)
  , ("nothing" , Nothing_)
  , ("from-just" , FromJust)
  , ("to-any", ToAny)
  , ("from-any", FromAny)
  , ("the" , The)
  , ("equal?" , Equalp)
  , ("integer?" , Integerp)
  , ("Any" , AnyT)
  , ("Unit" , UnitT)
  , ("Bool" , BoolT)
  , ("Nat" , NatT)
  , ("Integer" , IntegerT)
  , ("Real" , RealT)
  , ("ComplexReal" , ComplexRealT)
  , ("Char" , CharT)
  , ("String" , StringT)
  , ("BitVector" , BitVectorT)
  , ("Vector", VectorT)
  , ("->", FunT)
  , ("Maybe", MaybeT)
  , ("Variant", VariantT)
  , ("vector", VectorLit_)
  , ("vector-replicate", VectorReplicate_)
  , ("vector-empty?", VectorIsEmpty_)
  , ("vector-size", VectorSize_)
  , ("vector-get", VectorGetEntry_)
  , ("vector-set", VectorSetEntry_)
  , ("vector-cons", VectorCons_)
  , ("if" , If)
  , ("pack" , Pack)
  , ("not" , Not_)
  , ("and" , And_)
  , ("or" , Or_)
  , ("xor" , Xor_)
  , ("mod" , Mod)
  , ("jump" , Jump_)
  , ("case", Case)
  , ("return" , Return_)
  , ("branch" , Branch_)
  , ("maybe-branch" , MaybeBranch_)
  , ("tail-call" , TailCall_)
  , ("error", Error_)
  , ("output", Output_)
  , ("print" , Print_)
  , ("string-append", StringAppend)
  , ("Ref", RefT)
  , ("deref", Deref)
  , ("ref", Ref)
  , ("empty-ref", EmptyRef)
  , ("set-register!", SetRegister)
  , ("assert!", Assert_)
  , ("funcall", Funcall)
  ]


instance Show Keyword where
  show k = case [str | (str, k') <- keywords, k == k'] of
             [] -> "UNKNOWN KW"
             (s:_) -> T.unpack s


data Atomic = Kw Keyword -- ^ Keywords are all the built-in operators and expression formers
            | Lbl LabelName -- ^ Labels, but not the trailing colon
            | At AtomName -- ^ Atom names (which look like Scheme symbols)
            | Rg RegName -- ^ Registers, whose names have a leading single $
            | Gl GlobalName -- ^ Global variables, whose names have a leading double $$
            | Fn FunName -- ^ Function names, minus the leading @
            | Int Integer -- ^ Literal integers
            | Rat Rational -- ^ Literal rational numbers
            | Bool Bool   -- ^ Literal Booleans
            | StrLit Text -- ^ Literal strings
  deriving (Eq, Ord, Show)


instance IsAtom Atomic where
  showAtom (Kw s) = T.pack (show s)
  showAtom (Lbl (LabelName l)) = l <> ":"
  showAtom (Rg (RegName r)) = "$" <> r
  showAtom (Gl (GlobalName r)) = "$$" <> r
  showAtom (At (AtomName a)) = a
  showAtom (Fn (FunName a)) = "@" <> a
  showAtom (Int i) = T.pack (show i)
  showAtom (Rat r) = T.pack (show r)
  showAtom (Bool b) = if b then "#t" else "#f"
  showAtom (StrLit s) = T.pack $ show s

atom :: Parser Atomic
atom =  try (Lbl . LabelName <$> (identifier) <* char ':')
    <|> kwOrAtom
    <|> Fn . FunName <$> (char '@' *> identifier)
    <|> (char '$' *> ((char '$' *> (Gl . GlobalName <$> identifier)) <|> Rg . RegName <$> identifier))
    <|> try (Int . fromInteger <$> signedPrefixedNumber)
    <|> Rat <$> ((%) <$> signedPrefixedNumber <* char '/' <*> prefixedNumber)
    <|> char '#' *>  ((char 't' <|> char 'T') $> Bool True <|> (char 'f' <|> char 'F') $> Bool False)
    <|> char '"' *> (StrLit . T.pack <$> stringContents)


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
prefixedNumber = try (char '0' *> hexOrOct) <|> decimal
  where decimal = fromInteger . read <$> some (satisfy isDigit <?> "decimal digit")
        hexOrOct = char 'x' *> hex <|> oct <|> return 0
        hex = reading $ readHex <$> some (satisfy (\c -> isDigit c || elem c ("abcdefABCDEF" :: String)) <?> "hex digit")
        oct = reading $ readOct <$> some (satisfy (\c -> elem c ("01234567" :: String)) <?> "octal digit")
        reading p =
          p >>=
            \case
              [(x, "")] -> pure x
              _ -> empty
