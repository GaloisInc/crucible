{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module Lang.Crucible.Syntax.Atoms where

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


newtype AtomName = AtomName Text deriving (Eq, Ord, Show)
newtype LabelName = LabelName Text deriving (Eq, Ord, Show)
newtype RegName = RegName Text deriving (Eq, Ord, Show)
newtype FunName = FunName Text deriving (Eq, Ord, Show)


data Keyword = Defun | DefBlock
             | Start
             | Unpack
             | Plus | Minus | Times | Div
             | Just_ | Nothing_ | FromJust
             | AnyT | UnitT | BoolT | NatT | IntegerT | RealT | ComplexRealT | CharT | StringT
             | BitVectorT
             | The
             | Equalp | Integerp
             | If
             | Pack
             | Not_ | And_ | Or_ | Xor_
             | Mod
             | Lt
             | Jump_ | Return_ | Branch_ | MaybeBranch_ | TailCall_ | Error_ | Output_
             | Print_
             | Let
  deriving (Eq, Ord)

keywords :: [(Text, Keyword)]
keywords =
  [ ("defun" , Defun)
  , ("defblock" , DefBlock)
  , ("let", Let)
  , ("start" , Start)
  , ("unpack" , Unpack)
  , ("+" , Plus)
  , ("-" , Minus)
  , ("*" , Times)
  , ("/" , Div)
  , ("<" , Lt)
  , ("just" , Just_)
  , ("nothing" , Nothing_)
  , ("from-just" , FromJust)
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
  , ("if" , If)
  , ("pack" , Pack)
  , ("not" , Not_)
  , ("and" , And_)
  , ("or" , Or_)
  , ("xor" , Xor_)
  , ("mod" , Mod)
  , ("jump" , Jump_)
  , ("return" , Return_)
  , ("branch" , Branch_)
  , ("maybe-branch" , MaybeBranch_)
  , ("tail-call" , TailCall_)
  , ("error", Error_)
  , ("output", Output_)
  , ("print" , Print_)
  ]


instance Show Keyword where
  show k = case [str | (str, k') <- keywords, k == k'] of
             [] -> "UNKNOWN KW"
             (s:_) -> T.unpack s


data Atomic = Kw Keyword -- keywords are all the built-in operators and expression formers
            | Lbl LabelName -- Labels, but not the trailing colon
            | At AtomName -- Atom names (which look like Scheme symbols)
            | Rg RegName -- Registers, whose names have a leading $
            | Fn FunName -- Function names, minus the leading @
            | Int Integer
            | Rat Rational
            | Bool Bool
  deriving (Eq, Ord, Show)



atom :: Parser Atomic
atom =  try (Lbl . LabelName <$> (T.pack <$> many letter) <* char ':')
    <|> kwOrAtom
    <|> Fn . FunName <$> (char '@' *> identifier)
    <|> Rg . RegName <$> (char '$' *> identifier)
    <|> try (Int . fromInteger <$> signedPrefixedNumber)
    <|> Rat <$> ((%) <$> signedPrefixedNumber <* char '/' <*> prefixedNumber)
    <|> char '#' *>  (char 't' $> Bool True <|> char 'f' $> Bool False)
  where letter = satisfy isLetter

kwOrAtom :: Parser Atomic
kwOrAtom = do x <- identifier
              return $ maybe (At (AtomName x)) Kw (lookup x keywords)


signedPrefixedNumber :: (Eq a, Num a) => Parser a
signedPrefixedNumber =
  char '+' *> prefixedNumber <|>
  char '-' *> (negate <$> prefixedNumber) <|>
  prefixedNumber

prefixedNumber :: (Eq a, Num a) => Parser a
prefixedNumber = char '0' *> hexOrOct <|> decimal
  where decimal = fromInteger . read <$> some (satisfy isDigit <?> "decimal digit")
        hexOrOct = char 'x' *> hex <|> oct <|> return 0
        hex = reading $ readHex <$> some (satisfy (\c -> isDigit c || elem c ("abcdefABCDEF" :: String)) <?> "hex digit")
        oct = reading $ readOct <$> some (satisfy (\c -> elem c ("01234567" :: String)) <?> "octal digit")
        reading p =
          p >>=
            \case
              [(x, "")] -> pure x
              _ -> empty
