{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Syntax.SExpr (pattern A, pattern L, pattern (:::), Syntax(..), Datum(..), Syntactic(..),  Parser, syntaxPos, withPosFrom, sexp, identifier, toText, datumToText, skipWhitespace, PrintRules(..), PrintStyle(..), Layer(..), IsAtom(..)) where

import Data.Char (isDigit, isLetter)
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void
import What4.ProgramLoc as C



import Text.Megaparsec as MP
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.PrettyPrint.ANSI.Leijen as PP

newtype Syntax a = Syntax { unSyntax :: Posd (Layer Syntax a) }
  deriving (Show, Functor)

newtype Datum a = Datum { unDatum :: Layer Datum a}
  deriving (Show, Functor, Eq)

syntaxPos :: Syntax a -> Position
syntaxPos (Syntax (Posd p _)) = p

withPosFrom :: Syntax a -> b -> Posd b
withPosFrom stx x = Posd (syntaxPos stx) x

class Syntactic a b | a -> b where
  syntaxE :: a -> Layer Syntax b

instance Syntactic (Layer Syntax a) a where
  syntaxE = id


instance Syntactic (Syntax a) a where
  syntaxE (Syntax (Posd _ e)) = e

pattern A :: Syntactic a b => b -> a
pattern A x <- (syntaxE -> Atom x)

pattern L :: Syntactic a b => [Syntax b] -> a
pattern L xs <- (syntaxE -> List xs)


pattern (:::) :: Syntactic a b => Syntax b -> [Syntax b] -> a
pattern x ::: xs <- (syntaxE -> List (x : xs))

data Layer f a = List [f a] | Atom a
  deriving (Show, Functor, Eq)


syntaxToDatum :: Syntactic expr atom => expr -> Datum atom
syntaxToDatum (A x) = Datum (Atom x)
syntaxToDatum (L xs) = Datum (List (map syntaxToDatum xs))
syntaxToDatum _ = error "impossible - bad Syntactic instance"

type Parser = Parsec Void Text


skipWhitespace :: Parser ()
skipWhitespace = L.space space1 lineComment blockComment
  where lineComment = L.skipLineComment ";"
        blockComment = L.skipBlockComment "#|" "|#"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme skipWhitespace

withPos :: Parser a -> Parser (Posd a)
withPos p =
  do MP.SourcePos file line col <- getPosition
     let loc = C.SourcePos (T.pack file) (unPos line) (unPos col)
     res <- p
     return $ Posd loc res

symbol :: Text -> Parser Text
symbol = L.symbol skipWhitespace

list :: Parser (Syntax a) -> Parser (Syntax a)
list p =
  do Posd loc _ <- withPos (symbol "(")
     xs <- many p
     _ <- lexeme $ symbol ")"
     return $ Syntax (Posd loc (List xs))

-- | Given a parser for atoms, parse an s-expression that contains them.
sexp :: Parser a -> Parser (Syntax a)
sexp atom =
  (Syntax . fmap Atom <$> lexeme (withPos atom)) <|>
  list (sexp atom)

identifier :: Parser Text
identifier = T.pack <$> identString
  where letterLike x = isLetter x || (elem x ("<>=+-*/!_\\?" :: [Char]))
        nameChar x = letterLike x || isDigit x
        identString = (:) <$> satisfy letterLike <*> many (satisfy nameChar)


data PrintStyle = Special Int
newtype PrintRules a = PrintRules (a -> Maybe PrintStyle)

instance Monoid (PrintRules a) where
  mempty = PrintRules $ const Nothing
  mappend (PrintRules f) (PrintRules g) = PrintRules $ \z -> f z <|> g z


class IsAtom a where
  showAtom :: a -> Text

pprint :: (Syntactic expr a, IsAtom a) => PrintRules a -> expr -> PP.Doc
pprint rules expr = pprintDatum rules (syntaxToDatum expr)

pprintDatum :: IsAtom a => PrintRules a -> Datum a -> PP.Doc
pprintDatum rules@(PrintRules getLayout) stx =
  case unDatum stx of
    Atom at -> ppAtom at
    List lst ->
      PP.parens . PP.group $
      case lst of
        [] -> PP.empty
        [x] -> pprintDatum rules x
        ((unDatum -> Atom car) : xs) ->
          case getLayout car of
            Nothing -> ppAtom car <> PP.space <> PP.align (PP.vsep $ pprintDatum rules <$> xs)
            Just (Special i) ->
              let (special, rest) = splitAt i xs
              in PP.hang 2 $ PP.vsep $
                 PP.group (PP.hang 2 $ PP.vsep $ ppAtom car : (map (pprintDatum rules) special)) :
                 map (pprintDatum rules) rest
        xs -> PP.vsep $ pprintDatum rules <$> xs

  where ppAtom = PP.text . T.unpack . showAtom

toText :: (Syntactic expr a, IsAtom a) => PrintRules a -> expr -> Text
toText rules stx = T.pack (PP.displayS (PP.renderSmart 0.8 80 $ pprint rules stx) "")

datumToText :: IsAtom a => PrintRules a -> Datum a -> Text
datumToText rules dat = T.pack (PP.displayS (PP.renderSmart 0.8 80 $ pprintDatum rules dat) "")
