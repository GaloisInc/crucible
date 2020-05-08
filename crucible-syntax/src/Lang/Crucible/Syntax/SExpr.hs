{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Syntax.SExpr
  ( pattern A
  , pattern L
  , pattern (:::)
  , Syntax(..)
  , Datum(..)
  , Syntactic(..)
  ,  Parser
  , syntaxPos
  , withPosFrom
  , sexp
  , identifier
  , toText
  , datumToText
  , skipWhitespace
  , PrintRules(..)
  , PrintStyle(..)
  , Layer(..)
  , IsAtom(..)
  ) where

import Data.Char (isDigit, isLetter)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void

import Lang.Crucible.ProgramLoc as C

import Text.Megaparsec as MP
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.PrettyPrint.ANSI.Leijen as PP


-- | Syntax objects, in which each layer is annotated with a source position.
newtype Syntax a = Syntax { unSyntax :: Posd (Layer Syntax a) }
  deriving (Show, Functor, Eq)

-- | Syntax objects divorced of their source-code context, without source positions.
newtype Datum a = Datum { unDatum :: Layer Datum a}
  deriving (Show, Functor, Eq)

-- | Extract the source position from a 'Syntax' object.
syntaxPos :: Syntax a -> Position
syntaxPos (Syntax (Posd p _)) = p

-- | Use the position from a syntax object around something else.
withPosFrom :: Syntax a -> b -> Posd b
withPosFrom stx x = Posd (syntaxPos stx) x

-- | Instances of 'Syntactic' support observations using the 'L' and 'A' patterns.
class Syntactic a b | a -> b where
  syntaxE :: a -> Layer Syntax b

instance Syntactic (Layer Syntax a) a where
  syntaxE = id


instance Syntactic (Syntax a) a where
  syntaxE (Syntax (Posd _ e)) = e

-- | Match an atom from a syntactic structure
pattern A :: Syntactic a b => b -> a
pattern A x <- (syntaxE -> Atom x)

-- | Match a list from a syntactic structure
pattern L :: Syntactic a b => [Syntax b] -> a
pattern L xs <- (syntaxE -> List xs)

-- | Match the head and tail of a list-like structure
pattern (:::) :: Syntactic a b => Syntax b -> [Syntax b] -> a
pattern x ::: xs <- (syntaxE -> List (x : xs))

-- | The pattern functor for syntax, used both for 'Syntax' and
-- 'Datum'. In 'Syntax', it is composed with another structure that
-- adds source positions.
data Layer f a = List [f a] | Atom a
  deriving (Show, Functor, Eq)

-- | Convert any syntactic structure to its simplest description.
syntaxToDatum :: Syntactic expr atom => expr -> Datum atom
syntaxToDatum (A x) = Datum (Atom x)
syntaxToDatum (L xs) = Datum (List (map syntaxToDatum xs))
syntaxToDatum _ = error "impossible - bad Syntactic instance"

-- | A parser for s-expressions.
type Parser = Parsec Void Text

-- | Skip whitespace.
skipWhitespace :: Parser ()
skipWhitespace = L.space space1 lineComment blockComment
  where lineComment = L.skipLineComment ";"
        blockComment = L.skipBlockComment "#|" "|#"

-- | Skip the whitespace after a token.
lexeme :: Parser a -> Parser a
lexeme = L.lexeme skipWhitespace

-- | Parse something with its location.
withPos :: Parser a -> Parser (Posd a)
withPos p =
  do MP.SourcePos file line col <- getSourcePos
     let loc = C.SourcePos (T.pack file) (unPos line) (unPos col)
     res <- p
     return $ Posd loc res

-- | Parse a particular string.
symbol :: Text -> Parser Text
symbol = L.symbol skipWhitespace

-- | Parse a parenthesized list.
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

-- | Parse an identifier.
identifier :: Parser Text
identifier = T.pack <$> identString
  where letterLike x = isLetter x || elem x ("<>=+-*/!_\\?" :: [Char])
        nameChar x = letterLike x || isDigit x || elem x ("$" :: [Char])
        identString = (:) <$> satisfy letterLike <*> many (satisfy nameChar)

-- | Styles of printing
data PrintStyle =
  -- | Special forms should treat the first n subforms as special, and
  -- the remaining as a body. For instance, for a Lisp-like
  -- let-expression, use 'Special 1' for indentation.
  Special Int

-- | Printing rules describe how to specially format expressions that
-- begin with particular atoms.
newtype PrintRules a = PrintRules (a -> Maybe PrintStyle)

instance Semigroup (PrintRules a) where
  (<>) = mappend

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

-- | Render a syntactic structure to text, according to rules.
toText :: (Syntactic expr a, IsAtom a) => PrintRules a -> expr -> Text
toText rules stx = T.pack (PP.displayS (PP.renderSmart 0.8 80 $ pprint rules stx) "")

-- | Render a datum to text according to rules.
datumToText :: IsAtom a => PrintRules a -> Datum a -> Text
datumToText rules dat = T.pack (PP.displayS (PP.renderSmart 0.8 80 $ pprintDatum rules dat) "")
