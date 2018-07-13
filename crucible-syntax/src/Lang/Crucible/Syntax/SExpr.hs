{-# LANGUAGE DeriveFunctor, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, OverloadedStrings, PatternSynonyms, ViewPatterns #-}
module Lang.Crucible.Syntax.SExpr (pattern A, pattern L, pattern (:::), Syntax, unSyntax, Syntactic(..),  Parser, syntaxPos, withPosFrom, sexp, identifier, toText, PrintRules(..), PrintStyle(..)) where

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

newtype Syntax a = Syntax { unSyntax :: Posd (Layer a) }
  deriving (Show, Functor)

syntaxPos :: Syntax a -> Position
syntaxPos (Syntax (Posd p _)) = p

withPosFrom :: Syntax a -> b -> Posd b
withPosFrom stx x = Posd (syntaxPos stx) x

class Syntactic a b | a -> b where
  syntaxE :: a -> Layer b

instance Syntactic (Layer a) a where
  syntaxE = id

instance Syntactic (Syntax a) a where
  syntaxE (Syntax (Posd _ e)) = e

pattern A :: Syntactic a b => b -> a
pattern A x <- (syntaxE -> Atom x)

pattern L :: Syntactic a b => [Syntax b] -> a
pattern L xs <- (syntaxE -> List xs)


pattern (:::) :: Syntactic a b => Syntax b -> [Syntax b] -> a
pattern x ::: xs <- (syntaxE -> List (x : xs))

data Layer a = List [Syntax a] | Atom a
  deriving (Show, Functor)


type Parser = Parsec Void Text


skip :: Parser ()
skip = L.space space1 lineComment blockComment
  where lineComment = L.skipLineComment ";"
        blockComment = L.skipBlockComment "#|" "|#"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme skip

withPos :: Parser a -> Parser (Posd a)
withPos p =
  do MP.SourcePos file line col <- getPosition
     let loc = C.SourcePos (T.pack file) (unPos line) (unPos col)
     res <- p
     return $ Posd loc res

symbol :: Text -> Parser Text
symbol = L.symbol skip

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
  where letterLike x = isLetter x || (elem x ("<>=+-?*/!_\\" :: [Char]))
        nameChar x = letterLike x || isDigit x
        identString = (:) <$> satisfy letterLike <*> many (satisfy nameChar)


data PrintStyle = Special Int
newtype PrintRules a = PrintRules (a -> Maybe PrintStyle)

instance Monoid (PrintRules a) where
  mempty = PrintRules $ const Nothing
  mappend (PrintRules f) (PrintRules g) = PrintRules $ \z -> f z <|> g z



pprint :: PrintRules a -> (a -> Text) -> Syntax a -> PP.Doc
pprint rules@(PrintRules getLayout) atom stx =
  case syntaxE stx of
    Atom at -> ppAtom at
    List lst ->
      PP.parens . PP.group $
      case lst of
        [] -> PP.empty
        [x] -> pprint rules atom x
        ((syntaxE -> Atom car) : xs) ->
          case getLayout car of
            Nothing -> ppAtom car <> PP.space <> PP.align (PP.vsep $ pprint rules atom <$> xs)
            Just (Special i) ->
              let (special, rest) = splitAt i xs
              in PP.hang 2 $ PP.vsep $
                 PP.group (PP.hang 2 $ PP.vsep $ ppAtom car : (map (pprint rules atom) special)) :
                 map (pprint rules atom) rest
        xs -> PP.vsep $ pprint rules atom <$> xs

  where ppAtom = PP.text . T.unpack . atom

toText :: PrintRules a -> (a -> Text) -> Syntax a -> Text
toText rules atom stx = T.pack (PP.displayS (PP.renderSmart 0.8 80 $ pprint rules atom stx) "\n")
