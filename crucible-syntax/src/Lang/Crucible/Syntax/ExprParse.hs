{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Lang.Crucible.Syntax.ExprParse where

import Control.Applicative
import Control.Lens hiding (List)
import Control.Monad (ap)
import Control.Monad.Reader

import Data.List
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Lang.Crucible.Syntax.SExpr

import qualified Text.Megaparsec as MP

import What4.ProgramLoc (Posd(..))

data ProgressStep = First | Rest | Late
  deriving (Eq, Show)

instance Ord ProgressStep where
  compare First First = EQ
  compare First _ = LT
  compare Rest First = GT
  compare Rest Rest = EQ
  compare Rest _ = LT
  compare Late Late = EQ
  compare Late _ = GT

newtype Progress = Progress [ProgressStep]
  deriving (Eq, Show)

pushProgress :: ProgressStep -> Progress -> Progress
pushProgress p (Progress ps) = Progress (p : ps)

instance Ord Progress where
  compare (Progress xs) (Progress ys) =
    case (xs, ys) of
      ([], []) -> EQ
      ([], _:_) -> LT
      (_:_, []) -> GT
      (x:xs', y:ys') ->
        case compare (Progress xs') (Progress ys') of
          LT -> LT
          GT -> GT
          EQ -> compare x y


data Reason atom = Reason { expr :: Syntax atom
                          , message :: Text
                          }
  deriving (Functor, Show)

data Failure atom = Ok | Oops Progress [Reason atom]
  deriving (Functor, Show)

instance Monoid (Failure atom) where
  mempty = Ok
  mappend Ok e2 = e2
  mappend e1@(Oops _ _) Ok = e1
  mappend e1@(Oops p1 r1) e2@(Oops p2 r2) =
    case compare p1 p2 of
      LT -> e2
      GT -> e1
      EQ -> Oops p1 (mappend r1 r2)

data P atom a = P { success :: [a]
                  , failure :: Failure atom
                  }
  deriving Functor

instance Monoid (P atom a) where
  mempty = P mempty mempty
  mappend (P s1 f1) (P s2 f2) = P (mappend s1 s2) (mappend f1 f2)

instance Applicative (P atom) where
  pure x = P [x] mempty
  f <*> x = ap f x

instance Alternative (P atom) where
  empty = mempty
  (<|>) = mappend

instance Monad (P atom) where
  return = pure
  (P xs e) >>= f = mappend (mconcat [f x | x <- xs]) (P [] e)

data SyntaxParseCtx atom =
  SyntaxParseCtx { _parseProgress :: Progress
                 , _parseReason :: Reason atom
                 , _parseFocus :: Syntax atom
                 }

parseProgress :: Simple Lens (SyntaxParseCtx atom) Progress
parseProgress = lens _parseProgress (\s v -> s { _parseProgress = v })

parseReason :: Simple Lens (SyntaxParseCtx atom) (Reason atom)
parseReason = lens _parseReason (\s v -> s { _parseReason = v })

parseFocus :: Simple Lens (SyntaxParseCtx atom) (Syntax atom)
parseFocus = lens _parseFocus (\s v -> s { _parseFocus = v })


newtype SyntaxParse atom a =
  SyntaxParse { runSyntaxParse :: ReaderT (SyntaxParseCtx atom) (P atom) a }
  deriving (Functor, Applicative, Monad, MonadReader (SyntaxParseCtx atom))

instance Alternative (SyntaxParse atom) where
  empty =
    SyntaxParse $ ReaderT $ \(SyntaxParseCtx p r _) -> P [] (Oops p [r])
  (SyntaxParse (ReaderT x)) <|> (SyntaxParse (ReaderT y)) =
    SyntaxParse $ ReaderT $ \ctx -> x ctx <|> y ctx

parseError :: Progress -> Reason atom -> P atom a
parseError p r = P [] (Oops p [r])

-- | Strip location information from a syntax object
syntaxToDatum :: Syntactic expr atom => expr -> Datum atom
syntaxToDatum (A x) = Datum $ Atom x
syntaxToDatum (L ls) = Datum $ List $ map syntaxToDatum ls
syntaxToDatum _ = error "syntaxToDatum: impossible case - bad Syntactic instance"

anything :: SyntaxParse atom (Syntax atom)
anything = view parseFocus

satisfy :: (Syntax atom -> Bool) -> SyntaxParse atom (Syntax atom)
satisfy p =
  do foc <- view parseFocus
     if p foc
       then pure foc
       else empty

datum :: (IsAtom atom, Eq atom) => Datum atom -> SyntaxParse atom ()
datum dat =
  describe (datumToText mempty dat) $
    satisfy (\stx -> dat == syntaxToDatum stx) *> pure ()

describe :: Text -> SyntaxParse atom a -> SyntaxParse atom a
describe d p =
  do foc <- view parseFocus
     local (set parseReason (Reason foc d)) p

emptyList :: SyntaxParse atom ()
emptyList = describe (T.pack "empty expression ()") (satisfy (isNil . syntaxToDatum) *> pure ())
  where isNil (Datum (List [])) = True
        isNil _ = False

cons :: SyntaxParse atom a -> SyntaxParse atom b -> SyntaxParse atom (a, b)
cons a d =
  do focus <- view parseFocus
     case focus of
       L (e:es) ->
         do x <- local (set parseFocus e . over parseProgress (pushProgress First)) a
            let cdr = Syntax (Posd (syntaxPos focus) (List es))
            xs <- local (set parseFocus cdr . over parseProgress (pushProgress Rest)) d
            pure (x, xs)
       _ -> empty

rep :: SyntaxParse atom a -> SyntaxParse atom [a]
rep p =
  do focus <- view parseFocus
     case focus of
       L [] ->
         pure []
       L (e:es) ->
         do x <- local (set parseFocus e . over parseProgress (pushProgress First)) p
            let cdr = Syntax (Posd (syntaxPos focus) (List es))
            xs <- local (set parseFocus cdr . over parseProgress (pushProgress Rest)) (rep p)
            pure (x : xs)
       _ -> empty


list :: [SyntaxParse atom a] -> SyntaxParse atom [a]
list parsers = describe desc $ list' parsers


  where desc =
          mappend (T.pack (show (length parsers))) (T.pack " expressions")
        list' ps =
          do focus <- view parseFocus
             case focus of
               L es -> go (syntaxPos focus) ps es
               _ -> empty

        go _ [] [] = pure []
        go _ (_:_) [] = empty
        go _ [] (_:_) = empty
        go loc (p:ps) (e:es) =
          do x <- local (set parseFocus e . over parseProgress (pushProgress First)) p
             xs <- local (set parseFocus (Syntax (Posd loc (List es))) .
                          over parseProgress (pushProgress Rest))
                     (list' ps)
             pure (x : xs)


syntaxParse :: IsAtom atom => SyntaxParse atom a -> Syntax atom -> Either Text a
syntaxParse p stx =
  let (P yes no) =
        runReaderT (runSyntaxParse p) $
          SyntaxParseCtx (Progress []) (Reason stx (T.pack "bad syntax")) stx
  in
    case yes of
      [] ->
        Left $
          case no of
            Ok -> T.pack "bad syntax"
            Oops _ rs -> T.intercalate "\n\tor\n" $ nub $ map printReason rs
      (r:_) -> Right r
  where
    printReason :: IsAtom atom => Reason atom -> Text
    printReason (Reason found wanted) =
      T.concat
        [ "At ", T.pack (show (syntaxPos found))
        , ", expected " , wanted
        , " but got " , toText mempty found
        ]

newtype TrivialAtom = TrivialAtom Text deriving (Show, Eq)

instance IsAtom TrivialAtom where
  showAtom (TrivialAtom x) = x

instance IsString TrivialAtom where
  fromString x = TrivialAtom (fromString x)

test :: (Show a) => Text -> SyntaxParse TrivialAtom a -> IO ()
test txt p =
  case MP.parse (skipWhitespace *> sexp (TrivialAtom <$> identifier) <* MP.eof) "input" txt of
     Left err -> putStrLn "Reader error: " >> putStrLn (MP.parseErrorPretty' txt err)
     Right sexpr ->
       case syntaxParse p sexpr of
         Left e -> T.putStrLn e
         Right ok -> print ok
