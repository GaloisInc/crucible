{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.Syntax.ExprParse
  ( SyntaxParse
  , syntaxParseIO

  -- * Errors
  , SyntaxError(..)
  , printSyntaxError

  -- * Testing utilities
  , TrivialAtom(..)
  , test
  ) where

import Control.Applicative
import Control.Lens hiding (List, cons, backwards)
import Control.Monad (MonadPlus(..), ap)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import qualified Control.Monad.State.Strict as Strict

import Data.Containers.ListUtils (nubOrd)
import Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import GHC.Stack

import Lang.Crucible.Syntax.SExpr

import qualified Text.Megaparsec as MP

import Lang.Crucible.Syntax.Monad

data Search a = Try a (Search a) | Fail | Cut
  deriving Functor

instance Applicative Search where
  pure x = Try x Fail
  (<*>) = ap

instance Alternative Search where
  empty = Fail
  x <|> y =
    case x of
      Try first rest -> Try first (rest <|> y)
      Fail -> y
      Cut -> Cut

instance Monad Search where
  m >>= f =
    case m of
      Try x more -> f x <|> (more >>= f)
      Fail -> Fail
      Cut -> Fail

instance MonadPlus Search where
  mzero = empty
  mplus = (<|>)

instance Semigroup (Search a) where
  (<>) = (<|>)

instance Monoid (Search a) where
  mempty  = empty

instance Foldable Search where
  foldMap f (Try x xs) = f x `mappend` foldMap f xs
  foldMap _ _ = mempty

  toList (Try x xs) = x : toList xs
  toList _          = []

instance Traversable Search where
  traverse f (Try x xs) = Try <$> f x <*> traverse f xs
  traverse _ Fail = pure Fail
  traverse _ Cut = pure Cut

delimitSearch :: Search a -> Search a
delimitSearch (Try first rest) = Try first $ delimitSearch rest
delimitSearch Fail = Fail
delimitSearch Cut = Fail

cutSearch :: Search a
cutSearch = Cut

data Failure atom = Ok | Oops Progress (NonEmpty (Reason atom))
  deriving (Functor, Show)

instance Semigroup (Failure atom) where
  Ok              <> e2 = e2
  e1@(Oops _ _)   <> Ok = e1
  e1@(Oops p1 r1) <> e2@(Oops p2 r2) =
    case compare p1 p2 of
      LT -> e2
      GT -> e1
      EQ -> Oops p1 (r1 <> r2)

instance Monoid (Failure atom) where
  mempty = Ok

data P atom a = P { _success :: Search a
                  , _failure :: Failure atom
                  }
  deriving Functor

instance Semigroup (P atom a) where
  P s1 f1 <> P s2 f2 = P (s1 <> s2) (f1 <> f2)

instance Monoid (P atom a) where
  mempty = P mempty mempty

instance Applicative (P atom) where
  pure x = P (pure x) mempty
  f <*> x = ap f x

instance Alternative (P atom) where
  empty = mempty
  (<|>) = mappend

instance Monad (P atom) where
  (P xs e) >>= f = mappend (foldMap f xs) (P empty e)

instance MonadPlus (P atom) where
  mzero = empty
  mplus = (<|>)

newtype STP atom a = STP { runSTP :: IO (P atom a) }
  deriving (Functor, Semigroup, Monoid)

instance Applicative (STP atom) where
  pure = STP . pure . pure
  (<*>) = ap

instance Monad (STP atom) where
  STP m >>= f = STP $ do
    P xs e <- m
    mappend (runSTP (foldMap f xs)) (return $ P empty e)

instance MonadIO (STP atom) where
  liftIO m = STP $ return <$> m

data SyntaxParseCtx atom =
  SyntaxParseCtx { _parseProgress :: Progress
                 , _parseReason :: Reason atom
                 , _parseFocus :: Syntax atom
                 }
  deriving Show

parseProgress :: Simple Lens (SyntaxParseCtx atom) Progress
parseProgress = lens _parseProgress (\s v -> s { _parseProgress = v })

parseReason :: Simple Lens (SyntaxParseCtx atom) (Reason atom)
parseReason = lens _parseReason (\s v -> s { _parseReason = v })

parseFocus :: Simple Lens (SyntaxParseCtx atom) (Syntax atom)
parseFocus = lens _parseFocus (\s v -> s { _parseFocus = v })

-- | The default parsing monad. Use its 'MonadSyntax' instance to write parsers.
newtype SyntaxParse atom a =
  SyntaxParse { runSyntaxParse :: ReaderT (SyntaxParseCtx atom)
                                          (STP atom)
                                          a }
  deriving ( Functor, Applicative, Monad
           , MonadReader (SyntaxParseCtx atom), MonadIO
           )

instance Alternative (SyntaxParse atom) where
  empty =
    SyntaxParse $ ReaderT $ \(SyntaxParseCtx p r _) ->
      STP $ return $ P empty (Oops p (pure r))
  (SyntaxParse (ReaderT x)) <|> (SyntaxParse (ReaderT y)) =
    SyntaxParse $ ReaderT $ \ctx -> STP $ do
      a <- runSTP $ x ctx
      b <- runSTP $ y ctx
      return $ a <|> b

instance MonadPlus (SyntaxParse atom) where
  mzero = empty
  mplus = (<|>)

instance MonadSyntax atom (SyntaxParse atom) where
  anything = view parseFocus
  progress = view parseProgress
  withFocus stx = local $ set parseFocus stx
  withProgress f = local $ over parseProgress f
  withReason r = local $ set parseReason r
  cut =
    SyntaxParse $
    ReaderT $
    \(SyntaxParseCtx p r _) ->
      STP $ return $
      P cutSearch (Oops p (pure r))
  delimit (SyntaxParse (ReaderT f)) =
    SyntaxParse $
    ReaderT $
    \r -> STP $ do
      P s e <- runSTP $ f r
      return $ P (delimitSearch s) e
  call (SyntaxParse (ReaderT p)) =
    SyntaxParse $
    ReaderT $
    \r -> STP $ do
      P s e <- runSTP $ p r
      return $ case s of
        Try x _ -> P (Try x Fail) Ok
        Cut -> P Cut e
        Fail -> P Fail e

-- | Syntax errors explain why the error occurred.
data SyntaxError atom = SyntaxError (NonEmpty (Reason atom))
  deriving (Show, Eq)

-- | Convert an internal error structure into a form suitable for
-- humans to read.
printSyntaxError :: IsAtom atom => SyntaxError atom -> Text
printSyntaxError (SyntaxError rs) =
  T.intercalate "\n\tor\n" $ nubOrd $ map printGroup $ groupReasons rs
 where
    reasonPos (Reason found _) = syntaxPos found
    groupReasons reasons =
      [ (reasonPos repr, g)
      | g@(repr :| _) <- NE.groupBy (\x y -> reasonPos x == reasonPos y) (NE.toList reasons)
      ]
    printGroup (p, r@(Reason found _) :| more) =
      T.concat
      [ "At ", T.pack (show p)
      , ", expected ", T.intercalate " or " (nubOrd $ List.sort [ wanted | Reason _ wanted <- r:more ])
      , " but got ", toText mempty found]

-- | Attempt to parse the given piece of syntax, returning the first success found,
--   or the error(s) with the greatest progress otherwise.
syntaxParseIO :: IsAtom atom => SyntaxParse atom a -> Syntax atom -> IO (Either (SyntaxError atom) a)
syntaxParseIO p stx = do
  (P yes no) <-
        runSTP $ runReaderT (runSyntaxParse p) $
          SyntaxParseCtx emptyProgress (Reason stx (T.pack "bad syntax")) stx
  case Foldable.toList yes of
    [] ->
      return $ Left $ SyntaxError $
        case no of
          Ok        -> error "Internal error: no reason provided, yet no successful parse found."
          Oops _ rs -> rs
    (r:_) -> return $ Right r

-- | A trivial atom, which is a wrapper around 'Text', for use when testing the library.
newtype TrivialAtom = TrivialAtom Text deriving (Show, Eq)

instance IsAtom TrivialAtom where
  showAtom (TrivialAtom x) = x

instance IsString TrivialAtom where
  fromString x = TrivialAtom (fromString x)

-- | Test a parser on some input, displaying the result.
test :: (HasCallStack, Show a) => Text -> SyntaxParse TrivialAtom a -> IO ()
test txt p =
  case MP.parse (skipWhitespace *> sexp (TrivialAtom <$> identifier) <* MP.eof) "input" txt of
     Left err -> putStrLn "Reader error: " >> putStrLn (MP.errorBundlePretty err)
     Right sexpr ->
       syntaxParseIO p sexpr >>= \case
         Left e -> T.putStrLn (printSyntaxError e)
         Right ok -> print ok
