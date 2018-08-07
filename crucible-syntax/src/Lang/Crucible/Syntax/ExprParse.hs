{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Syntax.ExprParse where

import Control.Applicative
import Control.Lens hiding (List)
import Control.Monad (ap)
import Control.Monad.Reader
import qualified Control.Monad.State.Strict as Strict
import qualified Control.Monad.State.Lazy as Lazy
import Control.Monad.State.Class
import qualified Control.Monad.Writer.Strict as Strict
import qualified Control.Monad.Writer.Lazy as Lazy
import Control.Monad.Writer.Class

import Data.Foldable as Foldable
import Data.List
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup (Semigroup(..))
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Debug.Trace (trace)

import GHC.Stack

import Lang.Crucible.Syntax.SExpr

import qualified Text.Megaparsec as MP

import What4.ProgramLoc (Posd(..), Position)


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
  return x = pure x
  m >>= f =
    case m of
      Try x more -> f x <|> (more >>= f)
      Fail -> Fail
      Cut -> Fail

instance MonadPlus Search where
  mzero = empty
  mplus = (<|>)

instance Monoid (Search a) where
  mempty  = empty
  mappend = (<|>)

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
  deriving (Functor, Show, Eq)

data Failure atom = Ok | Oops Progress (NonEmpty (Reason atom))
  deriving (Functor, Show)

instance Monoid (Failure atom) where
  mempty = Ok
  mappend Ok e2 = e2
  mappend e1@(Oops _ _) Ok = e1
  mappend e1@(Oops p1 r1) e2@(Oops p2 r2) =
    case compare p1 p2 of
      LT -> e2
      GT -> e1
      EQ -> Oops p1 (r1 <> r2)

data P atom a = P { success :: Search a
                  , failure :: Failure atom
                  }
  deriving Functor

instance Monoid (P atom a) where
  mempty = P mempty mempty
  mappend (P s1 f1) (P s2 f2) = P (mappend s1 s2) (mappend f1 f2)

instance Applicative (P atom) where
  pure x = P (pure x) mempty
  f <*> x = ap f x

instance Alternative (P atom) where
  empty = mempty
  (<|>) = mappend

instance Monad (P atom) where
  return = pure
  (P xs e) >>= f = mappend (foldMap f xs) (P empty e)

instance MonadPlus (P atom) where
  mzero = empty
  mplus = (<|>)


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


newtype SyntaxParse atom a =
  SyntaxParse { runSyntaxParse :: ReaderT (SyntaxParseCtx atom) (P atom) a }
  deriving (Functor, Applicative, Monad, MonadReader (SyntaxParseCtx atom))

instance Alternative (SyntaxParse atom) where
  empty =
    SyntaxParse $ ReaderT $ \(SyntaxParseCtx p r _) -> P empty (Oops p (pure r))
  (SyntaxParse (ReaderT x)) <|> (SyntaxParse (ReaderT y)) =
    SyntaxParse $ ReaderT $ \ctx -> x ctx <|> y ctx

instance MonadPlus (SyntaxParse atom) where
  mzero = empty
  mplus = (<|>)

class (Alternative m, Monad m) => MonadSyntax atom m | m -> atom where
  anything :: m (Syntax atom)
  withFocus :: Syntax atom -> m a -> m a
  withProgress :: ProgressStep -> m a -> m a
  withReason :: Reason atom -> m a -> m a
  cut :: m a
  delimit :: m a -> m a

instance MonadSyntax atom (SyntaxParse atom) where
  anything = view parseFocus
  withFocus stx = local $ set parseFocus stx
  withProgress p = local $ over parseProgress (pushProgress p)
  withReason r = local $ set parseReason r
  cut =
    SyntaxParse $
    ReaderT $
    \(SyntaxParseCtx p r _) ->
      P cutSearch (Oops p (pure r))
  delimit (SyntaxParse (ReaderT f)) =
    SyntaxParse $
    ReaderT $
    \r ->
      let (P s e) = f r
      in P (delimitSearch s) e

instance MonadSyntax atom m => MonadSyntax atom (ReaderT r m) where
  anything = lift anything
  cut = lift cut
  delimit m =
    do r <- ask
       lift $ delimit (runReaderT m r)
  withFocus stx m =
    do r <- ask
       lift $ withFocus stx (runReaderT m r)
  withProgress p m =
    do r <- ask
       lift $ withProgress p (runReaderT m r)
  withReason why m =
    do r <- ask
       lift $ withReason why (runReaderT m r)



instance (MonadPlus m, MonadSyntax atom m) => MonadSyntax atom (Strict.StateT s m) where
  anything = lift anything
  cut = lift cut
  delimit m =
    do st <- get
       (s, st') <- lift $ delimit (Strict.runStateT m st)
       put st'
       return s
  withFocus stx m =
    do st <- get
       (s, st') <- lift $ withFocus stx (Strict.runStateT m st)
       put st'
       return s
  withProgress p m =
    do st <- get
       (s, st') <- lift $ withProgress p (Strict.runStateT m st)
       put st'
       return s
  withReason why m =
    do st <- get
       (s, st') <- lift $ withReason why (Strict.runStateT m st)
       put st'
       return s

instance (MonadPlus m, MonadSyntax atom m) => MonadSyntax atom (Lazy.StateT s m) where
  anything = lift anything
  cut = lift cut
  delimit m =
    do st <- get
       (s, st') <- lift $ delimit (Lazy.runStateT m st)
       put st'
       return s
  withFocus stx m =
    do st <- get
       (s, st') <- lift $ withFocus stx (Lazy.runStateT m st)
       put st'
       return s
  withProgress p m =
    do st <- get
       (s, st') <- lift $ withProgress p (Lazy.runStateT m st)
       put st'
       return s
  withReason why m =
    do st <- get
       (s, st') <- lift $ withReason why (Lazy.runStateT m st)
       put st'
       return s


instance (Monoid w, MonadSyntax atom m) => MonadSyntax atom (Strict.WriterT w m) where
  anything = lift anything
  cut = lift cut
  delimit m =
    do (x, w) <- lift $ delimit $ Strict.runWriterT m
       tell w
       return x
  withFocus stx m =
    do (x, w) <- lift $ withFocus stx $ Strict.runWriterT m
       tell w
       return x
  withProgress p m =
    do (x, w) <- lift $ withProgress p $ Strict.runWriterT m
       tell w
       return x
  withReason why m =
    do (x, w) <- lift $ withReason why $ Strict.runWriterT m
       tell w
       return x


instance (Monoid w, MonadSyntax atom m) => MonadSyntax atom (Lazy.WriterT w m) where
  anything = lift anything
  cut = lift cut
  delimit m =
    do (x, w) <- lift $ delimit $ Lazy.runWriterT m
       tell w
       return x
  withFocus stx m =
    do (x, w) <- lift $ withFocus stx $ Lazy.runWriterT m
       tell w
       return x
  withProgress p m =
    do (x, w) <- lift $ withProgress p $ Lazy.runWriterT m
       tell w
       return x
  withReason why m =
    do (x, w) <- lift $ withReason why $ Lazy.runWriterT m
       tell w
       return x


parseError :: Progress -> Reason atom -> P atom a
parseError p r = P empty (Oops p (pure r))

debug :: (Show atom) => String -> SyntaxParse atom a -> SyntaxParse atom a
debug msg p =
  do r <- ask
     trace (msg ++ show r) $ return ()
     p

-- | Strip location information from a syntax object
syntaxToDatum :: Syntactic expr atom => expr -> Datum atom
syntaxToDatum (A x) = Datum $ Atom x
syntaxToDatum (L ls) = Datum $ List $ map syntaxToDatum ls
syntaxToDatum _ = error "syntaxToDatum: impossible case - bad Syntactic instance"


satisfy :: MonadSyntax atom m => (Syntax atom -> Bool) -> m (Syntax atom)
satisfy p =
  do foc <- anything
     if p foc
       then pure foc
       else empty

datum :: (MonadSyntax atom m, IsAtom atom, Eq atom) => Datum atom -> m ()
datum dat =
  describe (datumToText mempty dat) $
    satisfy (\stx -> dat == syntaxToDatum stx) *> pure ()

atom :: (MonadSyntax atom m, IsAtom atom, Eq atom) => atom -> m ()
atom a = datum (Datum (Atom a))

atomic :: MonadSyntax atom m => m atom
atomic = sideCondition "an atom" perhapsAtom (syntaxToDatum <$> anything)
  where perhapsAtom (Datum (Atom a)) = Just a
        perhapsAtom _ = Nothing

describe :: MonadSyntax atom m => Text -> m a -> m a
describe d p =
  do foc <- anything
     withReason (Reason foc d) p

emptyList :: MonadSyntax atom m => m ()
emptyList = describe (T.pack "empty expression ()") (satisfy (isNil . syntaxToDatum) *> pure ())
  where isNil (Datum (List [])) = True
        isNil _ = False

anyList :: MonadSyntax atom m => m [Syntax atom]
anyList = sideCondition "zero or more expressions, in parentheses" isList anything
  where isList (Syntax (pos_val -> List xs)) = Just xs
        isList _ = Nothing


cons :: MonadSyntax atom m => m a -> m b -> m (a, b)
cons a d = depCons a (\x -> d >>= \y -> pure (x, y))

followedBy :: MonadSyntax atom m => m a -> m b -> m b
followedBy a d = depCons a (const d)

position :: MonadSyntax atom m => m Position
position = syntaxPos <$> anything

-- | A dependent cons (see 'depcons') that can impose a validation
-- step on the first projection
depConsCond :: MonadSyntax atom m => m a -> (a -> m (Either Text b)) -> m b
depConsCond a d =
  do focus <- anything
     case focus of
       L (e:es) ->
         do x <- withFocus e $ withProgress First $ a
            let cdr = Syntax (Posd (syntaxPos focus) (List es))
            res <- withFocus cdr $ withProgress Rest $ d x
            case res of
              Right answer -> return answer
              Left what -> withFocus e $ withProgress First $ later $ describe what empty
       _ -> empty


depCons :: MonadSyntax atom m => m a -> (a -> m b) -> m b
depCons a d =
  do focus <- anything
     case focus of
       L (e:es) ->
         do x <- withFocus e $ withProgress First $ a
            let cdr = Syntax (Posd (syntaxPos focus) (List es))
            withFocus cdr $ withProgress Rest $ d x
       _ -> empty


rep :: MonadSyntax atom m => m a -> m [a]
rep p =
  do focus <- anything
     case focus of
       L [] ->
         pure []
       L (e:es) ->
         do x <- withFocus e $ withProgress First p
            let cdr = Syntax (Posd (syntaxPos focus) (List es))
            xs <- withFocus cdr $ withProgress Rest $ rep p
            pure (x : xs)
       _ -> empty

parse :: MonadSyntax atom m => Syntax atom -> m a -> m a
parse = withFocus

list :: MonadSyntax atom m => [m a] -> m [a]
list parsers = describe desc $ list' parsers
  where desc =
          mappend (T.pack (show (length parsers))) (T.pack " expressions")
        list' ps =
          do focus <- anything
             case focus of
               L es -> go (syntaxPos focus) ps es
               _ -> empty

        go _ [] [] = pure []
        go _ (_:_) [] = empty
        go _ [] (_:_) = empty
        go loc (p:ps) (e:es) =
          do x <- withFocus e $ withProgress First p
             xs <- withFocus (Syntax (Posd loc (List es))) $
                   withProgress Rest $
                   list' ps
             pure (x : xs)

later :: MonadSyntax atom m => m a -> m a
later = withProgress Late


barrier :: MonadSyntax atom m => m ()
barrier = pure () <|> cut

sideCondition :: MonadSyntax atom m => Text -> (a -> Maybe b) -> m a -> m b
sideCondition msg ok p =
  do x <- p
     case ok x of
       Just y -> pure y
       Nothing ->
         later $ describe msg empty

sideCondition' :: MonadSyntax atom m => Text -> (a -> Bool) -> m a -> m a
sideCondition' msg ok p = sideCondition msg (\x -> if ok x then Just x else Nothing) p


-- | Syntax errors explain why the error occurred.
data SyntaxError atom = SyntaxError (NonEmpty (Reason atom))
  deriving (Show, Eq)

printSyntaxError :: IsAtom atom => SyntaxError atom -> Text
printSyntaxError (SyntaxError rs) =
  T.intercalate "\n\tor\n" $ nub $ map printGroup $ groupReasons rs
 where
    reasonPos (Reason found _) = syntaxPos found
    groupReasons reasons =
      [ (reasonPos repr, g)
      | g@(repr :| _) <- NE.groupBy (\x y -> reasonPos x == reasonPos y) (NE.toList reasons)
      ]
    printGroup (p, r@(Reason found _) :| more) =
      T.concat
      [ "At ", T.pack (show p)
      , ", expected ", T.intercalate " or " (nub $ sort [ wanted | Reason _ wanted <- r:more ])
      , " but got ", toText mempty found]

syntaxParse :: IsAtom atom => SyntaxParse atom a -> Syntax atom -> Either (SyntaxError atom) a
syntaxParse p stx =
  let (P yes no) =
        runReaderT (runSyntaxParse p) $
          SyntaxParseCtx (Progress []) (Reason stx (T.pack "bad syntax")) stx
  in
    case Foldable.toList yes of
      [] ->
        Left $ SyntaxError $
          case no of
            Ok        -> error "Internal error: no reason provided, yet no successful parse found."
            Oops _ rs -> rs
      (r:_) -> Right r

backwards :: MonadSyntax atom m => m a -> m a
backwards p =
  do foc <- anything
     case foc of
      l@(L xs) -> withFocus (Syntax (Posd (syntaxPos l) (List (reverse xs)))) p
      _ -> empty

commit :: MonadSyntax atom m => m ()
commit = pure () <|> cut

newtype TrivialAtom = TrivialAtom Text deriving (Show, Eq)

instance IsAtom TrivialAtom where
  showAtom (TrivialAtom x) = x

instance IsString TrivialAtom where
  fromString x = TrivialAtom (fromString x)

test :: (HasCallStack, Show a) => Text -> SyntaxParse TrivialAtom a -> IO ()
test txt p =
  case MP.parse (skipWhitespace *> sexp (TrivialAtom <$> identifier) <* MP.eof) "input" txt of
     Left err -> putStrLn "Reader error: " >> putStrLn (MP.parseErrorPretty' txt err)
     Right sexpr ->
       case syntaxParse p sexpr of
         Left e -> T.putStrLn (printSyntaxError e)
         Right ok -> print ok
