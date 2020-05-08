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
  ( MonadSyntax(..)
  , SyntaxParse
  , syntaxParseIO

  -- * Describing syntax
  , describe
  , atom
  , cons
  , depCons
  , depConsCond
  , followedBy
  , rep
  , list
  , backwards
  , emptyList
  , atomic
  , anyList
  , sideCondition
  , sideCondition'
  , satisfy

  -- * Eliminating location information
  , syntaxToDatum
  , datum

  -- * Parsing context
  , position
  , withProgressStep

  -- * Control structures
  , commit
  , parse

  -- * Progress through a parsing problem
  , ProgressStep(..)
  , Progress
  , pushProgress

  -- * Errors
  , later
  , SyntaxError(..)
  , printSyntaxError
  , Reason(..)

  -- * Testing utilities
  , TrivialAtom(..)
  , test
  ) where

import Control.Applicative
import Control.Lens hiding (List, cons, backwards)
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
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import GHC.Stack

import qualified Text.Megaparsec as MP

import Lang.Crucible.ProgramLoc (Posd(..), Position)
import Lang.Crucible.Syntax.SExpr

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

instance Semigroup (Search a) where
  (<>) = (<|>)

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

-- | Components of a path taken through a syntax object to reach the
-- current focus.
data ProgressStep =
    First -- ^ The head of a list was followed
  | Rest -- ^ The tail of a list was followed
  | Late -- ^ The path was annotated as 'later'
  deriving (Eq, Show)

instance Ord ProgressStep where
  compare First First = EQ
  compare First _ = LT
  compare Rest First = GT
  compare Rest Rest = EQ
  compare Rest _ = LT
  compare Late Late = EQ
  compare Late _ = GT

-- | The path taken through a syntax object to reach the current
-- focus.
newtype Progress = Progress [ProgressStep]
  deriving (Eq, Show)

-- | Add a step to a progress path
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


-- | The reason why a failure has occurred, consisting of description
-- 'message' combined with the focus that was described.
data Reason atom = Reason { expr :: Syntax atom
                          , message :: Text
                          }
  deriving (Functor, Show, Eq)

data Failure atom = Ok | Oops Progress (NonEmpty (Reason atom))
  deriving (Functor, Show)

instance Semigroup (Failure atom) where
  (<>) = mappend

instance Monoid (Failure atom) where
  mempty = Ok
  mappend Ok e2 = e2
  mappend e1@(Oops _ _) Ok = e1
  mappend e1@(Oops p1 r1) e2@(Oops p2 r2) =
    case compare p1 p2 of
      LT -> e2
      GT -> e1
      EQ -> Oops p1 (r1 <> r2)

data P atom a = P { _success :: Search a
                  , _failure :: Failure atom
                  }
  deriving Functor

instance Semigroup (P atom a) where
  (<>) = mappend

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

newtype STP atom a = STP { runSTP :: IO (P atom a) }
  deriving (Semigroup, Monoid)

instance Functor (STP atom) where
  fmap f (STP x) = STP $ fmap (fmap f) x

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

-- | Monads that can parse syntax need a few fundamental operations.
-- A parsing monad maintains an implicit "focus", which is the syntax
-- currently being matched, as well as the progress, which is the path
-- taken through the surrounding syntactic context to reach the
-- current focus. Additionally, the reason for a failure will always
-- be reported with respect to explicit descriptions - these are
-- inserted through 'withReason'.
class (Alternative m, Monad m) => MonadSyntax atom m | m -> atom where
  -- | Succeed with the current focus.
  anything :: m (Syntax atom)
  -- | Succeed with the current progress.
  progress :: m Progress
  -- | Run a new parser with a different focus.
  withFocus :: Syntax atom -> m a -> m a
  -- | Run a parser in a modified notion of progress.
  withProgress :: (Progress -> Progress) -> m a -> m a
  -- | Run a parser with a new reason for failure.
  withReason :: Reason atom -> m a -> m a
  -- | Fail, and additionally prohibit backtracking across the failure.
  cut :: m a
  -- | Delimit the dynamic extent of a 'cut'.
  delimit :: m a -> m a
  -- | Make the first solution reported by a computation into the only
  -- solution reported, eliminating further backtracking and previous
  -- errors. This allows syntax to be matched in exclusive "layers",
  -- reminiscent of the effect of trampolining through a macro
  -- expander. Use when solutions are expected to be unique.
  call :: m a -> m a

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

instance MonadSyntax atom m => MonadSyntax atom (ReaderT r m) where
  anything = lift anything
  cut = lift cut
  progress = lift progress
  delimit m =
    do r <- ask
       lift $ delimit (runReaderT m r)
  call m =
    do r <- ask
       lift $ call (runReaderT m r)
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
  progress = lift progress
  delimit m =
    do st <- get
       (s, st') <- lift $ delimit (Strict.runStateT m st)
       put st'
       return s
  call m =
    do st <- get
       (s, st') <- lift $ call (Strict.runStateT m st)
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
  progress = lift progress
  delimit m =
    do st <- get
       (s, st') <- lift $ delimit (Lazy.runStateT m st)
       put st'
       return s
  call m =
    do st <- get
       (s, st') <- lift $ call (Lazy.runStateT m st)
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
  progress = lift progress
  delimit m =
    do (x, w) <- lift $ delimit $ Strict.runWriterT m
       tell w
       return x
  call m =
    do (x, w) <- lift $ call $ Strict.runWriterT m
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
  progress = lift progress
  delimit m =
    do (x, w) <- lift $ delimit $ Lazy.runWriterT m
       tell w
       return x
  call m =
    do (x, w) <- lift $ call $ Lazy.runWriterT m
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




-- | Strip location information from a syntax object
syntaxToDatum :: Syntactic expr atom => expr -> Datum atom
syntaxToDatum (A x) = Datum $ Atom x
syntaxToDatum (L ls) = Datum $ List $ map syntaxToDatum ls
syntaxToDatum _ = error "syntaxToDatum: impossible case - bad Syntactic instance"

-- | Succeed if and only if the focus satisfies a Boolean predicate.
satisfy :: MonadSyntax atom m => (Syntax atom -> Bool) -> m (Syntax atom)
satisfy p =
  do foc <- anything
     if p foc
       then pure foc
       else empty

-- | Succeed only if the focus, having been stripped of position
-- information, is structurally equal to some datum.
datum :: (MonadSyntax atom m, IsAtom atom, Eq atom) => Datum atom -> m ()
datum dat =
  describe (datumToText mempty dat) $
    satisfy (\stx -> dat == syntaxToDatum stx) *> pure ()

-- | Succeed if and only if the focus is some particular given atom.
atom :: (MonadSyntax atom m, IsAtom atom, Eq atom) => atom -> m ()
atom a = datum (Datum (Atom a))

-- | Succeed if and only if the focus is any atom, returning the atom.
atomic :: MonadSyntax atom m => m atom
atomic = sideCondition "an atom" perhapsAtom (syntaxToDatum <$> anything)
  where perhapsAtom (Datum (Atom a)) = Just a
        perhapsAtom _ = Nothing

-- | Annotate a parser with a description, documenting its role in the
-- grammar. These descriptions are used to construct error messages.
describe :: MonadSyntax atom m => Text -> m a -> m a
describe !d p =
  do foc <- anything
     withReason (Reason foc d) p

-- | Succeed if and only if the focus is the empty list.
emptyList :: MonadSyntax atom m => m ()
emptyList = describe (T.pack "empty expression ()") (satisfy (isNil . syntaxToDatum) *> pure ())
  where isNil (Datum (List [])) = True
        isNil _ = False

-- | Succeed if and only if the focus is a list, returning its contents.
anyList :: MonadSyntax atom m => m [Syntax atom]
anyList = sideCondition "zero or more expressions, in parentheses" isList anything
  where isList (Syntax (pos_val -> List xs)) = Just xs
        isList _ = Nothing

-- | If the current focus is a list, apply one parser to its head and
-- another to its tail.
cons :: MonadSyntax atom m => m a -> m b -> m (a, b)
cons a d = depCons a (\x -> d >>= \y -> pure (x, y))

-- | If the current focus is a list, apply one parser to its head and
-- another to its tail, ignoring the result of the head.
followedBy :: MonadSyntax atom m => m a -> m b -> m b
followedBy a d = depCons a (const d)

-- | Return the source position of the focus.
position :: MonadSyntax atom m => m Position
position = syntaxPos <$> anything

-- | Manually add a progress step to the current path through the
-- context. Use this to appropriately guard calls to 'parse'.
withProgressStep :: (MonadSyntax atom m) => ProgressStep -> m a -> m a
withProgressStep s = withProgress (pushProgress s)


-- | A dependent cons (see 'depcons') that can impose a validation
-- step on the head of a list focus. If the head fails the validation
-- (that is, the second action returns 'Left'), the error is reported
-- in the head position.
depConsCond :: MonadSyntax atom m => m a -> (a -> m (Either Text b)) -> m b
depConsCond a d =
  do focus <- anything
     case focus of
       L (e:es) ->
         do x <- withFocus e $ withProgressStep First $ a
            let cdr = Syntax (Posd (syntaxPos focus) (List es))
            res <- withFocus cdr $ withProgressStep Rest $ d x
            case res of
              Right answer -> return answer
              Left what -> withFocus e $ withProgressStep First $ later $ describe what empty
       _ -> empty

-- | Use the result of parsing the head of the current-focused list to
-- compute a parsing action to use for the tail of the list.
depCons :: MonadSyntax atom m => m a -> (a -> m b) -> m b
depCons a d =
  do focus <- anything
     case focus of
       L (e:es) ->
         do x <- withFocus e $ withProgressStep First $ a
            let cdr = Syntax (Posd (syntaxPos focus) (List es))
            withFocus cdr $ withProgressStep Rest $ d x
       _ -> empty

-- | Produce a parser that matches a list of things matched by another
-- parser.
rep :: MonadSyntax atom m => m a -> m [a]
rep p =
  do focus <- anything
     case focus of
       L [] ->
         pure []
       L (e:es) ->
         do x <- withFocus e $ withProgressStep First p
            let cdr = Syntax (Posd (syntaxPos focus) (List es))
            xs <- withFocus cdr $ withProgressStep Rest $ rep p
            pure (x : xs)
       _ -> empty

-- | Manually override the focus. Use this with care - it can lead to
-- bogus error selection unless 'withProgress' is used to provide an
-- appropriate path.
parse :: MonadSyntax atom m => Syntax atom -> m a -> m a
parse = withFocus

-- | Match a list focus elementwise.
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
          do x <- withFocus e $ withProgressStep First p
             xs <- withFocus (Syntax (Posd loc (List es))) $
                   withProgressStep Rest $
                   list' ps
             pure (x : xs)

-- | Transform a parser such that its errors are considered to occur
-- after others, and thus be reported with a higher priority.
later :: MonadSyntax atom m => m a -> m a
later = withProgressStep Late

-- | Impose a side condition on a parser, failing with the given
-- description if the side condition is 'Nothing'.
sideCondition :: MonadSyntax atom m => Text -> (a -> Maybe b) -> m a -> m b
sideCondition !msg ok p =
  do x <- p
     case ok x of
       Just y -> pure y
       Nothing ->
         later $ describe msg empty

-- | Impose a Boolean side condition on a parser, failing with the
-- given description if the side condition is 'False'.
sideCondition' :: MonadSyntax atom m => Text -> (a -> Bool) -> m a -> m a
sideCondition' !msg ok p = sideCondition msg (\x -> if ok x then Just x else Nothing) p


-- | Syntax errors explain why the error occurred.
data SyntaxError atom = SyntaxError (NonEmpty (Reason atom))
  deriving (Show, Eq)

-- | Convert an internal error structure into a form suitable for
-- humans to read.
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

-- | Attempt to parse the given piece of syntax, returning the first success found,
--   or the error(s) with the greatest progress otherwise.
syntaxParseIO :: IsAtom atom => SyntaxParse atom a -> Syntax atom -> IO (Either (SyntaxError atom) a)
syntaxParseIO p stx = do
  (P yes no) <-
        runSTP $ runReaderT (runSyntaxParse p) $
          SyntaxParseCtx (Progress []) (Reason stx (T.pack "bad syntax")) stx
  case Foldable.toList yes of
    [] ->
      return $ Left $ SyntaxError $
        case no of
          Ok        -> error "Internal error: no reason provided, yet no successful parse found."
          Oops _ rs -> rs
    (r:_) -> return $ Right r

-- | When the current focus is a list, reverse its contents while
-- invoking another parser. If it is not a list, fail.
backwards :: MonadSyntax atom m => m a -> m a
backwards p =
  do foc <- anything
     case foc of
      l@(L xs) -> withFocus (Syntax (Posd (syntaxPos l) (List (reverse xs)))) p
      _ -> empty

-- | Trivially succeed, but prevent backtracking.
commit :: MonadSyntax atom m => m ()
commit = pure () <|> cut

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
