
module SAWScript.Compiler where

import SAWScript.Unify (foldMuM)

import Control.Applicative
import Control.Monad
import Data.List (intercalate)
import Data.Traversable

type Compiler a b = a -> Err b

type Err = E (IO ())

newtype E r a = E { runE :: (String -> r) -> (a -> r) -> r }

instance Functor (E r) where
  fmap f m = E $ \ fl sc -> runE m fl (sc . f)

instance Monad (E r) where
  return a = E $ \ _  sc -> sc a
  m >>= k  = E $ \ fl sc ->
    runE m fl $ \a ->
      runE (k a) fl sc
  fail str = E $ \ fl _  -> fl str

instance MonadPlus (E r) where
  mzero = fail "mzero"
  m1 `mplus` m2 = E $ \ fl sc ->
    runE m1 (\str -> runE m2 fl sc) sc

instance Applicative (E r) where
  pure = return
  (<*>) = ap

instance Alternative (E r) where
  empty = mzero
  (<|>) = mplus

catch :: E r a -> ((String -> r) -> String -> r) -> E r a
m `catch` handler = E $ \ fl sc -> runE m (handler fl) sc

compiler :: Show a => String -> Compiler a b -> Compiler a b
compiler name comp input = catch (comp input) $ \fl err ->
  fl $ intercalate "\n" [name ++ ": " ++ err, "in:",show input]

