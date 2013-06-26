{-# LANGUAGE CPP #-}
module SAWScript.Compiler where

import Control.Applicative
import Control.Monad
import Data.List (intercalate)
#if __GLASGOW_HASKELL__ < 706
import Prelude hiding (catch)
#endif

import SAWScript.Utils

-- | Wrapper around compiler function to format the result or error
runCompiler :: (Show b) => Compiler a b -> a -> (b -> IO ()) -> IO ()
runCompiler f a k = do
  runE (f a)
    reportError
    k -- continuation

reportError :: String -> IO ()
reportError = putStrLn . ("Error\n" ++) . indent 2

type Compiler a b = a -> Err b

type Err = E (IO ())

newtype E r a = E { runE :: (String -> r) -> (a -> r) -> r }

instance Functor (E r) where
  fmap f m = E $ \ fl sc -> runE m fl (sc . f)

instance Monad (E r) where
  return a = E $ \ _  sc -> sc a
  m >>= k  = E $ \ fl sc ->
    runE m fl $ \ a ->
      runE (k a) fl sc
  fail str = E $ \ fl _  -> fl str

instance MonadPlus (E r) where
  mzero = fail "mzero"
  m1 `mplus` m2 = E $ \ fl sc ->
    runE m1 (\err -> runE m2 (\err' -> fl (err ++ "\n" ++ err')) sc) sc

instance Applicative (E r) where
  pure = return
  (<*>) = ap

instance Alternative (E r) where
  empty = mzero
  (<|>) = mplus

onFailure :: Compiler a b -> ((String -> IO ()) -> String -> IO ()) -> Compiler a b
(pass `onFailure` handler) input = E $ \fl sc -> runE (pass input) (handler fl) sc

onSuccess :: Compiler a b -> ((b -> IO ()) -> b -> IO ()) -> Compiler a b
(pass `onSuccess` handler) input = E $ \fl sc -> runE (pass input) fl (handler sc)

onFailureRes :: E r a -> ((String -> r) -> String -> r) -> E r a
m `onFailureRes` handler = E $ \fl sc -> runE m (handler fl) sc

compiler :: Show a => String -> Compiler a b -> Compiler a b
compiler name comp input = onFailureRes (comp input) $ \fl err ->
  fl $ intercalate "\n" [name ++ ": " ++ err, "in:",show input]

