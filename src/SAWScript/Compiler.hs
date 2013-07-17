{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
module SAWScript.Compiler where

import Control.Applicative
import Control.Monad
#if __GLASGOW_HASKELL__ < 706
import Prelude hiding (catch)
#endif

import Text.Show.Pretty

import SAWScript.Utils

-- | Wrapper around compiler function to format the result or error
runCompiler :: (Show b) => Compiler a b -> a -> (b -> IO ()) -> IO ()
runCompiler f a k = do
  runErr (f a)
    reportError
    k -- continuation

reportError :: String -> IO ()
reportError = putStrLn . ("Error\n" ++) . indent 2

type Compiler a b = a -> Err b

newtype Err a = Err { runErr :: forall r. (String -> r) -> (a -> r) -> r }

instance Functor Err where
  fmap f m = Err $ \ fl sc -> runErr m fl (sc . f)

instance Monad Err where
  return a = Err $ \ _  sc -> sc a
  m >>= k  = Err $ \ fl sc ->
    runErr m fl $ \ a ->
      runErr (k a) fl sc
  fail str = Err $ \ fl _  -> fl str

instance MonadPlus Err where
  mzero = fail "mzero"
  m1 `mplus` m2 = Err $ \ fl sc ->
    runErr m1 (\err -> runErr m2 (\err' -> fl (err ++ "\n" ++ err')) sc) sc

instance Applicative Err where
  pure = return
  (<*>) = ap

instance Alternative Err where
  empty = mzero
  (<|>) = mplus

--after :: IO () -> Compiler a b -> Compiler a b
--after m pass = pass `onFailure` (\f' s -> m >> f' s) `onSuccess` (\f' res -> m >> f' res)

onFailure :: Compiler a b -> (forall r. (String -> r) -> String -> r) -> Compiler a b
(pass `onFailure` handler) input = Err $ \fl sc -> runErr (pass input) (handler fl) sc

onSuccess :: Compiler a b -> (forall r. (b -> r) -> b -> r) -> Compiler a b
(pass `onSuccess` handler) input = Err $ \fl sc -> runErr (pass input) fl (handler sc)

onFailureRes :: Err a -> (forall r. (String -> r) -> String -> r) -> Err a
m `onFailureRes` handler = Err $ \fl sc -> runErr m (handler fl) sc

compiler :: Show a => String -> Compiler a b -> Compiler a b
compiler name comp input = onFailureRes (comp input) $ \fl err ->
  fl $ unlines [name ++ ": " ++ err, "in:",ppShow input]

