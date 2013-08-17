{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.Compiler where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Error (ErrorT, runErrorT)
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

newtype Err b = Err { extractErrorT :: ErrorT String IO b }
              deriving (Functor, Applicative, Alternative, Monad, MonadPlus,
                        MonadIO)

runErr :: Err a -> (String -> IO r) -> (a -> IO r) -> IO r
runErr m fl sc = do
  result <- runErrorT $ extractErrorT m
  either fl sc result

compiler :: Show a => String -> Compiler a b -> Compiler a b
compiler name comp input = do
  result <- liftIO $ runErrorT $ extractErrorT $ comp input
  Err $ case result of
    Left err -> fail $
      unlines [ name ++ ": " ++ err
              , "in:"
              , ppShow input ]
    Right r -> return r
