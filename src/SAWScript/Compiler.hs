{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.Compiler ( Compiler, compiler, runCompiler
                          , Err, runErr, runErr'
                          , ErrT, runErrT, runErrT', mapErrT
                          ) where

import Control.Applicative (Alternative, Applicative)
import Control.Monad (MonadPlus)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Class (MonadTrans)
import Control.Monad.Trans.Error (ErrorT, mapErrorT, runErrorT)

import Text.Show.Pretty (ppShow)

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

{-| This is a slightly unusual formulation--'Err' is defined in terms of
'ErrT', but the inner monad is 'IO', not 'Identity'--for backward compatibility
reasons. -}
-- TODO: Make 'Err' use 'Identity' instead of 'IO'.
type Err = ErrT IO

newtype ErrT m b = ErrT { extractErrorT :: ErrorT String m b }
                 deriving (Functor, Applicative, Alternative, Monad, MonadPlus,
                           MonadIO, MonadTrans)

{-| 'runErr' uses continuation-passing style for backward compatibility. -}
-- TODO: Get rid of this.
runErr :: Err a -> (String -> IO r) -> (a -> IO r) -> IO r
runErr = runErrT

runErr' :: Err a -> IO (Either String a)
runErr' = runErrT'

{-| 'runErrT' uses continuation-passing style to present a interface uniform
with 'runErr'. -}
-- TODO: Once 'runErr' has been eliminated, replace this with 'runErrT''.
runErrT :: (Monad m) => ErrT m a -> (String -> m r) -> (a -> m r) -> m r
runErrT m fl sc = do
  result <- runErrT' m
  either fl sc result

runErrT' :: (Monad m) => ErrT m a -> m (Either String a)
runErrT' = runErrorT . extractErrorT

mapErrT :: (m (Either String a) -> n (Either String b)) -> ErrT m a -> ErrT n b
mapErrT f = ErrT . mapErrorT f . extractErrorT

compiler :: Show a => String -> Compiler a b -> Compiler a b
compiler name comp input = do
  result <- liftIO $ runErrorT $ extractErrorT $ comp input
  ErrT $ case result of
    Left err -> fail $
      unlines [ name ++ ": " ++ err
              , "in:"
              , ppShow input ]
    Right r -> return r
