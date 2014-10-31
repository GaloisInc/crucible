{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.Compiler ( Compiler, compiler
                          , Err, runErr
                          , ErrT, runErrT, mapErrT
                          , reportErrT
                          , liftParser
                          ) where

import Control.Applicative (Alternative, Applicative)
import Control.Monad (MonadPlus)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Class (MonadTrans)
import Control.Monad.Trans.Except (ExceptT, mapExceptT, runExceptT)

import SAWScript.AST (PrettyPrint, pShow)
import SAWScript.Parser (ParseError)

-- | Run an ErrT computation; fail with a formatted message upon error.
reportErrT :: (MonadIO io, Show a) => ErrT io a -> io a
reportErrT m = do
  result <- runErrT m
  case result of
    Left msg -> reportError msg
    Right b  -> return b

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines

reportError :: (MonadIO io) => String -> io a
reportError = error . ("Error\n" ++) . indent 2
--reportError = liftIO . putStrLn . ("Error\n" ++) . indent 2

type Compiler a b = a -> Err b

{-| This is a slightly unusual formulation--'Err' is defined in terms of
'ErrT', but the inner monad is 'IO', not 'Identity'--for backward compatibility
reasons. -}
-- TODO: Make 'Err' use 'Identity' instead of 'IO'.
type Err = ErrT IO

newtype ErrT m b = ErrT { extractExceptT :: ExceptT String m b }
                 deriving (Functor, Applicative, Alternative, Monad, MonadPlus,
                           MonadIO, MonadTrans)

runErr :: Err a -> IO (Either String a)
runErr = runErrT

runErrT :: (Monad m) => ErrT m a -> m (Either String a)
runErrT = runExceptT . extractExceptT

mapErrT :: (m (Either String a) -> n (Either String b)) -> ErrT m a -> ErrT n b
mapErrT f = ErrT . mapExceptT f . extractExceptT

compiler :: PrettyPrint a => String -> Compiler a b -> Compiler a b
compiler name comp input = do
  result <- liftIO $ runExceptT $ extractExceptT $ comp input
  ErrT $ case result of
    Left err -> fail $ err ++ " in " ++ pShow input
    Right r -> return r

liftParser :: (a -> Either ParseError b) -> Compiler a b
liftParser p x =
  case p x of
    Left err  -> fail (show err)
    Right res -> return res
