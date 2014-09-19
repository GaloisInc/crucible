{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.Compiler ( Compiler, compiler, runCompiler
                          , Err, runErr
                          , ErrT, runErrT, mapErrT
                          , liftParser
                          ) where

import Control.Applicative (Alternative, Applicative)
import Control.Monad (MonadPlus)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Class (MonadTrans)
import Control.Monad.Trans.Error (ErrorT, mapErrorT, runErrorT)

import SAWScript.AST (PrettyPrint, pShow)
import SAWScript.Parser (ParseError)

-- | Wrapper around compiler function to format the result or error
runCompiler :: (Show b, MonadIO io)
               => (a -> ErrT io b) {- This is effectively a supertype of
                  'Compiler a b'--it allows you to use any 'MonadIO', not just
                  'IO' itself. -}
               -> a
               -> (b -> io ())
               -> io ()
runCompiler f a k = do
  result <- runErrT (f a)
  case result of
    Left msg -> reportError msg
    Right b  -> k b

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines

reportError :: (MonadIO io) => String -> io ()
reportError = fail . ("Error\n" ++) . indent 2
--reportError = liftIO . putStrLn . ("Error\n" ++) . indent 2

type Compiler a b = a -> Err b

{-| This is a slightly unusual formulation--'Err' is defined in terms of
'ErrT', but the inner monad is 'IO', not 'Identity'--for backward compatibility
reasons. -}
-- TODO: Make 'Err' use 'Identity' instead of 'IO'.
type Err = ErrT IO

newtype ErrT m b = ErrT { extractErrorT :: ErrorT String m b }
                 deriving (Functor, Applicative, Alternative, Monad, MonadPlus,
                           MonadIO, MonadTrans)

runErr :: Err a -> IO (Either String a)
runErr = runErrT

runErrT :: (Monad m) => ErrT m a -> m (Either String a)
runErrT = runErrorT . extractErrorT

mapErrT :: (m (Either String a) -> n (Either String b)) -> ErrT m a -> ErrT n b
mapErrT f = ErrT . mapErrorT f . extractErrorT

compiler :: PrettyPrint a => String -> Compiler a b -> Compiler a b
compiler name comp input = do
  result <- liftIO $ runErrorT $ extractErrorT $ comp input
  ErrT $ case result of
    Left err -> fail $
      unlines [ name ++ ": " ++ err
              , "in:"
              , pShow input ]
    Right r -> return r

liftParser :: (a -> Either ParseError b) -> Compiler a b
liftParser p x =
  case p x of
    Left err  -> fail (show err)
    Right res -> return res
