{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.REPL.Monad ( REPLState, emptyState
                            , REP, runREP
                            , REPResult(..), successExit, failure
                            , io, haskeline, err) where

import Control.Applicative (Applicative)
import Control.Monad.Trans (lift, MonadIO, liftIO)
import Control.Monad.State (StateT, runStateT)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.Compiler (ErrT, runErrT', mapErrT)


--------------------------------- REPL state ----------------------------------

type REPLState = ()

emptyState :: REPLState
emptyState = ()


-------------------------------- REPL results ---------------------------------

data REPResult = Success REPLState
               | SuccessExit
               | Failure
               deriving (Eq, Show)


-------------------------------- The REP monad --------------------------------

{-| The 'REP' ("read-eval-print") monad encapsulates one iteration of the
read-eval-print loop. -}
newtype REP a =
  REP { extractInner :: MaybeT (StateT REPLState
                                       (ErrT (InputT IO))) a }
  deriving (Functor, Applicative, Monad)

runREP :: forall a.
          Haskeline.Settings IO
          -> REPLState
          -> REP a
          -> IO REPResult
runREP haskelineSettings initialState computation = do
  unwrapped :: Either String (Maybe a, REPLState)
            <- runInputT haskelineSettings .
                 runErrT' .
                   flip runStateT initialState .
                     runMaybeT .
                       extractInner $ computation
  case unwrapped of
    Right (Just _, finalState) -> return $ Success finalState
    Right (Nothing, _) -> return SuccessExit
    Left msg -> do
      runInputT haskelineSettings $ Haskeline.outputStrLn msg
      return Failure


-- Monadic primitives --

successExit :: REP a
successExit = REP $ fail "Exiting" -- message should be ignored

failure :: String -> REP a
failure msg = REP $ lift $ lift $ fail msg



-- Lifting computations --
{- 'REP' isn't a monad transformer, but inner monads can still be lifted to
it. -}

io :: IO a -> REP a
io = REP . lift . lift . lift . liftIO

haskeline :: InputT IO a -> REP a
haskeline = REP . lift . lift . lift

err :: ErrT IO a -> REP a
err = REP . lift . lift . mapErrT liftIO
