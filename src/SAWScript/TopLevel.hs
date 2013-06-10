{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.TopLevel
  ( Env(..)
  , TopLevel
  , runTopLevel
  , runTopLevel'
  ) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Vector.Storable as SV

import qualified Text.LLVM as LLVM
import qualified Verifier.LLVM.AST as L
import qualified Verifier.LLVM.Backend as L
import qualified Verifier.LLVM.Codebase as L
import qualified Verifier.LLVM.SAWBackend as L
import qualified Verifier.LLVM.Simulator as L

import Verifier.SAW
import Verifier.SAW.BitBlast
--import Verifier.SAW.Export.SmtLibTrans
import Verifier.SAW.SBVParser

import Verinf.Symbolic
import Verinf.Utils.LogMonad

type Trm = SharedTerm ()

data Env =
  Env
  { envSC :: SharedContext ()
  , envBE :: BitEngine Lit
  }

newtype TopLevel a = TopLevel (ReaderT Env (ErrorT String IO) a)
  deriving (Applicative, Functor, Monad,
           MonadError String, MonadReader Env, MonadIO)

runTopLevel :: TopLevel a -> IO (Either String a)
runTopLevel (TopLevel a) = do
  be <- createBitEngine
  sc <- mkSharedContext preludeModule
  let env = Env { envSC = sc, envBE = be }
  runErrorT (runReaderT a env)

runTopLevel' :: TopLevel a -> IO a
runTopLevel' a = do
  r <- runTopLevel a
  case r of
    Left err -> fail err
    Right res -> return res


{-
writeSMT :: FilePath -> Trm -> TopLevel ()
writeSMT f t = do
  sc <- envSC <$> ask
  let transParams =
        TransParams
        { transName = undefined
        , transInputs = undefined
        , transAssume = undefined
        , transCheck = [t]
        , transEnabled = Set.empty
        , transExtArr = False
        , transContext = sc
        }
  (scr, _) <- liftIO $ translate transParams
  liftIO . writeFile f . show . pp $ scr
-}

