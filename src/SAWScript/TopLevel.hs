{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.TopLevel
  ( Env(..)
  , readSBV
  , readSBVWith
  , writeAIG
  , writeSMT
  ) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Set as Set
import qualified Data.Vector.Storable as SV
import SMTLib1.PP

import Verifier.SAW.BitBlast
import Verifier.SAW.Export.SmtLibTrans
import Verifier.SAW.SBVParser
import Verifier.SAW.SharedTerm
import Verinf.Symbolic

type Trm = SharedTerm ()

data Env =
  Env
  { envSC :: SharedContext ()
  , envBE :: BitEngine Lit
  }

newtype TopLevel a = TopLevel (ReaderT Env (ErrorT String IO) a)
  deriving (Applicative, Functor, Monad,
           MonadError String, MonadReader Env, MonadIO)

readSBV :: FilePath -> TopLevel Trm
readSBV = readSBVWith (\_ _ -> Nothing)

readSBVWith :: (String -> Typ -> Maybe Trm) -> FilePath -> TopLevel Trm
readSBVWith um f = do
  sc <- envSC <$> ask
  liftIO $ parseSBVPgm sc um =<< loadSBV f

writeAIG :: FilePath -> Trm -> TopLevel ()
writeAIG f t = do
  be <- envBE <$> ask
  mbterm <- liftIO $ bitBlast be t
  case mbterm of
    Nothing -> fail "Can't bitblast."
    Just bterm -> do
      ls <- case bterm of
              BNat _ -> fail "Won't convert literal number to AIG for now"
              BBool l -> return $ SV.singleton l
              BVector ls -> return ls
      liftIO $ beWriteAigerV be f [ls]

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
