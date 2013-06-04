{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SAWScript.TopLevel
  ( Env(..)
  , TopLevel
  , runTopLevel
  , runTopLevel'
  , extractLLVM
  , readSBV
  , readSBVWith
  , writeAIG
  --, writeSMT
  ) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Vector.Storable as SV
import SMTLib1

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
      outs <- case bterm of
              BBool l -> return $ SV.singleton l
              BVector ls -> return ls
      ins <- liftIO $ beInputLits be
      liftIO $ beWriteAigerV be f ins outs

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

-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all
-- arguments and returns a term representing the return value. Some
-- verifications will require more complex execution contexts.
extractLLVM :: FilePath -> String -> TopLevel Trm
extractLLVM file func = do
  mdl <- liftIO $ L.loadModule file
  let dl = L.parseDataLayout $ LLVM.modDataLayout mdl
      mg = L.defaultMemGeom dl
      sym = L.Symbol func
  be <- envBE <$> ask
  (sbe, mem) <- liftIO $ L.createSAWBackend be dl mg
  cb <- liftIO $ L.mkCodebase sbe dl mdl
  case L.lookupDefine sym cb of
    Nothing -> fail $ "Bitcode file " ++ file ++
                      " does not contain symbol " ++ func ++ "."
    Just md -> liftIO $ L.runSimulator cb sbe mem L.defaultSEH Nothing $ do
      setVerbosity 0
      args <- mapM freshArg (L.sdArgs md)
      L.callDefine_ sym (L.sdRetType md) args
      mrv <- L.getProgramReturnValue
      case mrv of
        Nothing -> fail "No return value from simulated function."
        Just rv -> return rv

freshArg :: (L.Ident, L.MemType)
         -> L.Simulator (L.SAWBackend () Lit) IO (L.MemType, Trm)
freshArg (_, ty@(L.IntType bw)) = do
  sbe <- gets L.symBE
  tm <- L.liftSBE $ L.freshInt sbe bw
  return (ty, tm)
freshArg (_, _) = fail "Only integer arguments are supported for now."
