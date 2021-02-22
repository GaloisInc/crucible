module Crux.Polyglot.Config
  (
    PolyglotOptions
  , cruxPolyglotConfig
  , processPolyglotOpts
  , llvmPGOpts
  )
where

import System.Directory ( createDirectoryIfMissing )

import qualified Crux.LLVM.Config as CLCfg

import qualified Crux
import qualified Crux.Config as CC


type PolyglotOptions = (CLCfg.LLVMOptions, PolyglotLocalOptions)

data PolyglotLocalOptions = PolyglotLocalOptions

defaultPolyglotOptions :: PolyglotLocalOptions
defaultPolyglotOptions = PolyglotLocalOptions

cruxPolyglotConfig :: IO (Crux.Config PolyglotOptions)
cruxPolyglotConfig =
  let plygltCfg = Crux.Config
                  {
                    Crux.cfgFile = pure defaultPolyglotOptions
                  , Crux.cfgEnv = []
                  , Crux.cfgCmdLineFlag = []
                  }
  in do llvmCfg <- CLCfg.llvmCruxConfig
        return $ CC.cfgJoin llvmCfg plygltCfg


processPolyglotOpts :: (Crux.CruxOptions, PolyglotOptions)
                    -> IO (Crux.CruxOptions, PolyglotOptions)
processPolyglotOpts (cruxOpts, polyOpts) = do
  let cruxOpts2 = if null $ Crux.outDir cruxOpts
                  then cruxOpts { Crux.outDir = "results/polyglot" }
                  else cruxOpts
      odir = Crux.outDir cruxOpts2
  createDirectoryIfMissing True odir
  return (cruxOpts2, polyOpts)


llvmPGOpts :: PolyglotOptions -> CLCfg.LLVMOptions
llvmPGOpts (llvmOpts,_) = llvmOpts
