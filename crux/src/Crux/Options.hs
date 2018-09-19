{- |
Module      : Crux.Options
Description : Datatype for command-line options.
License     : BSD3
Maintainer  : sweirich
Stability   : provisional
-}

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE RankNTypes          #-}

module Crux.Options(CruxOptions(..),processOptionsThen,pathDesc,pathDelim) where

import Data.List (foldl',lookup)

import System.Console.GetOpt
import System.Environment
import System.FilePath
--import Text.Show.Functions ()
import System.IO
import Data.Typeable

import           Crux.Language (LangConf(..),LangOptions,Language,Options,CruxOptions(..))
import qualified Crux.Language as CL

defaultCruxOptions :: CruxOptions
defaultCruxOptions = CruxOptions {
    importPath = ["."]
  , simVerbose = 1
  , outDir = "report" 
  , inputFile = ""
  , showHelp = False
  , showVersion = False
  , printShowPos = False
  }

type AllPossibleOptions = (CruxOptions, [LangConf])

defaultOptions :: [LangConf] -> AllPossibleOptions
defaultOptions langs = (defaultCruxOptions, langs)


cmdLineCruxOptions :: [OptDescr (CruxOptions -> CruxOptions)]
cmdLineCruxOptions =
  [ Option "h?" ["help"]
    (NoArg (\opts -> opts { showHelp = True }))
    "Print this help message"
  , Option "V" ["version"]
    (NoArg (\opts -> opts { showVersion = True }))
    "Show the version of the tool"
  , Option "i" ["import-path"]
    (ReqArg
     (\p opts -> opts { importPath = importPath opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option [] ["output-locations"]
    (NoArg
     (\opts -> opts { printShowPos = True }))
     "Show the source locations that are responsible for output."
  , Option "d" ["sim-verbose"]
    (ReqArg
     (\v opts -> opts { simVerbose = read v })
     "num"
    )
    "Set simulator verbosity level"
  ]

promoteLang :: forall a. Language a => (CL.LangOptions a -> CL.LangOptions a)
                                -> (AllPossibleOptions -> AllPossibleOptions)
promoteLang g = \ (c,opts) -> (c, go opts)  
   where 
          go [] = []
          go ( l@(LangConf lopts): rest) =
            case cast lopts of
              Just lopts' -> LangConf (g lopts') : rest
              Nothing     -> l : go rest

cmdLineOptions :: [LangConf] -> [OptDescr (AllPossibleOptions -> AllPossibleOptions)]
cmdLineOptions langs = map (fmap promoteCruxOptions) cmdLineCruxOptions
                       ++ concat (map langCLOpts langs)
  where
    promoteCruxOptions f =  \(c,others) -> (f c, others)  
    langCLOpts (LangConf (_ :: LangOptions a)) = fmap (fmap promoteLang) (CL.cmdLineOptions @a)  



processEnv :: forall a. Language a => Options a -> IO (Options a)
processEnv opts = do
  curEnv <- getEnvironment
  return $ foldr addOpt opts curEnv
    where addOpt :: (String, String) -> Options a -> Options a
          addOpt ("IMPORT_PATH", p) (co,lo) =
            (co { importPath = importPath co ++ splitSearchPath p }, lo)
          addOpt (var,val) (co,lo) =
            case lookup var CL.envOptions of
              Just f  -> (co, f val lo)
              Nothing -> (co, lo)

findLang :: AllPossibleOptions -> FilePath -> Maybe LangConf
findLang (_,langs) file = go langs where
  go [] = Nothing
  go (lang@(LangConf (_:: LangOptions a)):rest) 
    | takeExtension file `elem` CL.validExtensions @a = Just lang
    | otherwise = go rest

  


-- If there is only one possible language, then add that to the name
-- of the executable. Otherwise, just use 'crux'
exeName :: [LangConf] -> String
exeName langs = case langs of
  [LangConf (_ :: LangOptions a)] -> "crux-" ++ CL.name @a
  _ -> "crux"

shortVersionText :: [LangConf] -> String
shortVersionText langs = exeName langs ++ "-0.1"

-- | Process all options, starting with the default options,
--   and then setting them via commandline, environment variables,
--   and general IO-setting functions
processOptionsThen :: [LangConf] -> (forall a. Language a => Options a -> IO ()) -> IO ()
processOptionsThen langs check = do
  hSetBuffering stdout LineBuffering
  argv <- getArgs
  case getOpt Permute options argv of
    (opts1, files, []) -> do
      let allOpts = foldl' (flip id) (defaultOptions langs) opts1
      case files of
        _ | showVersion (fst allOpts) -> hPutStrLn stderr (shortVersionText langs)
        _ | showHelp    (fst allOpts) -> hPutStrLn stderr usageMsg
        [file] -> do
          case findLang allOpts file of
            Just (LangConf (langOpts :: LangOptions a)) -> do
              opts <- processEnv ((fst allOpts) { inputFile = file }, langOpts)
              opts' <- CL.ioOptions opts
              check opts'
            Nothing -> hPutStrLn stderr $ "Unknown file extension" ++ takeExtension file
        _ -> hPutStrLn stderr usageMsg
    (_, _, errs) -> hPutStrLn stderr (concat errs ++ usageMsg)
  where options = cmdLineOptions langs
        header   = "Usage: " ++ (exeName langs) ++ " [OPTION...] file"
        usageMsg = usageInfo header options


{-           
promote g = \ opts -> opts { langConfs = go (langConfs opts) } 
   where 
          go [] = []
          go ( l@(LangConf lopts): rest) =
            case cast lopts of
              Just lopts' -> LangConf (g lopts') : rest
              Nothing     -> l : go rest -}
{-
promoteM :: (Monad m, Language a) => (CL.LangOptions a -> m (CL.LangOptions a))
                                  -> (Options a -> m (Options a))
promoteM = undefined
-}
{-            
promoteM g = \ opts -> go (langConfs opts) >>= \opts' -> return $ opts { langConfs = opts' } 
   where 
          go [] = return []
          go ( l@(LangConf lopts): rest) =
            case cast lopts of
              Just lopts' -> do
                conf' <- (g lopts')
                return (LangConf conf' : rest)
              Nothing     -> (l:) <$> go rest
-}
  



-- Lookup a language specific treatment of an environment variable
{-
findVar :: String -> String -> [LangConf] -> (CruxOptions -> CruxOptions)
findVar _ _ [] = id
findVar var val (LangConf (_:: LangOptions a) : rest) =
  case lookup var (CL.envOptions @a) of
    Just f -> promote (f val) . findVar var val rest
    Nothing -> findVar var val rest
-}



pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif
