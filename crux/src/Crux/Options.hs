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
import Data.Maybe( fromMaybe )

import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.IO
import Text.Read (readMaybe)
import Data.Typeable

import Crux.Language (LangConf(..),LangOptions,Language,Options,CruxOptions(..))
import qualified Crux.Language as CL

-- Unfortunately, we need to construct these arguments *before* we
-- know what the inputFile name is. So we cannot provide a default
-- value of outDir here.
defaultCruxOptions :: CruxOptions
defaultCruxOptions = CruxOptions {
    showHelp = False
  , simVerbose = 1
  , outDir = ""
  , inputFile = ""
  , showVersion = False
  , checkPathSat = False
  , profileCrucibleFunctions = True
  , profileSolver = True
  , globalTimeout = Nothing
  , goalTimeout = 60
  , profileOutputInterval = Nothing
  , loopBound = Nothing
  , makeCexes = True
  }

-- | All possible options that could be set from the command line.
-- These include the Crux options, plus all options from any language
-- (We don't know the language yet)
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

  , Option "d" ["sim-verbose"]
    (ReqArg
     (\v opts -> opts { simVerbose = read v })
     "num"
    )
    "Set simulator verbosity level"

  , Option [] ["path-sat"]
    (NoArg
     (\opts -> opts { checkPathSat = True }))
    "Enable path satisfiability checking"

  , Option [] ["output-directory"]
    (OptArg (\mv opts -> maybe opts (\v -> opts { outDir = v }) mv)
    "DIR")
    "Location for reports. If unset, no reports will be generated."

  , Option [] ["no-profile-crucible"]
    (NoArg
     (\opts -> opts { profileCrucibleFunctions = False }))
    "Disable profiling of crucible function entry/exit"

  , Option [] ["no-profile-solver"]
    (NoArg
     (\opts -> opts { profileSolver = False }))
    "Disable profiling of solver events"

  , Option "t" ["timeout"]
    (OptArg
     (\v opts -> opts{ globalTimeout = Just (fromMaybe "60" v) })
     "seconds")
    "Stop executing the simulator after this many seconds (default: 60 seconds)"

  , Option [] ["goal-timeout"]
    (ReqArg
     (\v opts -> case readMaybe v of
                   Just t -> opts{ goalTimeout = t }
                   Nothing -> opts)
     "seconds")
    "Stop trying to prove each goal after this many seconds (default: 10 seconds, 0 for none)"

  , Option "p" ["profiling-period"]
    (OptArg
      (\v opts -> opts{ profileOutputInterval = Just (fromMaybe "5" v) })
      "seconds")
    "Time between intermediate profile data reports (default: 5 seconds)"

  , Option "i" ["iteration-bound"]
    (ReqArg (\v opts -> opts { loopBound = Just v })
      "iterations")
    "Bound all loops to at most this many iterations"

  , Option "x" ["no-execs"]
    (NoArg
     (\opts -> opts { makeCexes = False }))
    "Disable generating counter-example executables"
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
                       ++ concatMap langCLOpts langs
  where
    promoteCruxOptions f =  \(c,others) -> (f c, others)
    langCLOpts (LangConf (_ :: LangOptions a)) = fmap (fmap promoteLang) (CL.cmdLineOptions @a)


-- Look for environment variable sto set options
processEnv :: forall a. Language a => Options a -> IO (Options a)
processEnv opts = do
  curEnv <- getEnvironment
  return $ foldr addOpt opts curEnv
    where addOpt :: (String, String) -> Options a -> Options a
          -- add crux environment variable lookup here
          addOpt (var,val) (co,lo) =
            case lookup var CL.envOptions of
              Just f  -> (co, f val lo)
              Nothing -> (co, lo)

-- Figure out which language we should use for simulation
-- based on the file extension
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
              opts  <- processEnv ((fst allOpts) { inputFile = file }, langOpts)
              opts' <- CL.ioOptions opts
              check opts'
            Nothing -> hPutStrLn stderr $ "Unknown file extension " ++ takeExtension file
        _ -> hPutStrLn stderr usageMsg
    (_, _, errs) -> hPutStrLn stderr (concat errs ++ usageMsg)
  where options  = cmdLineOptions langs
        header   = "Usage: " ++ (exeName langs) ++ " [OPTION...] file"
        usageMsg = usageInfo header options



pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif