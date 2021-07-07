{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Crux.LLVM.Compile where

import           Control.Applicative
import           Control.Exception ( SomeException(..), try )
import           Control.Monad ( guard, unless, when, forM_ )
import           Control.Monad.Logic ( observeAll )
import qualified Data.Foldable as Fold
import           Data.List ( intercalate, isSuffixOf )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import           System.Directory ( doesFileExist, removeFile
                                  , createDirectoryIfMissing, copyFile )
import           System.Exit ( ExitCode(..) )
import           System.FilePath ( takeExtension, (</>), (-<.>)
                                 , takeDirectory, takeFileName )
import           System.Process ( readProcess, readProcessWithExitCode )

import           What4.Interface
import           What4.ProgramLoc

import           Lang.Crucible.Simulator.SimError

import           Crux
import qualified Crux.Config.Common as CC
import           Crux.Model ( toDouble, showBVLiteral, showFloatLiteral
                            , showDoubleLiteral )
import           Crux.Types

import           Crux.LLVM.Config
import qualified Crux.LLVM.Log as Log


isCPlusPlus :: FilePath -> Bool
isCPlusPlus file =
  case takeExtension file of
    ".cpp" -> True
    ".cxx" -> True
    ".C" -> True
    ".bc" -> False
    _ -> False

anyCPPFiles :: [FilePath] -> Bool
anyCPPFiles = any isCPlusPlus

-- | attempt to find Clang executable by searching the file system
-- throw an error if it cannot be found this way.
-- (NOTE: do not look for environment var "CLANG". That is assumed
--  to be tried already.)
getClang :: IO FilePath
getClang = attempt (map inPath clangs)
  where
  inPath x = head . lines <$> readProcess "/usr/bin/which" [x] ""
  clangs   = [ "clang", "clang-4.0", "clang-3.6", "clang-3.8", "clang-7", "clang-8" ]

  attempt :: [IO FilePath] -> IO FilePath
  attempt ms =
    case ms of
      [] -> throwCError $ EnvError $
              unlines [ "Failed to find `clang`."
                      , "You may use CLANG to provide path to executable."
                      ]
      m : more -> do x <- try m
                     case x of
                       Left (SomeException {}) -> attempt more
                       Right a -> return a

runClang ::
  Logs msgs =>
  Log.SupportsCruxLLVMLogMessage msgs =>
  LLVMOptions -> [String] -> IO ()
runClang llvmOpts params =
  do let clang = clangBin llvmOpts
         allParams = clangOpts llvmOpts ++ params
     Log.sayCruxLLVM (Log.ClangInvocation (T.pack <$> (clang : map show allParams)))
     (res,sout,serr) <- readProcessWithExitCode clang allParams ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)

llvmLink :: LLVMOptions -> [FilePath] -> FilePath -> IO ()
llvmLink llvmOpts ins out =
  do let params = ins ++ [ "-o", out ]
     (res, sout, serr) <- readProcessWithExitCode (linkBin llvmOpts) params ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)

parseLLVMLinkVersion :: String -> String
parseLLVMLinkVersion = go . map words . lines
  where
    go (("LLVM" : "version" : version : _) : _) = version
    go (_ : rest) = go rest
    go [] = ""

llvmLinkVersion :: LLVMOptions -> IO String
llvmLinkVersion llvmOpts =
  do (res, sout, serr) <- readProcessWithExitCode (linkBin llvmOpts) ["--version"] ""
     case res of
       ExitSuccess   -> return (parseLLVMLinkVersion sout)
       ExitFailure n -> throwCError (ClangError n sout serr)

-- | Generates compiled LLVM bitcode for the set of input files
-- specified in the 'CruxOptions' argument, writing the output to a
-- pre-determined filename in the build directory specified in
-- 'CruxOptions'.
genBitCode ::
  Logs msgs =>
  Log.SupportsCruxLLVMLogMessage msgs =>
  CruxOptions -> LLVMOptions -> IO FilePath
genBitCode cruxOpts llvmOpts =
  -- n.b. use of head here is OK because inputFiles should not be
  -- empty (and was previously verified as such in CruxLLVMMain).
  if noCompile llvmOpts
  then return (head (Crux.inputFiles cruxOpts))
  else do
    let ofn = "crux~" <> (takeFileName $ head $ Crux.inputFiles cruxOpts) -<.> ".bc"
    genBitCodeToFile ofn (Crux.inputFiles cruxOpts) cruxOpts llvmOpts False

-- | Given the target filename and a list of input files, along with
-- the crux and llvm options, bitcode-compile each input .c file and
-- link the resulting files, along with any input .ll files into the
-- target bitcode (BC) file.  Returns the filepath of the target
-- bitcode file.
genBitCodeToFile :: Crux.Logs msgs
                 => Log.SupportsCruxLLVMLogMessage msgs
                 => String -> [FilePath] -> CruxOptions -> LLVMOptions -> Bool
                 -> IO FilePath
genBitCodeToFile finalBCFileName files cruxOpts llvmOpts copySrc = do
  let srcBCNames = [ (src, CC.bldDir cruxOpts </> takeFileName src -<.> ".bc")
                   | src <- files ]
      finalBCFile = CC.bldDir cruxOpts </> finalBCFileName
      incs src = takeDirectory src :
                 (libDir llvmOpts </> "includes") :
                 incDirs llvmOpts
      commonFlags = [ "-c", "-DCRUCIBLE", "-emit-llvm" ] <>
                    case targetArch llvmOpts of
                      Nothing -> []
                      Just a -> [ "--target=" <> a ]
      params (src, srcBC)
        | ".ll" `isSuffixOf` src =
            return $ commonFlags <> ["-O0", "-o", srcBC, src]

        | otherwise =
            -- Specify commonFlags after flags embedded in the src
            -- under the /assumption/ that the latter takes
            -- precedence.
            let flgs =
                  commonFlags <> [ "-g" ] ++
                  concat [ [ "-I", dir ] | dir <- incs src ] ++
                  concat [ [ "-fsanitize="++san, "-fsanitize-trap="++san ]
                         | san <- ubSanitizers llvmOpts ] ++
                  [ "-O" ++ show (optLevel llvmOpts), "-o", srcBC, src ]
            in (<> flgs) <$> crucibleFlagsFromSrc src

  finalBCExists <- doesFileExist finalBCFile
  unless (finalBCExists && lazyCompile llvmOpts) $
      do forM_ srcBCNames $ \f@(src,bc) -> do
           when (copySrc) $ copyFile src (takeDirectory bc </> takeFileName src)
           bcExists <- doesFileExist bc
           unless (or [ ".bc" `isSuffixOf` src
                      , bcExists && lazyCompile llvmOpts
                      ]) $
             runClang llvmOpts =<< params f
         ver <- llvmLinkVersion llvmOpts
         let libcxxBitcode | anyCPPFiles files = [libDir llvmOpts </> "libcxx-" ++ ver ++ ".bc"]
                           | otherwise = []
         llvmLink llvmOpts (map snd srcBCNames ++ libcxxBitcode) finalBCFile
         mapM_ (\(src,bc) -> unless (src == bc) (removeFile bc)) srcBCNames
  return finalBCFile


-- | A C source file being compiled and evaluated by crux can contain
-- zero or more lines matching the following:
--
-- >   /* CRUCIBLE clang_flags: {FLAGS} */
-- >   // CRUCIBLE clang_flags: {FLAGS}
-- >   /* CRUX clang_flags: {FLAGS} */
-- >   // CRUX clang_flags: {FLAGS}
--
-- Note that the "clang_flags" portion is case-insensitive, although
-- the "CRUCIBLE" or "CRUX" prefix is case sensitive and must be
-- capitalized.
--
-- All {FLAGS} will be collected as a set of space-separated words.
-- Flags from multiple lines will be concatenated together (without
-- any attempt to eliminate duplicates or conflicts) and the result
-- will be passed as additional flags to the `clang` compilation of
-- the source by Crux.
--
-- The above line matching is whitespace-sensitive and case-sensitive.
-- When C-style comment syntax is used, the comment must be closed on
-- the same line as it was opened (although there is no line length
-- restriction).

crucibleFlagsFromSrc :: FilePath -> IO [String]
crucibleFlagsFromSrc srcFile = do
  let marker1 = [ "CRUCIBLE ", "CRUX "]
      marker2 = [ "clang_flags: " ]
      flagLines fileLines =
        do let eachFrom = foldr ((<|>) . pure) empty
           l <- eachFrom fileLines
           (pfx, sfx) <- eachFrom [ ("/* ", " */"), ("// ", "") ]
           guard $ pfx `T.isPrefixOf` l
           let l1 = T.drop (T.length pfx) l
           guard $ sfx `T.isSuffixOf` l1
           let l2 = T.take (T.length l1 - T.length sfx) l1
           m1 <- eachFrom marker1
           guard $ m1 `T.isPrefixOf` l2
           let l3 = T.drop (T.length m1) l2
           m2 <- eachFrom marker2
           let (l3pfx, l4) = T.splitAt (T.length m2) l3
           guard $ T.toLower l3pfx == m2
           pure l4
    in fmap T.unpack .
       concatMap T.words .
       observeAll . flagLines .
       T.lines <$>
       TIO.readFile srcFile


makeCounterExamplesLLVM ::
  Crux.Logs msgs =>
  Log.SupportsCruxLLVMLogMessage msgs =>
  CruxOptions -> LLVMOptions -> CruxSimulationResult -> IO ()
makeCounterExamplesLLVM cruxOpts llvmOpts res
  | makeCexes cruxOpts = mapM_ (go . snd) . Fold.toList $ (cruxSimResultGoals res)
  | otherwise = return ()

 where
 go gs =
  case gs of
    Branch g1 g2  -> go g1 >> go g2
    -- skip proved goals
    ProvedGoal{} -> return ()
    -- skip unknown goals
    NotProvedGoal _ _ _ _ Nothing -> return ()
    -- skip resource exhausted goals
    NotProvedGoal _ (simErrorReason -> ResourceExhausted{}) _ _ _ -> return ()
    -- counterexample to non-resource-exhaustion goal
    NotProvedGoal _ c _ _ (Just (m,_evs)) ->
      do let suff = case plSourceLoc (simErrorLoc c) of
                      SourcePos _ l _ -> show l
                      _               -> "unknown"
         try (buildModelExes cruxOpts llvmOpts suff (ppModelC m)) >>= \case
           Left (ex :: SomeException) -> do
             logGoal gs
             Log.sayCruxLLVM Log.FailedToBuildCounterexampleExecutable
             logException ex
           Right (_prt,dbg) -> do
             Log.sayCruxLLVM (Log.Executable (T.pack dbg))
             Log.sayCruxLLVM (Log.Breakpoint (T.pack suff))

buildModelExes ::
  Crux.Logs msgs =>
  Log.SupportsCruxLLVMLogMessage msgs =>
  CruxOptions -> LLVMOptions -> String -> String -> IO (FilePath,FilePath)
buildModelExes cruxOpts llvmOpts suff counter_src =
  do let dir  = Crux.outDir cruxOpts
     createDirectoryIfMissing True dir

     let counterFile = dir </> ("counter-example-" ++ suff ++ ".c")
     let printExe    = dir </> ("print-model-" ++ suff)
     let debugExe    = dir </> ("debug-" ++ suff)
     writeFile counterFile counter_src

     let libs = libDir llvmOpts
         incs = (libs </> "includes") :
                (map takeDirectory files ++ incDirs llvmOpts)
         files = (Crux.inputFiles cruxOpts)
         libcxx | anyCPPFiles files = ["-lstdc++"]
                | otherwise = []

     runClang llvmOpts
                   [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "print-model.c"
                   , "-o", printExe
                   ]

     runClang llvmOpts $
              concat [ [ "-I", idir ] | idir <- incs ] ++
                     [ counterFile
                     , libs </> "concrete-backend.c"
                     , "-O0", "-g"
                     , "-o", debugExe
                     ] ++ files ++ libcxx

     return (printExe, debugExe)


ppValsC :: BaseTypeRepr ty -> Vals ty -> [String]
ppValsC ty (Vals xs) =
  let (cty, cnm, ppRawVal) = case ty of
        BaseBVRepr n ->
          ("int" ++ show n ++ "_t", "int" ++ show n ++ "_t", showBVLiteral n)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | Just Refl <- testEquality eb (knownNat @8)
          , Just Refl <- testEquality sb (knownNat @24)
          -> ("float", "float", showFloatLiteral)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | Just Refl <- testEquality eb (knownNat @11)
          , Just Refl <- testEquality sb (knownNat @53)
          -> ("double", "double", showDoubleLiteral)
        BaseRealRepr -> ("double", "real", (show . toDouble))

        _ -> error ("Type not implemented: " ++ show ty)
  in  [ "size_t const crucible_values_number_" ++ cnm ++
                " = " ++ show (length xs) ++ ";"

      , "const char* crucible_names_" ++ cnm ++ "[] = { " ++
            intercalate "," (map (show . entryName) xs) ++ " };"

      , cty ++ " const crucible_values_" ++ cnm ++ "[] = { " ++
            intercalate "," (map (ppRawVal . entryValue) xs) ++ " };"
      ]

ppModelC :: ModelView -> String
ppModelC m = unlines
             $ "#include <stdint.h>"
             : "#include <stddef.h>"
             : "#include <math.h>"
             : ""
             : concatMap ppModelForType llvmModelTypes
 where
  ppModelForType (Some tpr) =
    case MapF.lookup tpr (modelVals m) of
      -- NB, produce the declarations even if there are no variables
      Nothing   -> ppValsC tpr (Vals [])
      Just vals -> ppValsC tpr vals


llvmModelTypes :: [Some BaseTypeRepr]
llvmModelTypes =
  [ Some (BaseBVRepr (knownNat @8))
  , Some (BaseBVRepr (knownNat @16))
  , Some (BaseBVRepr (knownNat @32))
  , Some (BaseBVRepr (knownNat @64))
  , Some (BaseFloatRepr (FloatingPointPrecisionRepr (knownNat @8) (knownNat @24)))
  , Some (BaseFloatRepr (FloatingPointPrecisionRepr (knownNat @11) (knownNat @53)))
  ]
