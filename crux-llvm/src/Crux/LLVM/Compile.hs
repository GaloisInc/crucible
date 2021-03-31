{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Crux.LLVM.Compile where

import           Control.Exception ( SomeException(..), try, displayException )
import           Control.Monad ( unless, when, forM_ )
import qualified Data.Foldable as Fold
import           Data.List ( intercalate, isSuffixOf )
import qualified Data.Parameterized.Map as MapF
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

runClang :: Logs => CruxOptions -> LLVMOptions -> [String] -> IO ()
runClang cruxOpts llvmOpts params =
  do let clang = clangBin llvmOpts
         allParams = clangOpts llvmOpts ++ params
     when (simVerbose cruxOpts > 1) $ say "CLANG" $ unwords (clang : map show allParams)
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
genBitCode :: Logs => CruxOptions -> LLVMOptions -> IO FilePath
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
genBitCodeToFile :: Logs
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
            commonFlags <> ["-O0", "-o", srcBC, src]

        | otherwise =
            commonFlags <> [ "-g" ] ++
            concat [ [ "-I", dir ] | dir <- incs src ] ++
            concat [ [ "-fsanitize="++san, "-fsanitize-trap="++san ]
                   | san <- ubSanitizers llvmOpts ] ++
            [ "-O" ++ show (optLevel llvmOpts), "-o", srcBC, src ]

  finalBCExists <- doesFileExist finalBCFile
  unless (finalBCExists && lazyCompile llvmOpts) $
      do forM_ srcBCNames $ \f@(src,bc) -> do
           when (copySrc) $ copyFile src (takeDirectory bc </> takeFileName src)
           bcExists <- doesFileExist bc
           unless (or [ ".bc" `isSuffixOf` src
                      , bcExists && lazyCompile llvmOpts
                      ]) $
             runClang cruxOpts llvmOpts (params f)
         ver <- llvmLinkVersion llvmOpts
         let libcxxBitcode | anyCPPFiles files = [libDir llvmOpts </> "libcxx-" ++ ver ++ ".bc"]
                           | otherwise = []
         llvmLink llvmOpts (map snd srcBCNames ++ libcxxBitcode) finalBCFile
         mapM_ (\(src,bc) -> unless (src == bc) (removeFile bc)) srcBCNames
  return finalBCFile


makeCounterExamplesLLVM ::
  Logs => CruxOptions -> LLVMOptions -> CruxSimulationResult -> IO ()
makeCounterExamplesLLVM cruxOpts llvmOpts res
  | makeCexes cruxOpts = mapM_ (go . snd) . Fold.toList $ (cruxSimResultGoals res)
  | otherwise = return ()

 where
 go gs =
  case gs of
    AtLoc _ _ gs1 -> go gs1
    Branch g1 g2  -> go g1 >> go g2
    Goal _ (c,_) _ r ->
      let suff = case plSourceLoc (simErrorLoc c) of
                   SourcePos _ l _ -> show l
                   _               -> "unknown"
          msg = show c
          skipGoal = case simErrorReason c of
                       ResourceExhausted _ -> True
                       _ -> False

      in case (r, skipGoal) of
           (NotProved _ (Just m), False) ->
             do sayFail "Crux" ("Counter example for " ++ msg)
                try (buildModelExes cruxOpts llvmOpts suff (ppModelC m)) >>= \case
                  Left (ex :: SomeException) ->
                    sayFail "Crux" (unlines ["Failed to build counterexample executable", displayException ex])
                  Right (_prt,dbg) -> do
                    say "Crux" ("*** debug executable: " ++ dbg)
                    say "Crux" ("*** break on line: " ++ suff)
           _ -> return ()

buildModelExes :: Logs => CruxOptions -> LLVMOptions -> String -> String -> IO (FilePath,FilePath)
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

     runClang cruxOpts llvmOpts
                   [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "print-model.c"
                   , "-o", printExe
                   ]

     runClang cruxOpts llvmOpts $
              concat [ [ "-I", idir ] | idir <- incs ] ++
                     [ counterFile
                     , libs </> "concrete-backend.c"
                     , "-O0", "-g"
                     , "-o", debugExe
                     ] ++ files ++ libcxx

     return (printExe, debugExe)


ppValsC :: BaseTypeRepr ty -> Vals ty -> String
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
  in unlines
      [ "size_t const crucible_values_number_" ++ cnm ++
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
             : MapF.foldrWithKey (\k v rest -> ppValsC k v : rest) [] vals
            where vals = modelVals m
