{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Crux.LLVM.Config where

import           Config.Schema
import           Control.Applicative ( Alternative(..) )
import           Control.Exception ( Exception, displayException, throwIO )
import           Control.Monad ( guard )
import           Control.Monad.State ( liftIO, MonadIO )
import qualified Data.Text as Text
import           System.Directory ( doesDirectoryExist )
import           System.Environment ( getExecutablePath )
import           System.FilePath ( (</>), joinPath, normalise, splitPath, takeDirectory )

import qualified Data.LLVM.BitCode as LLVM

import           Lang.Crucible.LLVM.Intrinsics ( IntrinsicsOptions(..), AbnormalExitBehavior(..) )
import           Lang.Crucible.LLVM.MemModel ( MemOptions(..), laxPointerMemOptions )
import           Lang.Crucible.LLVM.Translation ( TranslationOptions(..) )

import qualified Crux
import           Paths_crux_llvm ( getDataDir )


--
-- LLVM specific errors
--
data CError =
    ClangError Int String String
  | LLVMParseError LLVM.Error
  | MissingFun String
  | BadFun
  | EnvError String
  | NoFiles
    deriving Show

instance Exception CError where
  displayException = ppCError

ppCError :: CError -> String
ppCError err = case err of
    NoFiles                -> "crux-llvm requires at least one input file."
    EnvError msg           -> msg
    BadFun                 -> "Function should have no arguments"
    MissingFun x           -> "Cannot find code for " ++ show x
    LLVMParseError e       -> LLVM.formatError e
    ClangError n sout serr ->
      unlines $ [ "`clang` compilation failed."
                , "*** Exit code: " ++ show n
                , "*** Standard out:"
                ] ++
                [ "   " ++ l | l <- lines sout ] ++
                [ "*** Standard error:" ] ++
                [ "   " ++ l | l <- lines serr ]


throwCError :: MonadIO m => CError -> m b
throwCError e = liftIO (throwIO e)


abnormalExitBehaviorSpec :: ValueSpec AbnormalExitBehavior
abnormalExitBehaviorSpec =
  (AlwaysFail <$ atomSpec "always-fail") <!>
  (OnlyAssertFail <$ atomSpec "only-assert-fail") <!>
  (NeverFail <$ atomSpec "never-fail")

data LLVMOptions = LLVMOptions
  { clangBin   :: FilePath
  , linkBin    :: FilePath
  , clangOpts  :: [String]
  , libDir     :: FilePath
  , incDirs    :: [FilePath]
  , targetArch :: Maybe String
  , ubSanitizers :: [String]
  , intrinsicsOpts :: IntrinsicsOptions
  , memOpts        :: MemOptions
  , transOpts      :: TranslationOptions
  , entryPoint :: String
  , lazyCompile :: Bool
  , noCompile :: Bool
  , optLevel :: Int
  , symFSRoot :: Maybe FilePath
  }

-- | The @c-src@ directory, which contains @crux-llvm@–specific files such as
-- @crucible.h@, can live in different locations depending on how @crux-llvm@
-- was built. This function looks in a couple of common places:
--
-- 1. A directory relative to the @crux-llvm@ binary itself. This is the case
--    when running a @crux-llvm@ binary distribution. If that can't be found,
--    default to...
--
-- 2. The @data-files@ directory, as reported by @cabal@'s 'getDataDir'
--    function.
--
-- This isn't always guaranteed to work in every situation, but it should cover
-- enough common cases to be useful in practice.
findDefaultLibDir :: IO FilePath
findDefaultLibDir = getDirRelativeToBin <|> getCabalDataDir
  where
    getDirRelativeToBin :: IO FilePath
    getDirRelativeToBin = do
      binDir <- takeDirectory `fmap` getExecutablePath
      let libDirPrefix = normalise . joinPath . init . splitPath $ binDir
          libDir       = libDirPrefix </> cSrc
      libDirExists <- doesDirectoryExist libDir
      guard libDirExists
      pure libDir

    getCabalDataDir :: IO FilePath
    getCabalDataDir = do
      libDirPrefix <- getDataDir
      pure $ libDirPrefix </> cSrc

    cSrc :: FilePath
    cSrc = "c-src"

llvmCruxConfig :: IO (Crux.Config LLVMOptions)
llvmCruxConfig = do
  libDirDefault <- findDefaultLibDir
  return Crux.Config
   { Crux.cfgFile =
      do clangBin <- Crux.section "clang" Crux.fileSpec "clang"
                     "Binary to use for `clang`."

         linkBin  <- Crux.section "llvm-link" Crux.fileSpec "llvm-link"
                     "Binary to use for `llvm-link`."

         clangOpts <- Crux.section "clang-opts"
                                    (Crux.oneOrList Crux.stringSpec) []
                      "Additional options for `clang`."

         libDir <- Crux.section "lib-dir" Crux.dirSpec libDirDefault
                   "Locations of `crux-llvm` support library."

         incDirs <- Crux.section "include-dirs"
                        (Crux.oneOrList Crux.dirSpec) []
                    "Additional include directories."

         targetArch <- Crux.sectionMaybe "target-architecture" Crux.stringSpec
                       "Target architecture to pass to LLVM build operations.\
                       \ Default is no specification for current system architecture"

         intrinsicsOpts <- do abnormalExitBehavior <-
                                Crux.section "abnormal-exit-behavior" abnormalExitBehaviorSpec AlwaysFail
                                  (Text.unwords
                                    [ "Should Crux fail when simulating a function which triggers an"
                                    , "abnormal exit, such as abort()? Possible options are:"
                                    , "'always-fail' (default); 'only-assert-fail', which only fails"
                                    , "when simulating __assert_fail(); and 'never-fail'."
                                    , "The latter two options are primarily useful for SV-COMP."
                                    ])
                              return IntrinsicsOptions{..}

         memOpts <- do laxPointerOrdering <-
                         Crux.section "lax-pointer-ordering" Crux.yesOrNoSpec False
                           "Allow order comparisons between pointers from different allocation blocks"
                       laxConstantEquality <-
                         Crux.section "lax-constant-equality" Crux.yesOrNoSpec False
                           "Allow equality comparisons between pointers to constant data"
                       laxLoadsAndStores <-
                         Crux.section "lax-loads-and-stores" Crux.yesOrNoSpec False
                           "Relax some of Crucible's validity checks for memory loads and stores"
                       return MemOptions{..}

         transOpts <- do laxArith <-
                           Crux.section "lax-arithmetic" Crux.yesOrNoSpec False
                             "Do not produce proof obligations related to arithmetic overflow, etc."
                         optLoopMerge <-
                           Crux.section "opt-loop-merge" Crux.yesOrNoSpec False
                             "Insert merge blocks in loops with early exits (i.e. breaks or returns). This may improve simulation performance."
                         debugIntrinsics <- Crux.section "debug-intrinsics" Crux.yesOrNoSpec False
                              "Translate statements using certain llvm.dbg intrinsic functions."
                         return TranslationOptions{..}

         entryPoint <- Crux.section "entry-point" Crux.stringSpec "main"
                           "Name of the entry point function to begin simulation."

         lazyCompile <- Crux.section "lazy-compile" Crux.yesOrNoSpec False
                           "Avoid compiling bitcode from source if intermediate files already exist"

         noCompile <- Crux.section "no-compile" Crux.yesOrNoSpec False
                        "Treat the input file as an LLVM module, do not compile it"

         ubSanitizers <- Crux.section "ub-sanitizers" (Crux.listSpec Crux.stringSpec) []
                           "Undefined Behavior sanitizers to enable in `clang`"

         optLevel <- Crux.section "opt-level" Crux.numSpec 1
                           "Optimization level to request from `clang`"

         symFSRoot <- Crux.sectionMaybe "symbolic-fs-root" Crux.stringSpec
                      "The root of a symbolic filesystem to make available to\
                      \ the program during symbolic execution"

         return LLVMOptions { .. }

   , Crux.cfgEnv  =
      [ Crux.EnvVar "CLANG"      "Binary to use for `clang`."
        $ \v opts -> Right opts { clangBin = v }

      , Crux.EnvVar "CLANG_OPTS" "Options to pass to `clang`."
        $ \v opts -> Right opts { clangOpts = words v }

      , Crux.EnvVar "LLVM_LINK" "Use this binary to link LLVM bitcode (`llvm-link`)."
        $ \v opts -> Right opts { linkBin = v }

      ]

   , Crux.cfgCmdLineFlag =
      [ Crux.Option ['I'] ["include-dirs"]
        "Additional include directories."
        $ Crux.ReqArg "DIR"
        $ \d opts -> Right opts { incDirs = d : incDirs opts }

      , Crux.Option [] ["target"]
        "Target architecture to pass to LLVM build operations"
        $ Crux.OptArg "ARCH"
        $ \a opts -> Right opts { targetArch = a }

      , Crux.Option [] ["lax-pointers"]
        "Turn on lax rules for pointer comparisons"
        $ Crux.NoArg
        $ \opts -> Right opts{ memOpts = laxPointerMemOptions }

      , Crux.Option [] ["lax-arithmetic"]
        "Turn on lax rules for arithemetic overflow"
        $ Crux.NoArg
        $ \opts -> Right opts { transOpts = (transOpts opts) { laxArith = True } }

      , Crux.Option [] ["opt-loop-merge"]
        "Insert merge blocks in loops with early exits"
        $ Crux.NoArg
        $ \opts -> Right opts { transOpts = (transOpts opts) { optLoopMerge = True } }

      , Crux.Option [] ["lazy-compile"]
        "Avoid compiling bitcode from source if intermediate files already exist (default: off)"
        $ Crux.NoArg
        $ \opts -> Right opts{ lazyCompile = True }

      , Crux.Option [] ["no-compile"]
        "Treat the input file as an LLVM module, do not compile it"
        $ Crux.NoArg
        $ \opts -> Right opts{ noCompile = True }

      , Crux.Option [] ["entry-point"]
        "Name of the entry point to begin simulation"
        $ Crux.ReqArg "SYMBOL"
        $ \s opts -> Right opts{ entryPoint = s }

      , Crux.Option "O" []
        "Optimization level for `clang`"
        $ Crux.ReqArg "NUM"
        $ Crux.parsePosNum "NUM"
        $ \v opts -> opts { optLevel = v }

      , Crux.Option [] ["symbolic-fs-root"]
        "The root of a symbolic filesystem to make available to the program during symbolic execution"
        $ Crux.OptArg "DIR"
        $ \a opts -> Right opts { symFSRoot = a }
      ]
   }
