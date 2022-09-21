{- | This is the SVCOMP utility for crux-llvm.  It is designed to run
   the inputs for the "Competition on Software Verification" (SV-COMP).
   Specifically, it takes as inputs:

   * A file containing a specification to check, and

   * An architecture (either @32bit@ or @64bit@) to assume, and

   * A input C file.

   It will then attempt to verify the file against that specification,
   eventually printing @VERIFIED@, @FALSIFIED@, or @UNKNOWN@ depending on the
   results. If the result is @VERIFIED@ or @FALSFIED@, it will also produce a
   witness automaton which represents a proof that the program does or does not
   meet the specification.
-}

{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}

module Main (main) where

import Control.Applicative ( Alternative(..) )
import Control.Exception ( SomeException, try )
import Control.Monad.Extra ( whenJust )
import qualified Crypto.Hash.SHA256 as SHA256 ( hash )
import Data.Aeson ( ToJSON )
import qualified Data.Attoparsec.Text as Atto
import qualified Data.ByteString.Base16 as B16 ( encode )
import qualified Data.ByteString.Char8 as B ( readFile, unpack )
import Data.Foldable ( traverse_, toList )
import Data.Function ( on )
import Data.Functor.Identity ( Identity(..) )
import Data.Functor.WithIndex ( FunctorWithIndex(..) )
import qualified Data.List.Extra as L
import Data.Maybe ( mapMaybe )
import Data.Sequence ( Seq )
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Time.LocalTime ( getZonedTime )
import Data.Version ( showVersion )
import GHC.Generics ( Generic )
import System.Exit ( exitFailure, exitSuccess )
import System.FilePath ( (</>) )

-- crucible
import Lang.Crucible.Backend ( CrucibleEvent(..) )

-- crux
import qualified Crux
import Crux.Config.Common ( CruxOptions(..), outputOptions )
import qualified Crux.Log as Log
import Crux.Report
import Crux.SVCOMP hiding (SVCompLanguage(..))
import Crux.SVCOMP.Witness
import Crux.Types as Crux

-- what4
import What4.Expr.GroundEval ( GroundValueWrapper )
import What4.ProgramLoc ( Position(..), ProgramLoc, plFunction, plSourceLoc )

-- local
import Crux.LLVM.Compile
import Crux.LLVM.Config
import qualified Crux.LLVM.Log as Log
import Crux.LLVM.Simulate
import CruxLLVMMain ( processLLVMOptions )
import Paths_crux_llvm (version)
import qualified SVComp.Log as Log

data SVCompLogging
  = LoggingCrux Log.CruxLogMessage
  | LoggingCruxLLVM Log.CruxLLVMLogMessage
  | LoggingSVComp Log.SVCompLogMessage
  deriving (Generic, ToJSON)

svCompLoggingToSayWhat :: SVCompLogging -> SayWhat
svCompLoggingToSayWhat (LoggingCrux msg) = Log.cruxLogMessageToSayWhat msg
svCompLoggingToSayWhat (LoggingCruxLLVM msg) = Log.cruxLLVMLogMessageToSayWhat msg
svCompLoggingToSayWhat (LoggingSVComp msg) = Log.svCompLogMessageToSayWhat msg

withSVCompLogging ::
  ( ( Log.SupportsCruxLogMessage SVCompLogging
    , Log.SupportsCruxLLVMLogMessage SVCompLogging
    , Log.SupportsSVCompLogMessage SVCompLogging
    ) => computation ) ->
  computation
withSVCompLogging computation = do
  let ?injectCruxLogMessage = LoggingCrux
      ?injectCruxLLVMLogMessage = LoggingCruxLLVM
      ?injectSVCompLogMessage = LoggingSVComp
    in computation

main :: IO ()
main = withSVCompLogging $ do
  cfg <- llvmCruxConfig
  let opts = Crux.cfgJoin cfg svcompOptions
  mkOutCfg <- Crux.defaultOutputConfig svCompLoggingToSayWhat
  Crux.loadOptions mkOutCfg "crux-llvm-svcomp" version opts
    $ \(co0,(lo0,svOpts)) ->
    do (cruxOpts, llvmOpts) <- processLLVMOptions (co0{ outDir = "results" </> "SVCOMP" },lo0)
       svOpts' <- processSVCOMPOptions svOpts
       let tgt = case runIdentity $ svcompArch svOpts' of
                   Arch32 -> "i386-unknown-linux-elf"
                   Arch64 -> "x86_64-unknown-linux-elf"
           llvmOpts' = llvmOpts { targetArch = Just tgt }
       processInputFiles cruxOpts llvmOpts' svOpts'

processInputFiles :: Log.Logs msgs
                  => Log.SupportsCruxLLVMLogMessage msgs
                  => Log.SupportsSVCompLogMessage msgs
                  => CruxOptions -> LLVMOptions -> SVCOMPOptions Identity
                  -> IO ()
processInputFiles cruxOpts llvmOpts svOpts =
  traverse_ process $ Crux.inputFiles cruxOpts
  where
    process :: FilePath -> IO ()
    process inputFile = do
      mbBcFile <- genBitCodeMaybe inputFile
      whenJust mbBcFile $ \bcFile ->
        evaluateBitCode inputFile bcFile

    genBitCodeMaybe :: FilePath -> IO (Maybe FilePath)
    genBitCodeMaybe inputFile
      | or [ L.isSuffixOf bl inputFile | bl <- svcompBlacklist svOpts ]
      = do Log.saySVComp (Log.Skipping Log.DueToBlacklist (T.pack inputFile))
           return Nothing
      | otherwise
      = Just <$> genBitCode cruxOpts llvmOpts

    evaluateBitCode :: FilePath -> FilePath -> IO ()
    evaluateBitCode inputFile bcFile = withSVCompLogging $ do
      mkOutCfg <- Crux.defaultOutputConfig svCompLoggingToSayWhat
      let ?outputConfig = mkOutCfg (Just (outputOptions cruxOpts))
      mres <- try $
               do res <- Crux.runSimulator cruxOpts (simulateLLVMFile bcFile llvmOpts)
                  generateReport cruxOpts res
                  return res

      case mres of
        Left e ->
          do Log.saySVComp Log.SimulatorThrewException
             Log.logException (e :: SomeException)
             exitFailure

        Right res@(CruxSimulationResult cmpl gls) ->
          do let numTotalGoals = sum (Crux.totalProcessedGoals . fst <$> gls)
             let numDisprovedGoals = sum (Crux.disprovedGoals . fst <$> gls)
             let numProvedGoals = sum (Crux.provedGoals . fst <$> gls)

             let verdict
                   | numDisprovedGoals > 0 = Falsified
                   | ProgramComplete <- cmpl
                   , numProvedGoals == numTotalGoals = Verified
                   | otherwise = Unknown

             specFileContents <- B.readFile $ runIdentity $ svcompSpec svOpts
             let specFileText = T.decodeUtf8 specFileContents
             prop <- case Atto.parseOnly propParse specFileText of
                       Left msg ->
                         do Log.saySVComp $ Log.PropertyParseError specFileText (T.pack msg)
                            exitFailure
                       Right p -> return p

             witType <- case verdict of
                          Verified  -> do Crux.logSimResult True res
                                          Log.saySVComp $ Log.Verdict Verified prop
                                          pure CorrectnessWitness
                          Falsified -> do Crux.logSimResult True res
                                          Log.saySVComp $ Log.Verdict Falsified prop
                                          pure ViolationWitness
                          Unknown   -> do Log.saySVComp $ Log.Verdict Unknown prop
                                          exitSuccess

             inputFileContents <- B.readFile inputFile
             creationTime <- getZonedTime
             let mkWitness nodes edges = Witness
                   { witnessType           = witType
                   , witnessSourceCodeLang = C
                   , witnessProducer       = "crux-llvm-" ++ showVersion version
                   , witnessSpecification  = L.trim $ B.unpack specFileContents
                   , witnessProgramFile    = inputFile
                   , witnessProgramHash    = B16.encode $ SHA256.hash inputFileContents
                   , witnessArchitecture   = runIdentity $ svcompArch svOpts
                   , witnessCreationTime   = creationTime
                   , witnessNodes          = nodes
                   , witnessEdges          = edges
                   }
                 trivialCorrectnessWitness = mkWitness [(mkNode 0) { nodeEntry = Just True }] []

             writeFile (svcompWitnessOutput svOpts) $ ppWitness $ case witType of
               CorrectnessWitness -> trivialCorrectnessWitness
               ViolationWitness   -> let (nodes, edges) = mkViolationWitness $ fmap snd gls
                                     in mkWitness nodes edges

mkViolationWitness :: Seq ProvedGoals -> ([WitnessNode], [WitnessEdge])
mkViolationWitness gs =
  case L.firstJust findNotProvedGoal $ toList gs of
    Nothing -> error "Could not find event log for counterexample"
    Just (_mv, events) ->
      let locs  = -- It is possible for certain LLVM instructions which do not
                  -- directly map back to source locations to be given a line
                  -- number of 0. (See #862 for an example.) Line number 0
                  -- wreaks havoc on witness validators, so we filter out such
                  -- locations to avoid this.
                  filter ((/= Just 0) . programLocSourcePosLine) $
                  -- Witness validators aren't hugely fond of using the same
                  -- line number multiple times successively, so remove
                  -- consecutive duplicates.
                  removeRepeatsBy ((==) `on` programLocSourcePosLine) $
                  mapMaybe locationReachedEventLoc events
          edges = imap violationEdge locs
          nodes = violationNodes $ length edges
      in (nodes, edges)
  where
    findNotProvedGoal :: ProvedGoals -> Maybe (ModelView, [CrucibleEvent GroundValueWrapper])
    findNotProvedGoal (Branch pg1 pg2)          = findNotProvedGoal pg1 <|> findNotProvedGoal pg2
    findNotProvedGoal (NotProvedGoal _ _ _ _ x _) = x
    findNotProvedGoal ProvedGoal{}              = Nothing

    violationNodes :: Int -> [WitnessNode]
    violationNodes numEdges =
      map (\idx -> (mkNode idx)
                     { nodeEntry     = if idx == 0        then Just True else Nothing
                     , nodeViolation = if idx == numEdges then Just True else Nothing
                     })
          [0..numEdges]

    locationReachedEventLoc :: CrucibleEvent GroundValueWrapper -> Maybe ProgramLoc
    locationReachedEventLoc (LocationReachedEvent loc) = Just loc
    locationReachedEventLoc CreateVariableEvent{}      = Nothing

    violationEdge :: Int -> ProgramLoc -> WitnessEdge
    violationEdge idx loc =
      let mbSourcePos = programLocSourcePos loc in
      (mkEdge idx (idx+1))
        { edgeStartLine       = fst <$> mbSourcePos
        , edgeAssumptionScope = Just $ show $ plFunction loc
          -- crux-llvm–specific extensions
        , edgeStartColumn     = snd <$> mbSourcePos
        }

    programLocSourcePos :: ProgramLoc -> Maybe (Int, Int)
    programLocSourcePos pl =
      case plSourceLoc pl of
        SourcePos _ l c -> Just (l, c)
        BinaryPos{}     -> Nothing
        OtherPos{}      -> Nothing
        InternalPos     -> Nothing

    programLocSourcePosLine :: ProgramLoc -> Maybe Int
    programLocSourcePosLine = fmap fst . programLocSourcePos
