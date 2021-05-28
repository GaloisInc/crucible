{- | TODO RGS: Docs
-}

{-# Language ApplicativeDo #-}
{-# Language ImplicitParams #-}
{-# Language KindSignatures #-}
{-# Language NamedFieldPuns #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language RecordWildCards #-}
{-# Language ScopedTypeVariables #-}

module Main (main) where

import Config.Schema
import Control.Applicative ( Alternative(..) )
import Control.Exception ( SomeException, try )
import Control.Monad.Extra ( whenJust )
import qualified Crypto.Hash.SHA256 as SHA256 ( hash )
import qualified Data.Attoparsec.Text as Atto
import qualified Data.ByteString.Base16 as B16 ( encode )
import qualified Data.ByteString.Char8 as B ( readFile, unpack )
import Data.ByteString ( ByteString )
import Data.Foldable ( traverse_, toList )
import Data.Function ( on )
import Data.Functor.Identity ( Identity(..) )
import Data.Functor.WithIndex ( FunctorWithIndex(..) )
import Data.Kind (Type)
import qualified Data.List.Extra as L
import Data.Maybe ( catMaybes, mapMaybe )
import Data.Sequence ( Seq )
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Time.Format.ISO8601 ( iso8601Show )
import Data.Time.LocalTime ( ZonedTime, getZonedTime )
import Data.Version ( showVersion )
import System.Exit ( exitFailure, exitSuccess )
import System.FilePath ( (</>), takeBaseName )
import Text.XML.Light

-- crucible
import Lang.Crucible.Backend ( CrucibleEvent(..) )

-- crux
import qualified Crux
import Crux.Config.Common ( CruxOptions(..) )
import qualified Crux.Log as Log
import Crux.Report
import Crux.SVCOMP hiding (SVCompLanguage(..))
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
import qualified SVComp.Witness.Log as Log

data SVCompWitnessLogging
  = LoggingCrux Log.CruxLogMessage
  | LoggingCruxLLVM Log.CruxLLVMLogMessage
  | LoggingSVCompWitness Log.SVCompWitnessLogMessage

svCompWitnessLoggingToSayWhat :: SVCompWitnessLogging -> SayWhat
svCompWitnessLoggingToSayWhat (LoggingCrux msg) = Log.cruxLogMessageToSayWhat msg
svCompWitnessLoggingToSayWhat (LoggingCruxLLVM msg) = Log.cruxLLVMLogMessageToSayWhat msg
svCompWitnessLoggingToSayWhat (LoggingSVCompWitness msg) = Log.svCompWitnessLogMessageToSayWhat msg

withSVCompWitnessLogging ::
  ( ( Log.SupportsCruxLogMessage SVCompWitnessLogging
    , Log.SupportsCruxLLVMLogMessage SVCompWitnessLogging
    , Log.SupportsSVCompWitnessLogMessage SVCompWitnessLogging
    ) => computation ) ->
  computation
withSVCompWitnessLogging computation = do
  let ?injectCruxLogMessage = LoggingCrux
      ?injectCruxLLVMLogMessage = LoggingCruxLLVM
      ?injectSVCompWitnessLogMessage = LoggingSVCompWitness
    in computation

main :: IO ()
main = withSVCompWitnessLogging $ do
  cfg <- llvmCruxConfig
  let opts = cfg `Crux.cfgJoin` (svcompOptions `Crux.cfgJoin` svcompWitnessOptions)
  Crux.loadOptions (Crux.defaultOutputConfig svCompWitnessLoggingToSayWhat)
                   "crux-llvm-svcomp" version opts $ \(co0,(lo0,(svOpts,svWitnessOpts))) ->
    do (cruxOpts, llvmOpts) <- processLLVMOptions (co0{ outDir = "results" </> "SVCOMP" },lo0)
       svWitnessOpts' <- processSVCOMPWitnessOptions svWitnessOpts
       processInputFiles cruxOpts llvmOpts svOpts svWitnessOpts'

data SVCOMPWitnessOptions (f :: Type -> Type) = SVCOMPWitnessOptions
  { svcompArch       :: f Arch
  , svcompSpec       :: f FilePath
  , svcompWitnessDir :: FilePath
  }

processSVCOMPWitnessOptions :: SVCOMPWitnessOptions Maybe -> IO (SVCOMPWitnessOptions Identity)
processSVCOMPWitnessOptions
    (SVCOMPWitnessOptions{svcompArch, svcompSpec, svcompWitnessDir}) = do
  svcompArch' <- process "svcomp-arch" svcompArch
  svcompSpec' <- process "svcomp-spec" svcompSpec
  pure $ SVCOMPWitnessOptions{ svcompArch = svcompArch', svcompSpec = svcompSpec'
                             , svcompWitnessDir }
  where
    process :: String -> Maybe a -> IO (Identity a)
    process optName = maybe (fail $ "A value for --" ++ optName ++ " must be provided") (pure . Identity)

svcompWitnessOptions :: Crux.Config (SVCOMPWitnessOptions Maybe)
svcompWitnessOptions = Crux.Config
  { cfgFile =
      do svcompArch <-
           Crux.sectionMaybe "svcomp-arch" archSpec
           "The architecture assumed for the verification task."

         svcompSpec <-
           Crux.sectionMaybe "svcomp-spec" Crux.fileSpec
           "The file containing the specification text used to verify the program. Likely a .prp file."

         svcompWitnessDir <-
           Crux.section "svcomp-witness-dir" Crux.fileSpec "."
           "The directory in which to output the witness automaton file."

         return SVCOMPWitnessOptions{ .. }

  , cfgEnv = []

  , cfgCmdLineFlag =
      [ Crux.Option [] ["svcomp-arch"]
        "The architecture assumed for the verification task."
        $ Crux.ReqArg "`32bit` or `64bit`"
        $ parseArch
        $ \a opts -> opts{ svcompArch = Just a }

      , Crux.Option [] ["svcomp-spec"]
        "The file containing the specification text used to verify the program. Likely a .prp file."
        $ Crux.ReqArg "FILE"
        $ \f opts -> Right opts{ svcompSpec = Just f }

      , Crux.Option [] ["svcomp-witness-dir"]
        "The directory in which to output the witness automaton file."
        $ Crux.ReqArg "DIR"
        $ \d opts -> Right opts{ svcompWitnessDir = d }
      ]
  }

archSpec :: ValueSpec Arch
archSpec =
  (Arch32 <$ atomSpec "32bit") <!>
  (Arch64 <$ atomSpec "64bit")

parseArch :: (Arch -> opts -> opts) -> String -> Crux.OptSetter opts
parseArch mk = \txt opts ->
  case txt of
    "32bit" -> Right (mk Arch32 opts)
    "64bit" -> Right (mk Arch64 opts)
    _       -> Left "Invalid architecture"

processInputFiles :: Log.Logs msgs
                  => Log.SupportsCruxLLVMLogMessage msgs
                  => Log.SupportsSVCompWitnessLogMessage msgs
                  => CruxOptions -> LLVMOptions -> SVCOMPOptions -> SVCOMPWitnessOptions Identity
                  -> IO ()
processInputFiles cruxOpts llvmOpts svOpts svWitnessOpts =
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
      = do Log.saySVCompWitness (Log.Skipping Log.DueToBlacklist (T.pack inputFile))
           return Nothing
      | otherwise
      = let tgt = case runIdentity $ svcompArch svWitnessOpts of
                    Arch32 -> "i386-unknown-linux-elf"
                    Arch64 -> "x86_64-unknown-linux-elf"
            llvmOpts' = llvmOpts { targetArch = Just tgt } in
        Just <$> genBitCode cruxOpts llvmOpts'

    evaluateBitCode :: FilePath -> FilePath -> IO ()
    evaluateBitCode inputFile bcFile = withSVCompWitnessLogging $ do
      let ?outputConfig = Crux.defaultOutputConfig svCompWitnessLoggingToSayWhat $ Just cruxOpts

      mres <- try $
               do res <- Crux.runSimulator cruxOpts (simulateLLVMFile bcFile llvmOpts)
                  generateReport cruxOpts res
                  return res

      case mres of
        Left e ->
          do Log.saySVCompWitness Log.SimulatorThrewException
             Log.logException (e :: SomeException)
             exitFailure

        Right (CruxSimulationResult cmpl gls) ->
          do let totalGoals = sum (Crux.totalProcessedGoals . fst <$> gls)
             let disprovedGoals = sum (Crux.disprovedGoals . fst <$> gls)
             let provedGoals = sum (Crux.provedGoals . fst <$> gls)

             let verdict
                   | disprovedGoals > 0 = Falsified
                   | ProgramComplete <- cmpl
                   , provedGoals == totalGoals = Verified
                   | otherwise = Unknown

             specFileContents <- B.readFile $ runIdentity $ svcompSpec svWitnessOpts
             let specFileText = T.decodeUtf8 specFileContents
             prop <- case Atto.parseOnly propParse specFileText of
                       Left msg ->
                         do Log.saySVCompWitness $ Log.PropertyParseError specFileText (T.pack msg)
                            exitFailure
                       Right p -> return p

             witType <- case verdict of
                          Verified  -> do Log.saySVCompWitness $ Log.Verdict Verified prop
                                          pure CorrectnessWitness
                          Falsified -> do Log.saySVCompWitness $ Log.Verdict Falsified prop
                                          pure ViolationWitness
                          Unknown   -> do Log.saySVCompWitness $ Log.Verdict Unknown prop
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
                   , witnessArchitecture   = runIdentity $ svcompArch svWitnessOpts
                   , witnessCreationTime   = creationTime
                   , witnessNodes          = nodes
                   , witnessEdges          = edges
                   }
                 trivialCorrectnessWitness = mkWitness [(mkNode 0) { nodeEntry = Just True }] []

             let witnessFileName = takeBaseName inputFile ++ "-witness.graphml"
             writeFile witnessFileName $ ppWitness $ case witType of
               CorrectnessWitness -> trivialCorrectnessWitness
               ViolationWitness   -> let (nodes, edges) = mkViolationWitness $ fmap snd gls
                                     in mkWitness nodes edges

mkViolationWitness :: Seq ProvedGoals -> ([WitnessNode], [WitnessEdge])
mkViolationWitness gs =
  case L.firstJust findNotProvedGoal $ toList gs of
    Nothing -> error "Could not find event log for counterexample"
    Just (_mv, events) ->
      let locs  = -- Witness validators aren't hugely fond of using the same
                  -- line number multiple times successively, so remove
                  -- consecutive duplicates.
                  removeRepeatsBy ((==) `on` (fmap fst . programLocSourcePos)) $
                  mapMaybe locationReachedEventLoc events
          edges = imap violationEdge locs
          nodes = violationNodes $ length edges
      in (nodes, edges)
  where
    findNotProvedGoal :: ProvedGoals -> Maybe (ModelView, [CrucibleEvent GroundValueWrapper])
    findNotProvedGoal (Branch pg1 pg2)          = findNotProvedGoal pg1 <|> findNotProvedGoal pg2
    findNotProvedGoal (NotProvedGoal _ _ _ _ x) = x
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

-- | A witness automaton. Adheres to the format specified in
-- https://github.com/sosy-lab/sv-witnesses/tree/a592b52c4034423d42bed2059addbc6d8f1fa443#data-elements.
data Witness = Witness
  { witnessType           :: WitnessType
  , witnessSourceCodeLang :: SourceCodeLang
  , witnessProducer       :: String
  , witnessSpecification  :: String
  , witnessProgramFile    :: FilePath
  , witnessProgramHash    :: ByteString
  , witnessArchitecture   :: Arch
  , witnessCreationTime   :: ZonedTime
  , witnessNodes          :: [WitnessNode]
  , witnessEdges          :: [WitnessEdge]
  }
  deriving Show

data WitnessNode = WitnessNode
  { nodeId             :: Id
  , nodeEntry          :: Maybe Bool
  , nodeSink           :: Maybe Bool
  , nodeViolation      :: Maybe Bool
  , nodeInvariant      :: Maybe String
  , nodeInvariantScope :: Maybe String
  }
  deriving Show

mkNode :: Int -> WitnessNode
mkNode i = WitnessNode
  { nodeId             = mkNodeId i
  , nodeEntry          = Nothing
  , nodeSink           = Nothing
  , nodeViolation      = Nothing
  , nodeInvariant      = Nothing
  , nodeInvariantScope = Nothing
  }

mkNodeId :: Int -> Id
mkNodeId i = "N" ++ show i

data WitnessEdge = WitnessEdge
  { edgeSource                   :: Id
  , edgeTarget                   :: Id
  , edgeAssumption               :: Maybe Assumption
  , edgeAssumptionScope          :: Maybe String
  , edgeAssumptionResultFunction :: Maybe String
  , edgeControl                  :: Maybe Control
  , edgeStartLine                :: Maybe Int
  , edgeEndLine                  :: Maybe Int
  , edgeStartOffset              :: Maybe Int
  , edgeEndOffset                :: Maybe Int
  , edgeEnterLoopHead            :: Maybe Bool
  , edgeEnterFunction            :: Maybe String
  , edgeReturnFromFunction       :: Maybe String
  , edgeThreadId                 :: Maybe String
  , edgeCreateThread             :: Maybe String

    -- crux-llvm–specific extensions
  , edgeStartColumn              :: Maybe Int
      -- Not to be confused with startoffset, which records the total number
      -- of characters from the very start of the program. This, on the other
      -- hand, simply records the number of characters from the start of the
      -- current line, which I find to be a nice debugging tool.
  }
  deriving Show

mkEdge :: Int -> Int -> WitnessEdge
mkEdge source target = WitnessEdge
  { edgeSource                   = mkNodeId source
  , edgeTarget                   = mkNodeId target
  , edgeAssumption               = Nothing
  , edgeAssumptionScope          = Nothing
  , edgeAssumptionResultFunction = Nothing
  , edgeControl                  = Nothing
  , edgeStartLine                = Nothing
  , edgeEndLine                  = Nothing
  , edgeStartOffset              = Nothing
  , edgeEndOffset                = Nothing
  , edgeEnterLoopHead            = Nothing
  , edgeEnterFunction            = Nothing
  , edgeReturnFromFunction       = Nothing
  , edgeThreadId                 = Nothing
  , edgeCreateThread             = Nothing

    -- crux-llvm–specific extensions
  , edgeStartColumn              = Nothing
  }

data WitnessType
  = CorrectnessWitness
  | ViolationWitness
  deriving Show

ppWitnessType :: WitnessType -> String
ppWitnessType witnessType =
  case witnessType of
    CorrectnessWitness -> "correctness_witness"
    ViolationWitness   -> "violation_witness"

data SourceCodeLang
  = C
  | Java
  deriving Show

ppSourceCodeLang :: SourceCodeLang -> String
ppSourceCodeLang sourceCodeLang =
  case sourceCodeLang of
    C    -> "C"
    Java -> "Java"

data Arch
  = Arch32
  | Arch64
  deriving Show

ppArch :: Arch -> String
ppArch arch =
  case arch of
    Arch32 -> "32bit"
    Arch64 -> "64bit"

newtype Assumption = Assumption [String]
  deriving Show

ppAssumption :: Assumption -> String
ppAssumption (Assumption exprs) =
  L.intercalate ";" exprs

data Control
  = ConditionTrue
  | ConditionFalse
  deriving Show

ppControl :: Control -> String
ppControl control =
  case control of
    ConditionTrue  -> "condition-true"
    ConditionFalse -> "condition-false"

data GraphMLAttrType
  = Boolean
  | Int
  | Long
  | Float
  | Double
  | String
  deriving Show

ppGraphMLAttrType :: GraphMLAttrType -> String
ppGraphMLAttrType ty =
  case ty of
    Boolean -> "boolean"
    Int     -> "int"
    Long    -> "long"
    Float   -> "float"
    Double  -> "double"
    String  -> "string"

data GraphMLAttrDomain
  = Graph
  | Node
  | Edge
  | All
  deriving Show

ppGraphMLAttrDomain :: GraphMLAttrDomain -> String
ppGraphMLAttrDomain domain =
  case domain of
    Graph -> "graph"
    Node  -> "node"
    Edge  -> "edge"
    All   -> "all"

ppBool :: Bool -> String
ppBool b =
  case b of
    False -> "false"
    True  -> "true"

ppByteString :: ByteString -> String
ppByteString = B.unpack

ppInt :: Int -> String
ppInt = show

ppString :: String -> String
ppString = id

ppZonedTime :: ZonedTime -> String
ppZonedTime = iso8601Show

type Id = String

dataNode :: String -> (a -> String) -> a -> Element
dataNode keyVal ppThing thing =
  add_attr (Attr{attrKey = unqual "key", attrVal = keyVal}) $
  unode "data" $
    ppThing thing

ppWitness :: Witness -> String
ppWitness witness =
  unlines [ "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
          , ppElement $ unode "graph" witness
          ]

instance Node Witness where
  node n Witness{ witnessType, witnessSourceCodeLang, witnessProducer
                , witnessSpecification, witnessProgramFile, witnessProgramHash
                , witnessArchitecture, witnessCreationTime
                , witnessNodes, witnessEdges
                } =
    add_attrs [ Attr{ attrKey = unqual "xmlns"
                    , attrVal = "http://graphml.graphdrawing.org/xmlns"
                    }
              , Attr{ attrKey = unqual "xmlns:xsi"
                    , attrVal = "http://www.w3.org/2001/XMLSchema-instance"
                    }
              , Attr{ attrKey = unqual "xsi:schemaLocation"
                    , attrVal = "http://graphml.graphdrawing.org/xmlns http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd"
                    }
              ] $
    unode "graphml" $
      [ keyNode "witness-type"   String Graph
      , keyNode "sourcecodelang" String Graph
      , keyNode "producer"       String Graph
      , keyNode "specification"  String Graph
      , keyNode "programfile"    String Graph
      , keyNode "programhash"    String Graph
      , keyNode "architecture"   String Graph
      , keyNode "creationtime"   String Graph

      , keyNode "entry"           Boolean Node
      , keyNode "sink"            Boolean Node
      , keyNode "violation"       Boolean Node
      , keyNode "invariant"       String  Node
      , keyNode "invariant.scope" String  Node

      , keyNode "assumption"                String  Edge
      , keyNode "assumption.scope"          String  Edge
      , keyNode "assumption.resultfunction" String  Edge
      , keyNode "control"                   String  Edge
      , keyNode "startline"                 Int     Edge
      , keyNode "endline"                   Int     Edge
      , keyNode "startoffset"               Int     Edge
      , keyNode "endoffset"                 Int     Edge
      , keyNode "enterLoopHead"             Boolean Edge
      , keyNode "enterFunction"             String  Edge
      , keyNode "returnFromFunction"        String  Edge
      , keyNode "threadId"                  String  Edge
      , keyNode "createThread"              String  Edge
        -- crux-llvm–specific extensions
      , keyNode "startcolumn"               Int     Edge

      , add_attr (Attr{attrKey = unqual "edgedefault", attrVal = "directed"}) $
        node n $
          [ dataNode "witness-type"   ppWitnessType    witnessType
          , dataNode "sourcecodelang" ppSourceCodeLang witnessSourceCodeLang
          , dataNode "producer"       ppString         witnessProducer
          , dataNode "specification"  ppString         witnessSpecification
          , dataNode "programfile"    ppString         witnessProgramFile
          , dataNode "programhash"    ppByteString     witnessProgramHash
          , dataNode "architecture"   ppArch           witnessArchitecture
          , dataNode "creationtime"   ppZonedTime      witnessCreationTime
          ] ++ map (unode "node") witnessNodes
            ++ map (unode "edge") witnessEdges
      ]
    where
      keyNode :: Id -> GraphMLAttrType -> GraphMLAttrDomain -> Element
      keyNode name ty domain =
        add_attrs [ Attr{attrKey = unqual "id",        attrVal = name}
                  , Attr{attrKey = unqual "attr.name", attrVal = name}
                  , Attr{attrKey = unqual "attr.type", attrVal = ppGraphMLAttrType ty}
                  , Attr{attrKey = unqual "for",       attrVal = ppGraphMLAttrDomain domain}
                  ] $
        case ty of
          Boolean -> unode "key" [unode "default" (ppBool False)]
          _       -> unode "key" ()

instance Node WitnessNode where
  node n WitnessNode{ nodeId, nodeEntry, nodeSink
                    , nodeViolation, nodeInvariant, nodeInvariantScope
                    } =
    add_attr (Attr{attrKey = unqual "id", attrVal = nodeId}) $
    node n $ catMaybes
      [ dataNode "entry"           ppBool   <$> nodeEntry
      , dataNode "sink"            ppBool   <$> nodeSink
      , dataNode "violation"       ppBool   <$> nodeViolation
      , dataNode "invariant"       ppString <$> nodeInvariant
      , dataNode "invariant.scope" ppString <$> nodeInvariantScope
      ]

instance Node WitnessEdge where
  node n WitnessEdge{ edgeSource, edgeTarget
                    , edgeAssumption, edgeAssumptionScope, edgeAssumptionResultFunction
                    , edgeControl, edgeStartLine, edgeEndLine, edgeStartOffset, edgeEndOffset
                    , edgeEnterLoopHead, edgeEnterFunction, edgeReturnFromFunction
                    , edgeThreadId, edgeCreateThread
                      -- crux-llvm–specific extensions
                    , edgeStartColumn
                    } =
    add_attrs [ Attr{attrKey = unqual "source", attrVal = edgeSource}
              , Attr{attrKey = unqual "target", attrVal = edgeTarget}
              ] $
    node n $ catMaybes
      [ dataNode "assumption"                ppAssumption <$> edgeAssumption
      , dataNode "assumption.scope"          ppString     <$> edgeAssumptionScope
      , dataNode "assumption.resultfunction" ppString     <$> edgeAssumptionResultFunction
      , dataNode "control"                   ppControl    <$> edgeControl
      , dataNode "startline"                 ppInt        <$> edgeStartLine
      , dataNode "endline"                   ppInt        <$> edgeEndLine
      , dataNode "startoffset"               ppInt        <$> edgeStartOffset
      , dataNode "endoffset"                 ppInt        <$> edgeEndOffset
      , dataNode "enterLoopHead"             ppBool       <$> edgeEnterLoopHead
      , dataNode "enterFunction"             ppString     <$> edgeEnterFunction
      , dataNode "returnFromFunction"        ppString     <$> edgeReturnFromFunction
      , dataNode "threadId"                  ppString     <$> edgeThreadId
      , dataNode "createThread"              ppString     <$> edgeCreateThread
      , dataNode "startcolumn"               ppInt        <$> edgeStartColumn
      ]
