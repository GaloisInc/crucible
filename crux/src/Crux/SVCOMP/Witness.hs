-- | This module defines a data type for SV-COMP witness automatons, as
--   specified in https://github.com/sosy-lab/sv-witnesses.

{-# Language NamedFieldPuns #-}
module Crux.SVCOMP.Witness
  ( Witness(..), WitnessNode(..), WitnessEdge(..)
  , WitnessType(..), SourceCodeLang(..), Control(..), GraphMLAttrType(..)
  , mkNode, mkNodeId, mkEdge
  , ppWitness
  ) where

import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B (unpack)
import qualified Data.List as L (intercalate)
import           Data.Maybe (catMaybes)
import           Data.Time.Format.ISO8601 (iso8601Show)
import           Data.Time.LocalTime (LocalTime(..), TimeOfDay(..), ZonedTime(..))
import           Text.XML.Light

import Crux.SVCOMP (Arch(..))

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
ppZonedTime = iso8601Show . roundNearestSecond
  where
    -- Round to the nearest second to ensure that we do not print out seconds
    -- with a decimal component. This is an unforunate hack to work around
    -- https://github.com/sosy-lab/sv-witnesses/issues/40.
    roundNearestSecond :: ZonedTime -> ZonedTime
    roundNearestSecond zt@ZonedTime{ zonedTimeToLocalTime =
                       lt@LocalTime{ localTimeOfDay =
                       tod@TimeOfDay{ todSec = sec }}} =
      zt{ zonedTimeToLocalTime =
      lt{ localTimeOfDay =
      tod{ todSec = fromInteger (round sec) }}}

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
