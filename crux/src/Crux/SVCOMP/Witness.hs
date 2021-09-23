-- | This module defines a data type for SV-COMP witness automatons, as
--   specified in https://github.com/sosy-lab/sv-witnesses.

{-# Language CPP #-}
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
import           Data.Time.LocalTime (LocalTime(..), TimeOfDay(..), ZonedTime(..))
import           Text.XML.Light

import Crux.SVCOMP (Arch(..))

#if MIN_VERSION_time(1,9,0)
import Data.Time.Format.ISO8601 (iso8601Show)
#else
import Data.Fixed (Pico)
import Data.Time.Calendar (Day, toGregorian)
import Data.Time.LocalTime (TimeZone(..))
#endif

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

#if !MIN_VERSION_time(1,9,0)
-- Unfortunately, @iso8601Show@ is only available in recent versions of the
-- @time@ library, so we backport the necessary machinery for older versions of
-- @time@ here.

-- | Show in the most commonly used ISO 8601 format.
iso8601Show :: ISO8601 t =>t -> String
iso8601Show = formatShow iso8601Format

class ISO8601 t where
    -- | The most commonly used ISO 8601 format for this type.
    iso8601Format :: Format t

-- | @yyyy-mm-dd@ (ISO 8601:2004(E) sec. 4.1.2.2 extended format)
instance ISO8601 Day where
    iso8601Format = calendarFormat ExtendedFormat

-- | @hh:mm:ss[.sss]@ (ISO 8601:2004(E) sec. 4.2.2.2, 4.2.2.4(a) extended format)
instance ISO8601 TimeOfDay where
    iso8601Format = timeOfDayFormat ExtendedFormat

-- | @yyyy-mm-ddThh:mm:ss[.sss]±hh:mm@ (ISO 8601:2004(E) sec. 4.3.2 extended format)
instance ISO8601 ZonedTime where
    iso8601Format = zonedTimeFormat iso8601Format iso8601Format ExtendedFormat

yearFormat' :: Format Integer
yearFormat' = integerFormat NegSign (Just 4)

monthFormat :: Format Int
monthFormat = integerFormat NoSign (Just 2)

dayOfMonthFormat :: Format Int
dayOfMonthFormat = integerFormat NoSign (Just 2)

hourFormat' :: Format Int
hourFormat' = integerFormat NoSign (Just 2)

minuteFormat :: Format Int
minuteFormat = integerFormat NoSign (Just 2)

secondFormat :: Format Pico
secondFormat = decimalFormat NoSign (Just 2)

mapGregorian :: Format (Integer, (Int, Int)) -> Format Day
mapGregorian =
    mapMFormat {-(\(y, (m, d)) -> fromGregorianValid y m d)-} (\day -> (\(y, m, d) -> Just (y, (m, d))) $ toGregorian day)

mapTimeOfDay :: Format (Int, (Int, Pico)) -> Format TimeOfDay
mapTimeOfDay = mapMFormat {-(\(h, (m, s)) -> isoMakeTimeOfDayValid h m s)-} (\(TimeOfDay h m s) -> Just (h, (m, s)))

-- | ISO 8601:2004(E) sec. 4.1.2.2
calendarFormat :: FormatExtension -> Format Day
calendarFormat fe = mapGregorian $ extDashFormat fe yearFormat $ extDashFormat fe monthFormat dayOfMonthFormat

-- | ISO 8601:2004(E) sec. 4.1.2.3(b)
yearFormat :: Format Integer
yearFormat = yearFormat'

-- | ISO 8601:2004(E) sec. 4.2.2.2, 4.2.2.4(a)
timeOfDayFormat :: FormatExtension -> Format TimeOfDay
timeOfDayFormat fe = mapTimeOfDay $ extColonFormat fe hourFormat' $ extColonFormat fe minuteFormat secondFormat

-- | ISO 8601:2004(E) sec. 4.2.2.5
withTimeDesignator :: Format t -> Format t
withTimeDesignator f = literalFormat "T" **> f

-- | ISO 8601:2004(E) sec. 4.2.5.1
timeOffsetFormat :: FormatExtension -> Format TimeZone
timeOffsetFormat fe =
    let -- toTimeZone (sign, (h, m)) = minutesToTimeZone $ sign * (h * 60 + m)
        fromTimeZone tz =
            let mm = timeZoneMinutes tz
                hm = quotRem (abs mm) 60
             in (signum mm, hm)
     in isoMap {-toTimeZone-} fromTimeZone $
            mandatorySignFormat <**> extColonFormat fe (integerFormat NoSign (Just 2)) (integerFormat NoSign (Just 2))

-- | ISO 8601:2004(E) sec. 4.3.2
localTimeFormat :: Format Day -> Format TimeOfDay -> Format LocalTime
localTimeFormat fday ftod =
    isoMap {-(\(day, tod) -> LocalTime day tod)-} (\(LocalTime day tod) -> (day, tod)) $ fday <**> withTimeDesignator ftod

-- | ISO 8601:2004(E) sec. 4.3.2
zonedTimeFormat :: Format Day -> Format TimeOfDay -> FormatExtension -> Format ZonedTime
zonedTimeFormat fday ftod fe =
    isoMap {-(\(lt, tz) -> ZonedTime lt tz)-} (\(ZonedTime lt tz) -> (lt, tz)) $
        timeAndOffsetFormat (localTimeFormat fday ftod) fe

-- | ISO 8601:2004(E) sec. 4.3.3
timeAndOffsetFormat :: Format t -> FormatExtension -> Format (t, TimeZone)
timeAndOffsetFormat ft fe = ft <**> timeOffsetFormat fe

class IsoVariant f where
    isoMap :: {-(a -> b) ->-} (b -> a) -> f a -> f b

instance IsoVariant Format where
    isoMap {-ab-} ba (MkFormat sa {-ra-}) = MkFormat (\b -> sa $ ba b) -- (fmap ab ra)

infixr 3 <**>, **>, <**

class IsoVariant f => Productish f where
    -- pUnit :: f ()
    (<**>) :: f a -> f b -> f (a, b)
    (**>) :: f () -> f a -> f a
    fu **> fa = isoMap {-(\((), a) -> a)-} (\a -> ((), a)) $ fu <**> fa
    (<**) :: f a -> f () -> f a
    fa <** fu = isoMap {-(\(a, ()) -> a)-} (\a -> (a, ())) $ fa <**> fu

instance Productish Format where
    -- pUnit = MkFormat{formatShowM = \_ -> Just "" {-, formatReadP = return ()-} }
    (<**>) (MkFormat sa {-ra-}) (MkFormat sb {-rb-}) =
        let sab (a, b) = do
                astr <- sa a
                bstr <- sb b
                return $ astr ++ bstr
            {-
            rab = do
                a <- ra
                b <- rb
                return (a, b)
            -}
         in MkFormat sab -- rab
    (MkFormat sa {-ra-}) **> (MkFormat sb {-rb-}) =
        let s b = do
                astr <- sa ()
                bstr <- sb b
                return $ astr ++ bstr
            {-
            r = do
                ra
                rb
            -}
         in MkFormat s -- r
    (MkFormat sa {-ra-}) <** (MkFormat sb {-rb-}) =
        let s a = do
                astr <- sa a
                bstr <- sb ()
                return $ astr ++ bstr
            {-
            r = do
                a <- ra
                rb
                return a
            -}
         in MkFormat s -- r

-- | A text format for a type
newtype {-data-} Format t = MkFormat
    { -- | Show a value in the format, if representable
      formatShowM :: t -> Maybe String
    {-
    , -- | Read a value in the format
      formatReadP :: ReadP t
    -}
    }

-- | Show a value in the format, or error if unrepresentable
formatShow :: Format t -> t -> String
formatShow fmt t =
    case formatShowM fmt t of
        Just str -> str
        Nothing -> error "formatShow: bad value"

mapMFormat :: {-(a -> Maybe b) ->-} (b -> Maybe a) -> Format a -> Format b
mapMFormat {-amb-} bma (MkFormat sa {-ra-}) =
    MkFormat (\b -> bma b >>= sa) {- $ do
        a <- ra
        case amb a of
            Just b -> return b
            Nothing -> pfail -}

data SignOption
    = NoSign
    | NegSign
    | PosNegSign

zeroPad :: Maybe Int -> String -> String
zeroPad Nothing s = s
zeroPad (Just i) s = replicate (i - length s) '0' ++ s

trimTrailing :: String -> String
trimTrailing "" = ""
trimTrailing "." = ""
trimTrailing s
    | last s == '0' = trimTrailing $ init s
trimTrailing s = s

showNumber :: Show t => SignOption -> Maybe Int -> t -> Maybe String
showNumber signOpt mdigitcount t =
    let showIt str =
            let (intPart, decPart) = break ((==) '.') str
             in (zeroPad mdigitcount intPart) ++ trimTrailing decPart
     in case show t of
            ('-' : str) ->
                case signOpt of
                    NoSign -> Nothing
                    _ -> Just $ '-' : showIt str
            str ->
                Just $
                    case signOpt of
                        PosNegSign -> '+' : showIt str
                        _ -> showIt str

literalFormat :: String -> Format ()
literalFormat s = MkFormat{formatShowM = \_ -> Just s {-, formatReadP = string s >> return ()-} }

casesFormat :: Eq a => [(a, String)] -> Format a
casesFormat pairs =
    let s t = lookup t pairs
        {-
        r [] = pfail
        r ((v, str) : pp) = (string str >> return v) <++ r pp
        -}
     in MkFormat s -- $ r pairs

mandatorySignFormat :: (Eq t, Num t) => Format t
mandatorySignFormat = casesFormat [(1, "+"), (0, "+"), (-1, "-")]

integerFormat :: (Show t, Read t, Num t) => SignOption -> Maybe Int -> Format t
integerFormat signOpt mdigitcount = MkFormat (showNumber signOpt mdigitcount) -- (readNumber signOpt mdigitcount False)

decimalFormat :: (Show t, Read t, Num t) => SignOption -> Maybe Int -> Format t
decimalFormat signOpt mdigitcount = MkFormat (showNumber signOpt mdigitcount) -- (readNumber signOpt mdigitcount True)

data FormatExtension
    = -- | ISO 8601:2004(E) sec. 2.3.4. Use hyphens and colons.
      ExtendedFormat
    | -- | ISO 8601:2004(E) sec. 2.3.3. Omit hyphens and colons. "The basic format should be avoided in plain text."
      BasicFormat

sepFormat :: String -> Format a -> Format b -> Format (a, b)
sepFormat sep fa fb = (fa <** literalFormat sep) <**> fb

dashFormat :: Format a -> Format b -> Format (a, b)
dashFormat = sepFormat "-"

colnFormat :: Format a -> Format b -> Format (a, b)
colnFormat = sepFormat ":"

extDashFormat :: FormatExtension -> Format a -> Format b -> Format (a, b)
extDashFormat ExtendedFormat = dashFormat
extDashFormat BasicFormat = (<**>)

extColonFormat :: FormatExtension -> Format a -> Format b -> Format (a, b)
extColonFormat ExtendedFormat = colnFormat
extColonFormat BasicFormat = (<**>)
#endif
