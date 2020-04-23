{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ExistentialQuantification #-}
-- | This module deals with loading configurations.
module Crux.Config
  ( -- * Writing configurations
    Config(..), cfgJoin

    -- ** Configuration files
  , SectionsSpec, section, sectionMaybe
  , yesOrNoSpec, stringSpec, numSpec, fractionalSpec
  , oneOrList, fileSpec, dirSpec

    -- ** Environment variables
  , EnvDescr(..), mapEnvDescr

    -- ** Command line options
  , OptDescr(..), ArgDescr(..), OptSetter
  , mapOptDescr, mapArgDescr

  -- Unified config exports
  , CmdLineOptions(..)
  --, CmdLineOpt(..)
  --, CmdLineOptDoc(..)
  , opt
  , atom
  , withShortFlag
  , withDocumentation
  , withEnvironmentVar
  , isRepeatable
  , FlagYesOrNo(..)
  , OptUpdater(..)
  , ValSpec(..)
  , pathVal
  ) where

import           Data.Int
import           Data.Char
import           Data.List ( intercalate , lookup )
import           Data.Functor.Alt ( (<!>) )
import           Data.Foldable ( foldlM )
import           Numeric.Natural
import           Data.List.NonEmpty ( NonEmpty(..) )
import           Data.Word
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Tuple ( swap )

import Data.Maybe ( fromMaybe, listToMaybe, mapMaybe )

import SimpleGetOpt as SGO
import Config.Schema as CS


{- | Loading options from multiple sources.  First we load configuration
from a file, then we consider environment variables, and finally we
update using the command line flags. If there is no configuration file
provided, then this is equivalent to having an empty configuration file,
so the config file schema should be able to cope with missing settings. -}

data Config opts = Config
  { cfgFile     :: SectionsSpec opts
    -- ^ Configuration file settings (and, implicitly, defaults).

  , cfgEnv      :: [ EnvDescr opts ]
    -- ^ Settings from environment variables

  , cfgCmdLineFlag  :: [ OptDescr opts ]
    -- ^ Command line flags.
  }

-- | How the value of an environment variable contributes to the options.
data EnvDescr opts =
  EnvVar { evName  :: String                   -- ^ Name of variable
         , evDoc   :: String                   -- ^ Documentation
         , evValue :: String -> SGO.OptSetter opts -- ^ How it affects the options
         }


cfgJoin :: Config a -> Config b -> Config (a,b)
cfgJoin cfg1 cfg2 = Config
  { cfgFile         = (,) <$> cfgFile cfg1 <*> cfgFile cfg2
  , cfgEnv          = map (mapEnvDescr inFst) (cfgEnv cfg1) ++
                      map (mapEnvDescr inSnd) (cfgEnv cfg2)
  , cfgCmdLineFlag  = map (mapOptDescr inFst) (cfgCmdLineFlag cfg1) ++
                      map (mapOptDescr inSnd) (cfgCmdLineFlag cfg2)
  }

inFst :: SGO.OptSetter a -> SGO.OptSetter (a,b)
inFst f = \(a,b) -> do a' <- f a
                       pure (a',b)

inSnd :: SGO.OptSetter b -> SGO.OptSetter (a,b)
inSnd f = \(a,b) -> do b' <- f b
                       pure (a,b')

--------------------------------------------------------------------------------


-- | An option that can be configured in the file.
section :: Text        {- ^ Option name -} ->
           ValueSpec a {- ^ What type of value we expect -} ->
           a           {- ^ Default value to use if option not specified -} ->
           Text        {-^ Documentation -} ->
           SectionsSpec a
section nm spec def doc = fromMaybe def <$> optSection' nm spec doc

sectionMaybe :: Text {- ^ Option name -} ->
                ValueSpec a {- ^ What type of value we expect -} ->
                Text        {- ^ Documentation -} ->
                SectionsSpec (Maybe a)
sectionMaybe = optSection'

fileSpec :: ValueSpec FilePath
fileSpec = namedSpec "FILE" stringSpec

dirSpec :: ValueSpec FilePath
dirSpec = namedSpec "DIR" stringSpec

--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

mapEnvDescr :: (SGO.OptSetter a -> SGO.OptSetter b) -> EnvDescr a -> EnvDescr b
mapEnvDescr f e = e { evValue = f . evValue e }

mapArgDescr :: (SGO.OptSetter a -> SGO.OptSetter b) -> ArgDescr a -> ArgDescr b
mapArgDescr g ad =
  case ad of
    NoArg os   -> NoArg (g os)
    ReqArg s f -> ReqArg s (g . f)
    OptArg s f -> OptArg s (g . f)

mapOptDescr :: (SGO.OptSetter a -> SGO.OptSetter b) -> OptDescr a -> OptDescr b
mapOptDescr f o = o { optArgument = mapArgDescr f (optArgument o) }





--------------------------------------------------------------------------------
-- NEW: Config Unification Code
--------------------------------------------------------------------------------

-- | A unified specification for Crux command line
-- arguments/flags/options and how they impact the
-- underlying `config` parameter. The intent is that there
-- is essentially "one way" to think about how a Crux
-- program's execution can be configured/modified, from
-- which we can generate consistent and well-documented
-- command line, config file, and environment variable
-- parsing/handling.
data CmdLineOptions (config :: *) =
  CmdLineOptions
  { cmdLineParamDocs :: [(String, String)]
  -- ^ Documentation for the free-form parameters
  -- (i.e., parameters which are neither flags nor options).
  , cmdLineParamFn :: String -> config -> Either String config
  -- ^ Function called on the free-form parameters (i.e.,
  -- parameters which are neither flags nor options) in
  -- left-to-right order to update the configuration.
  , cmdLineParamConfigSection :: String
  -- ^ The name of the section in the config file which
  -- contains the free-form/positional parameters (i.e.,
  -- parameters which are neither flags nor options).
  , cmdLineOpts :: [CmdLineOpt config]
  -- ^ Flags or option specifications.
  }

-- | A Crux option---i.e., one which would be specified via
-- a command line flag or flag and argument (e.g., `-q` or
-- `--sim-verbose=NUM`)---describing the kind of expected
-- value, what flags/config file sections enable/update it,
-- what (if any) environment variable can set it, and both
-- concise and verbose documentation.
data CmdLineOpt (config :: *) =
  CmdLineOpt
  { cOptName :: String
  -- ^ The option's name (must be unique).
  , cOptShortFlags :: [Char]
  -- ^ Short (i.e., single character) command-line flags (if
  -- any) used to toggle the option. E.g., a help menu might
  -- use `['h','?']`.
  , cOptLongFlags :: [String]
    -- ^ Long (i.e., multi-character) command-line flags (if
    -- any) used to toggle the option. E.g., `["js-flags"]`.
  , cOptCanRepeat :: Bool
  -- ^ Is the intent that specifying this option more than
  -- one time produces a configuration that reflects that
  -- fact?  E.g., in gcc the `-l` flag can be repeated as
  -- many times as necessary to specify all the libraries to
  -- search while linking. In terms of a config file
  -- section, can the entry contain one-or-more entries
  -- instead of just a single entry? (N.B., even when this
  -- is False, a command line flag may still _technically_
  -- be passed multiple times without producing an explicit
  -- error by the command line argument parser, but the
  -- assumption is the program's configuration will only
  -- reflect having been updated with one (the last?) value
  -- passed.)
  , cOptConfigSection :: String
    -- ^ The name of the corresponding section in the config
    -- file where this option is specified.
  , cOptEnvVar :: Maybe String
  -- ^ The environment variable which can also specify
  -- this option (if any).
  , cOptDescription :: String
  -- ^ A short but clear description of the option, the kind
  -- that would appear next to a flag when the `--help` menu is
  -- printed.
  , cOptDocumentation :: CmdLineOptDoc
  -- ^ A longer description (if warranted), the kind that
  -- might appear in documentation for the tool (or further
  -- down in a man page).
  , cOptUpdater :: OptUpdater config
  -- ^ How should this option (when provided) update the
  -- configuration?
  }

-- | Describes the long form documentation to use for an
-- option, which can either be same as the options shorter
-- description (@SameAsDescr@) or a custom longer-form
-- description (@DocStr@)
data CmdLineOptDoc
  = DocSameAsDescr
  | DocStr String

-- | Used to indicate whether passing the flag is equivalent
-- to specifying `yes` or `no` in the config file.
data FlagYesOrNo =
  FlagIsYes
  | FlagIsNo
  deriving (Eq, Ord)

-- | Describes how an option updates the configuration
-- state.
data OptUpdater (config :: *) =
  -- | Describes how a flag (i.e., a yes/no config section)
  -- updates the config. For the command line arguments, the
  -- update function is called to update the config when the
  -- flag _is_ passed. If the flag is passed and the
  -- @FlagYesOrNo@ is @FlagIsYes@ then the updater will be
  -- called with @True@; if the flag is passed and the
  -- @FlagYesOrNo@ is @FlagIsNo@ then the updater will be
  -- called with @False@. For the config file, an entry of
  -- `yes` for the section will call the updater with @True@
  -- while `no` will call the updater with @False@.
  NoArgUpdater FlagYesOrNo (Bool -> config -> Either String config) (config -> Bool)
  -- | Describes how an option with a required argument
  --  value (e.g., gcc's `-o <file>`) updates the config and
  --  how to retrieve that value.
  | forall a . ReqArgUpdater (ValSpec a) (a -> config -> Either String config) (config -> a)
  -- | Describes how an option with an optional argument
  -- value updates the config and how to retrieve that
  -- value.
  | forall a . OptArgUpdater (ValSpec a) (Maybe a -> config -> Either String config) (config -> a)


-- | A description of option parameter values from which we
-- can essentially automatically generate consistent command
-- line flag/option parsers _and_ a Config.Schema
-- configuration file parser.
data ValSpec :: * -> * where
  -- | A raw string.
  StringVal   :: ValSpec String
  -- | A float.
  FloatVal    :: ValSpec Float
  -- | A double.
  DoubleVal   :: ValSpec Double
  -- | A rational.
  RationalVal :: ValSpec Rational
  -- | A fixed-size integer (i.e., a Haskell @Int@).
  IntVal      :: ValSpec Int
  -- | An 8-bit integer.
  Int8Val     :: ValSpec Int8
  -- | An 6-bit integer.
  Int16Val    :: ValSpec Int16
  -- | An 32-bit integer
  Int32Val    :: ValSpec Int32
  -- | An 64-bit integer.
  Int64Val    :: ValSpec Int64
  -- | An integer.
  IntegerVal  :: ValSpec Integer
  -- | A nonnegative integer.
  NaturalVal  :: ValSpec Natural
  -- | A fixed-size nonnegative integer (i.e., a Haskell @Word@).
  WordVal     :: ValSpec Word
  -- | An 8-bit nonnegative integer.
  Word8Val    :: ValSpec Word8
  -- | An 16-bit nonnegative integer.
  Word16Val   :: ValSpec Word16
  -- | An 32-bit nonnegative integer.
  Word32Val   :: ValSpec Word32
  -- | An 64-bit nonnegative integer.
  Word64Val   :: ValSpec Word64
  -- | An atom from a (non-empty) set of enumerated atomic
  -- literals. (N.B., comparisons are case-insensitive.)
  EnumVal    :: Eq a => [(String, a)] -> ValSpec a
  -- | A value matching one specification or the other,
  -- using left-biased precedence.
  EitherVal  :: ValSpec a -> ValSpec b -> ValSpec (Either a b)
  -- | A named custom value specification using an arbitrary
  -- string parser and printer--should only be used when other
  -- specifications are insufficient. N.B., the composition
  -- of the printer and parser should be the identity function.
  CustomVal  :: String -> (String -> Either String a) -> (a -> String) -> ValSpec a
  -- | A ValSpec with a custom name. N.B., since names are
  -- used like meta-variable in documentation, they should
  -- generally be in all caps and contain no spaces (e.g.,
  -- `INT`, `FILE_EXT`, etc).
  NamedVal :: String -> ValSpec a -> ValSpec a


-- | Check if a string is an atom, returning an error
-- message if it is not, otherwise return nothing.
isAtom :: String -> Maybe String
isAtom [] = Just "the empty string is not a valid atom"
isAtom str@(c:_)
  | not $ isAlpha c =
    Just $
    show c
    ++ " is not a valid start to an atom;"
    ++ " atoms must begin with alphabetic characters."
  | not $ all atomChar str =
    Just $
    show str
    ++ " is not a valid atom;"
    ++ " atoms must contain only alphabetic characters,"
    ++ " digits,  or one of '.', '_', or '-'."
    ++ show c
  | otherwise = Nothing
  where atomChar c = or $ map ($ c) [ isAlpha
                                    , isDigit
                                    , (=='.')
                                    , (=='_')
                                    , (=='-')]


newtype Atom = MkAtom { atomStr :: String }

atom :: String -> Atom
atom str = case isAtom str of
             Nothing -> MkAtom str
             Just errMsg -> error errMsg


-- | Given an initial/default Crux configuration and a
-- specification for the command line options and how they
-- relate to the config file contents and enviroment
-- variables, produce an updated Crux configuration.
cmdLineOptionsToConfig ::
  forall config .
  config
  -> CmdLineOptions config
  -> Config config
cmdLineOptionsToConfig defaultConfig
  CmdLineOptions { cmdLineParamDocs = freeFormParams
                 , cmdLineParamFn = cmdLineParamFn
                 , cmdLineParamConfigSection = paramFileSection
                 , cmdLineOpts = opts
                 } =
  Config { cfgFile =
           (flip fmap)
           secUpdater
           (\cfgUpdate ->
              case cfgUpdate defaultConfig of
                Left err -> error $ "Crux command line specification failed to produce a Config.Schema: " ++ err
                Right cfg' -> cfg')
         , cfgEnv = mapMaybe (toEnvDescr defaultConfig) opts
         , cfgCmdLineFlag = map (toOptDescr defaultConfig) opts
         }
  where secUpdater :: CS.SectionsSpec (config -> Either String config)
        secUpdater = toSectionsSpec defaultConfig paramFileSection paramFileDescr cmdLineParamFn opts
        paramFileDescr = intercalate ", " (map snd freeFormParams)




-- | Convert a @CmdLineOpt@ into a @EnvDescr@ if an
-- environment variable is associated with this option.
toEnvDescr ::
  config
  -> CmdLineOpt config
  -> Maybe (EnvDescr config)
toEnvDescr _ (CmdLineOpt {cOptEnvVar = Nothing}) = Nothing
toEnvDescr initialOrDefaultConfig
  CmdLineOpt { cOptEnvVar = Just name
             , cOptDescription = initialDescription
             , cOptUpdater = optUpdater
             } = Just $
  EnvVar { evName = name
         , evDoc = initialDescription ++ " (default: " ++ (showDefaultValue initialOrDefaultConfig optUpdater) ++ ")"
         , evValue = case optUpdater of
                       NoArgUpdater _ updater _ -> yesNoUpdater updater
                       ReqArgUpdater vSpec updater getter ->
                         valSpecUpdater vSpec updater
                       OptArgUpdater vSpec updater getter ->
                         (valSpecMaybeUpdater vSpec updater) . Just
         }


-- | Converts a funciton which updates a config with a bool to one
-- which updates a config given the strings "yes" or "no"
yesNoUpdater ::
  (Bool -> config -> Either String config) ->
  String ->
  config ->
  Either String config
yesNoUpdater updater str cfg
  | caseInsensitiveStringEq str "yes" = updater True cfg
  | caseInsensitiveStringEq str "no"  = updater False cfg
  | otherwise = Left $ "Expected `yes` or `no`, but got `" ++  str


-- | Produces a Config.Schema SectionsSpec which will update
-- a config based on parsed config file contents.
toSectionsSpec ::
  forall config .
  config
  -- ^ The initial/default configuration state.
  -> String
  -- ^ Name of the section where input files are listed.
  -> String
  -- ^ Description of the section where input files are listed.
  -> (String -> config -> Either String config)
  -- ^ Function which updates the config with a seen
  -- positional/free-form command-line argument
  -> [CmdLineOpt config]
  -- ^ The options to convert.
  -> CS.SectionsSpec (config -> Either String config)
toSectionsSpec initialOrDefaultConfig inputSecName inputSecDescr inputUpdater opts =
  foldl combine inputSec optSecs
  where inputSec = (flip fmap)
                   (CS.optSection' inputSecName' (CS.oneOrList fileSpec) inputSecDescr')
                   (\case Nothing  -> \cfg -> Right cfg
                          Just xs -> \cfg -> foldlM (flip inputUpdater) cfg xs)
        inputSecName'  = T.pack inputSecName
        inputSecDescr' = T.pack inputSecDescr
        combine ::
          CS.SectionsSpec (config -> Either String config)
          -> CS.SectionsSpec (config -> Either String config)
          -> CS.SectionsSpec (config -> Either String config)
        combine spec1 spec2 = do
          f <- spec1
          g <- spec2
          pure $ \cfg -> do
            cfg' <- f cfg
            g cfg'
        convert = toSingleSectionsSpecUpdater initialOrDefaultConfig
        optSecs :: [CS.SectionsSpec (config -> Either String config)]
        optSecs = map convert opts



-- | Convert a Crux command line option specification into a
-- SectionsSpec from Config.Schema which can update a config
-- given the user-provided section data.
toSingleSectionsSpecUpdater ::
  config
  -- ^ The initial/default configuration state.
  -> CmdLineOpt config
  -- ^ The option to convert.
  -> CS.SectionsSpec (config -> Either String config)
toSingleSectionsSpecUpdater initialOrDefaultConfig
  CmdLineOpt { cOptConfigSection = configSecName
             , cOptCanRepeat   = canRepeat
             , cOptDescription = initialDescription
             , cOptUpdater = optUpdater
             } =
  let secName = T.pack configSecName
      dfltLongDescr = T.pack $ initialDescription ++ " (default: " ++ (showDefaultValue initialOrDefaultConfig optUpdater) ++ ")"
      configId cfg = Right cfg
  in case optUpdater of
       NoArgUpdater flagYesOrNo updater _getter ->
         let dflt = if flagYesOrNo == FlagIsYes then "no" else "yes"
             yesNoDescr = T.pack $ initialDescription ++ " (default: " ++ dflt ++ ")"
         in (flip fmap)
            (CS.optSection' secName CS.yesOrNoSpec yesNoDescr)
            (\maybeSectionVal ->
               case maybeSectionVal of
                 -- If the option is provided, update the
                 -- config with the updater and that value.
                 Just True  -> updater True
                 Just False -> updater False
                 -- Otherwise the config won't be updated,
                 -- whether or not a section was provided.
                 _ -> configId)
       ReqArgUpdater vSpec updater _getter ->
         let spec = toValueSpec vSpec
         in if canRepeat
            then (flip fmap)
                 (CS.optSection' secName (CS.oneOrList spec) dfltLongDescr)
                 (\case Nothing  -> configId
                        Just xs -> \cfg -> foldlM (flip updater) cfg xs)
            else (flip fmap)
                 (CS.optSection' secName spec dfltLongDescr)
                 (\case Nothing  -> configId
                        Just val -> updater val)
       OptArgUpdater vSpec updater _getter ->
         let spec = toValueSpec vSpec
         in if canRepeat
            then (flip fmap)
                 (CS.optSection' secName (CS.oneOrList spec) dfltLongDescr)
                 (\case Nothing  -> configId
                        Just xs -> \cfg -> foldlM (\cfg x -> updater (Just x) cfg) cfg xs)
            else (flip fmap)
                 (CS.optSection' secName spec dfltLongDescr)
                 (\case Nothing  -> configId
                        Just val -> updater (Just val))

toValueSpec ::
  ValSpec x
  -- ^ How is the environment updated when it is enabled?
  -> CS.ValueSpec x
toValueSpec rawSpec = go rawSpec
  where
    go :: forall a . ValSpec a -> CS.ValueSpec a
    go StringVal   = CS.stringSpec
    go FloatVal    = CS.anySpec
    go DoubleVal   = CS.anySpec
    go RationalVal = CS.anySpec
    go IntVal      = CS.anySpec
    go Int8Val     = CS.anySpec
    go Int16Val    = CS.anySpec
    go Int32Val    = CS.anySpec
    go Int64Val    = CS.anySpec
    go IntegerVal  = CS.anySpec
    go NaturalVal  = CS.anySpec
    go WordVal     = CS.anySpec
    go Word8Val    = CS.anySpec
    go Word16Val   = CS.anySpec
    go Word32Val   = CS.anySpec
    go Word64Val   = CS.anySpec
    go (EnumVal []) = error "An Enum ValSpec must have at least one entry"
    go (EnumVal (e:es))
      | Just errMsg <- listToMaybe $ mapMaybe (isAtom . fst) (e:es) =
          error $ "Encountered an error in an EnumVal specification: " ++ errMsg
      | otherwise =
        let mkSpec (atom, val) = val <$ CS.atomSpec (T.pack atom)
        in foldl (<!>) (mkSpec e) $ map mkSpec es
    go (EitherVal l r)   = Left <$> (go l) <!> Right <$> (go r)
    go (CustomVal cName cParser _printer) =
      CS.customSpec (T.pack cName) CS.stringSpec (\str -> case cParser str of
                                                            Left msg -> Left $ T.pack msg
                                                            Right val -> Right val)
    go (NamedVal name spec) =
      CS.namedSpec (T.pack name) (go spec)



-- | Convert a Crux command line option specification into
-- an OptDescr from SimpleGetOpt (which is the module we
-- delegate the actual command line parsing implementation).
toOptDescr ::
  config
  -- ^ The initial/default configuration state.
  -> CmdLineOpt config
  -- ^ The option to convert.
  -> SGO.OptDescr config
toOptDescr initialOrDefaultConfig
  CmdLineOpt { cOptName = optName
             , cOptShortFlags  = sflags
             , cOptLongFlags   = lflags
             , cOptDescription = initialDescription
             , cOptUpdater = optUpdater
             } =
  SGO.Option { SGO.optShortFlags  = sflags
             , SGO.optLongFlags   = lflags
             , SGO.optDescription = description
             , SGO.optArgument    = toOptSetter optUpdater
             }
  where description = initialDescription ++ (showDefaultValue initialOrDefaultConfig optUpdater)

toOptSetter :: OptUpdater config -> SGO.ArgDescr config
toOptSetter (NoArgUpdater FlagIsYes updater _) = SGO.NoArg $ updater True
toOptSetter (NoArgUpdater FlagIsNo  updater _) = SGO.NoArg $ updater False
toOptSetter (ReqArgUpdater vSpec updater _) = SGO.ReqArg (valSpecDescription vSpec) (valSpecUpdater vSpec updater)
toOptSetter (OptArgUpdater vSpec updater _) = SGO.OptArg (valSpecDescription vSpec) (valSpecMaybeUpdater vSpec updater)


valSpecDescription :: ValSpec a -> String
valSpecDescription =
  \case
    StringVal          -> "STRING"
    FloatVal           -> "FLOAT"
    DoubleVal          -> "DOUBLE"
    RationalVal        -> "RATIONAL"
    IntVal             -> "INT"
    Int8Val            -> "INT8"
    Int16Val           -> "INT16"
    Int32Val           -> "INT32"
    Int64Val           -> "INT64"
    IntegerVal         -> "INTEGER"
    NaturalVal         -> "NATURAL"
    WordVal            -> "UINT"
    Word8Val           -> "UINT8"
    Word16Val          -> "UINT16"
    Word32Val          -> "UINT32"
    Word64Val          -> "UINT64"
    EnumVal es -> intercalate "|" $ map fst es
    CustomVal name _ _   -> name
    NamedVal  name _   -> name


valSpecUpdater ::
  ValSpec a
  -- ^ The description of the expected value from which we derive a parser.
  -> (a -> config -> Either String config)
  -- ^ The function which attempts to update the config with the parsed value.
  -> String
  -- ^ The raw string input to parse from the aforementioned derived parser.
  -> config
  -- ^ The config to update.
  -> Either String config
valSpecUpdater valSpec cfgUpdater rawStr config = do
  val <- valSpecParser valSpec rawStr
  cfgUpdater val config


valSpecMaybeUpdater ::
  ValSpec a
  -- ^ The description of the expected value from which we derive a parser.
  -> (Maybe a -> config -> Either String config)
  -- ^ The function which attempts to update the config with the parsed value.
  -> Maybe String
  -- ^ The raw string input (if any) to parse from the aforementioned derived parser.
  -> config
  -- ^ The config to update.
  -> Either String config
valSpecMaybeUpdater valSpec cfgUpdater Nothing config = cfgUpdater Nothing config
valSpecMaybeUpdater valSpec cfgUpdater (Just rawStr) config = do
  val <- valSpecParser valSpec rawStr
  cfgUpdater (Just val) config


-- | Produce a basic string parser for the specified kind of value.
valSpecParser :: ValSpec a -> String -> Either String a
valSpecParser initialValSpec =
  \str -> case parse str of
            Nothing -> Left $ "`"++str++"` is not a valid "++(valSpecDescription initialValSpec)
            Just val -> Right val
  where
    parse = go initialValSpec
    go :: forall a . ValSpec a -> String -> Maybe a
    go StringVal   = Just
    go FloatVal    = readParse
    go DoubleVal   = readParse
    go RationalVal = readParse
    go IntVal      = readParse
    go Int8Val     = readParse
    go Int16Val    = readParse
    go Int32Val    = readParse
    go Int64Val    = readParse
    go IntegerVal  = readParse
    go NaturalVal  = readParse
    go WordVal     = readParse
    go Word8Val    = readParse
    go Word16Val   = readParse
    go Word32Val   = readParse
    go Word64Val   = readParse
    go (EnumVal es) =
      \str ->
        let checkAtom (a, aVal) = if caseInsensitiveStringEq str a then Just aVal else Nothing
        in listToMaybe $ mapMaybe checkAtom es
    go (EitherVal vSpecA vSpecB) =
      let parseA = go vSpecA
          parseB = go vSpecB
      in \str -> maybe (Right <$> (parseB str)) (Just . Left) (parseA str)
    go (NamedVal _nm vSpec) = go vSpec
    -- A simple default parser for primitives with a Read instance.
    readParse :: (Read a) => String -> Maybe a
    readParse str = case reads str of
                      [] -> Nothing
                      ((val,_):_) -> Just val
    -- Case-insensitive string equality predicate

caseInsensitiveStringEq :: String -> String -> Bool
caseInsensitiveStringEq [] [] = True
caseInsensitiveStringEq (x:xs) (y:ys) = toLower x == toLower y && caseInsensitiveStringEq xs ys
caseInsensitiveStringEq _ _ = False


showDefaultVal :: ValSpec a -> a -> String
showDefaultVal vSpec val =
  case vSpec of
    StringVal   -> val
    FloatVal    -> show val
    DoubleVal   -> show val
    RationalVal -> show val
    IntVal      -> show val
    Int8Val     -> show val
    Int16Val    -> show val
    Int32Val    -> show val
    Int64Val    -> show val
    IntegerVal  -> show val
    NaturalVal  -> show val
    WordVal     -> show val
    Word8Val    -> show val
    Word16Val   -> show val
    Word32Val   -> show val
    Word64Val   -> show val
    (EnumVal es) ->
      case lookup val $ map swap es of
        Just str -> str
        Nothing -> error $ "default value for enum is not a user-visible option; options are "
                   ++ (show $ map fst es)
    EitherVal vSpecL vSpecR ->
      case val of
        Left lVal -> showDefaultVal vSpecL lVal
        Right rVal -> showDefaultVal vSpecR rVal 
    NamedVal _nm vSpec -> showDefaultVal vSpec val
    CustomVal _ _ printer -> printer val
  
showDefaultValue ::
  -- | The initial/default configuration.
  config ->
  -- | The updater for this option
  OptUpdater config ->
  -- | A string representing the default value.
  String
showDefaultValue initCfg optUpdater =
  case optUpdater of
    NoArgUpdater _ _ getter -> boolToYesNo $ getter initCfg
    ReqArgUpdater vSpec _ getter -> showDefaultVal vSpec $ getter initCfg
    OptArgUpdater vSpec _ getter -> showDefaultVal vSpec $ getter initCfg


boolToYesNo :: Bool -> String
boolToYesNo True = "yes"
boolToYesNo False = "no"


pathVal :: ValSpec FilePath
pathVal = NamedVal "PATH" StringVal



opt ::
  forall config .
  -- | Option name (i.e., human readable and Title Case).
  String ->
  -- | Name of the long flag and config section.
  Atom ->
  -- | Short description of the option/flag.
  String ->
  -- | How is the config updated.
  OptUpdater config ->
  -- | Command line option with a long flag, config section
  -- with the same name as the long flag, documentation the
  -- same as the short description, and the specified
  -- configuration updater.
  CmdLineOpt config
opt optName longFlagName descr updater = CmdLineOpt
  { cOptName = optName
  , cOptShortFlags = []
  , cOptLongFlags = [ atomStr longFlagName ]
  , cOptCanRepeat = False
  , cOptConfigSection = atomStr longFlagName
  , cOptEnvVar = Nothing
  , cOptDescription = descr
  , cOptDocumentation = DocSameAsDescr
  , cOptUpdater = updater
  }


-- | Adds the given character as a short command line flag.
withShortFlag ::
  forall config .
  Char ->
  CmdLineOpt config ->
  CmdLineOpt config
withShortFlag c o = o { cOptShortFlags = c:(cOptShortFlags o) }

-- | Set the command line option's documentation string.
withDocumentation ::
  forall config .
  String ->
  CmdLineOpt config ->
  CmdLineOpt config
withDocumentation docStr o = o { cOptDocumentation = DocStr docStr }

-- | Set the the command line option's environment variable.
withEnvironmentVar ::
  forall config .
  CmdLineOpt config ->
  String ->
  CmdLineOpt config
withEnvironmentVar o evar = o {cOptEnvVar = Just evar }

-- | Set the command line option's so it is repeatable
-- (i.e., so repeated usages of the flag are cumulative and
-- so the config file can contain one or a list of entries.
isRepeatable ::
  forall config .
  CmdLineOpt config ->
  CmdLineOpt config
isRepeatable o = o {cOptCanRepeat = True }
