------------------------------------------------------------------------
-- |
-- Module      : What4.Config
-- Description : Declares attributes for simulator configuration settings.
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- This module provides access to persistent configuration settings, and
-- is designed for access both by Haskell client code of the What4 library,
-- and by users of the systems ultimately built using the library, for example,
-- from within a user-facing REPL.
--
-- Configurations are defined dynamically by combining a collection of
-- configuration option descriptions.  This allows disparate modules
-- to define their own configuration options, rather than having to
-- define the options for all modules in a central place.  Every
-- configuration option has a name, which consists of a nonempty
-- sequence of period-separated strings.  The intention is that option
-- names should conform to a namespace hierarchy both for
-- organizational purposes and to avoid namespace conflicts.  For
-- example, the options for an \"asdf\" module might be named as:
--
--    * asdf.widget
--    * asdf.frob
--    * asdf.max_bound
--
-- At runtime, a configuration consists of a collection of nested
-- finite maps corresponding to the namespace tree of the existing
-- options.  A configuration option may be queried or set either by
-- using a raw string representation of the name (see
-- @getOptionSettingFromText@), or by using a `ConfigOption` value
-- (using @getOptionSetting@), which provides a modicum of type-safety
-- over the basic dynamically-typed configuration maps.
--
-- Each option is associated with an \"option style\", which describes
-- the underlying type of the option (e.g., integer, boolean, string,
-- etc.) as well as the allowed settings of that value.  In addition,
-- options can take arbitrary actions when their values are changed in
-- the @opt_onset@ callback.
--
-- Every configuration comes with the built-in `verbosity`
-- configuration option pre-defined.  A `Config` value is constructed
-- using the `initialConfig` operation, which should be given the
-- initial verbosity value and a collection of configuration options
-- to install.  A configuration may be later extended with additional
-- options by using the `extendConfig` operation.
--
-- Example use (assuming the you wanted to use the z3 solver):
--
-- > import What4.Solver
-- >
-- > setupSolverConfig :: (IsExprBuilder sym) -> sym -> IO ()
-- > setupSolverConfig sym = do
-- >   let cfg = getConfiguration sym
-- >   extendConfig (solver_adapter_config_options z3Adapter) cfg
-- >   z3PathSetter <- getOptionSetting z3Path
-- >   res <- setOpt z3PathSetter "/usr/bin/z3"
-- >   assert (null res) (return ())
--
-- Developer's note: we might want to add the following operations:
--
--   * a method for \"unsetting\" options to restore the default state of an option
--   * a method for removing options from a configuration altogether
--       (i.e., to undo extendConfig)
------------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module What4.Config
  ( -- * Names of properties
    ConfigOption
  , configOption
  , configOptionType
  , configOptionName
  , configOptionText
  , configOptionNameParts

    -- * Option settings
  , OptionSetting(..)
  , Opt(..)

    -- * Defining option styles
  , OptionStyle(..)
  , set_opt_default
  , set_opt_onset

    -- ** OptionSetResult
  , OptionSetResult(..)
  , optOK
  , optWarn
  , optErr
  , checkOptSetResult

    -- ** Option style templates
  , Bound(..)
  , boolOptSty
  , integerOptSty
  , realOptSty
  , stringOptSty
  , realWithRangeOptSty
  , realWithMinOptSty
  , realWithMaxOptSty
  , integerWithRangeOptSty
  , integerWithMinOptSty
  , integerWithMaxOptSty
  , enumOptSty
  , listOptSty
  , executablePathOptSty

    -- * Describing configuration options
  , ConfigDesc
  , mkOpt
  , opt
  , optV
  , optU
  , optUV

    -- * Building and manipulating configurations
  , Config
  , initialConfig
  , extendConfig

  , getOptionSetting
  , getOptionSettingFromText

    -- * Extracting entire subtrees of the current configuration
  , ConfigValue(..)
  , getConfigValues

    -- * Printing help messages for configuration options
  , configHelp

    -- * Verbosity
  , verbosity
  , verbosityLogger
  ) where

import           Control.Applicative (Const(..))
import           Control.Exception
import           Control.Lens ((&))
import           Control.Monad.Identity
import           Control.Monad.IO.Class
import           Control.Monad.Writer.Strict hiding ((<>))
import           Data.Kind
import           Data.Maybe
import           Data.Typeable
import           Data.Foldable (toList)
import           Data.IORef
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Semigroup (Semigroup(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           Numeric.Natural
import           System.IO ( Handle, hPutStr )
import           System.IO.Error ( ioeGetErrorString )

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

import           What4.BaseTypes
import           What4.Concrete
import qualified What4.Utils.Environment as Env

-------------------------------------------------------------------------
-- ConfigOption

-- | A Haskell-land wrapper around the name of a configuration option.
--   Developers are encouraged to define and use `ConfigOption` values
--   to avoid two classes of errors: typos in configuration option names;
--   and dynamic type-cast failures.  Both classes of errors can be lifted
--   to statically-checkable failures (missing symbols and type-checking,
--   respectively) by consistently using `ConfigOption` values.
--
--   The following example indicates the suggested useage
--
-- @
--   asdfFrob :: ConfigOption BaseRealType
--   asdfFrob = configOption BaseRealRepr "asdf.frob"
--
--   asdfMaxBound :: ConfigOption BaseIntegerType
--   asdfMaxBound = configOption BaseIntegerRepr "asdf.max_bound"
-- @
data ConfigOption (tp :: BaseType) where
  ConfigOption :: BaseTypeRepr tp -> NonEmpty Text -> ConfigOption tp

instance Show (ConfigOption tp) where
  show = configOptionName

-- | Construct a `ConfigOption` from a string name.  Idomatic useage is
--   to define a single top-level `ConfigOption` value in the module where the option
--   is defined to consistently fix its name and type for all subsequent uses.
configOption :: BaseTypeRepr tp -> String -> ConfigOption tp
configOption tp nm =
  case splitPath (Text.pack nm) of
    Just ps -> ConfigOption tp ps
    Nothing -> error "config options cannot have an empty name"

-- | Split a text value on \' characters.  Return @Nothing@ if
--   the whole string, or any of its segments, is the empty string.
splitPath :: Text -> Maybe (NonEmpty Text)
splitPath nm =
   let nms = Text.splitOn "." nm in
   case nms of
     (x:xs) | all (not . Text.null) (x:xs) -> Just (x:|xs)
     _ -> Nothing

-- | Get the individual dot-separated segments of an option's name.
configOptionNameParts :: ConfigOption tp -> [Text]
configOptionNameParts (ConfigOption _ (x:|xs)) = x:xs

-- | Reconstruct the original string name of this option.
configOptionName :: ConfigOption tp -> String
configOptionName = Text.unpack . configOptionText

-- | Reconstruct the original string name of this option.
configOptionText :: ConfigOption tp -> Text
configOptionText (ConfigOption _ (x:|xs)) = Text.intercalate "." $ (x:xs)

-- | Retrieve the run-time type representation of @tp@.
configOptionType :: ConfigOption tp -> BaseTypeRepr tp
configOptionType (ConfigOption tp _) = tp

------------------------------------------------------------------------------
-- OptionSetResult

-- | When setting the value of an option, a validation function is called
--   (as defined by the associated @OptionStyle@).  The result of the validation
--   function is an @OptionSetResult@.  If the option value given is invalid
--   for some reason, an error should be returned.  Additionally, warning messages
--   may be returned, which will be passed through to the eventuall call site
--   attempting to alter the option setting.
data OptionSetResult =
  OptionSetResult
  { optionSetError    :: !(Maybe Doc)
  , optionSetWarnings :: !(Seq Doc)
  }

instance Semigroup OptionSetResult where
  x <> y = OptionSetResult
            { optionSetError    = optionSetError x <> optionSetError y
            , optionSetWarnings = optionSetWarnings x <> optionSetWarnings y
            }

instance Monoid OptionSetResult where
  mappend = (<>)
  mempty  = optOK

-- | Accept the new option value with no errors or warnings.
optOK :: OptionSetResult
optOK = OptionSetResult{ optionSetError = Nothing, optionSetWarnings = mempty }

-- | Reject the new option value with an error message.
optErr :: Doc -> OptionSetResult
optErr x = OptionSetResult{ optionSetError = Just x, optionSetWarnings = mempty }

-- | Accept the given option value, but report a warning message.
optWarn :: Doc -> OptionSetResult
optWarn x = OptionSetResult{ optionSetError = Nothing, optionSetWarnings = Seq.singleton x }


-- | An @OptionSetting@ gives the direct ability to query or set the current value
--   of an option.  The @getOption@ field is an action that, when executed, fetches
--   the current value of the option, if it is set.  The @setOption@ method attempts
--   to set the value of the option.  If the associated @opt_onset@ validation method
--   rejects the option, it will retain its previous value; otherwise it will be set
--   to the given value.  In either case, the generated @OptionSetResult@ will be
--   returned.
data OptionSetting (tp :: BaseType) =
  OptionSetting
  { optionSettingName :: ConfigOption tp
  , getOption :: IO (Maybe (ConcreteVal tp))
  , setOption :: ConcreteVal tp -> IO OptionSetResult
  }


-- | An option defines some metadata about how a configuration option behaves.
--   It contains a base type representation, which defines the runtime type
--   that is expected for setting and querying this option at runtime.
data OptionStyle (tp :: BaseType) =
  OptionStyle
  { opt_type :: BaseTypeRepr tp
    -- ^ base type representation of this option

  , opt_onset :: Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult
    -- ^ An operation for validating new option values.  This action may also
    -- be used to take actions whenever an option setting is changed.
    --
    -- The first argument is the current value of the option (if any).
    -- The second argument is the new value that is being set.
    -- If the validation fails, the operation should return a result
    -- describing why validation failed. Optionally, warnings may also be returned.

  , opt_help :: Doc
    -- ^ Documentation for the option to be displayed in the event a user asks for information
    --   about this option.  This message should contain information relevant to all options in this
    --   style (e.g., its type and range of expected values), not necessarily
    --   information about a specific option.

  , opt_default_value :: Maybe (ConcreteVal tp)
    -- ^ This gives a default value for the option, if set.
  }

-- | A basic option style for the given base type.
--   This option style performs no validation, has no
--   help information, and has no default value.
defaultOpt :: BaseTypeRepr tp -> OptionStyle tp
defaultOpt tp =
  OptionStyle
  { opt_type = tp
  , opt_onset = \_ _ -> return mempty
  , opt_help = empty
  , opt_default_value = Nothing
  }

-- | Update the @opt_onset@ field.
set_opt_onset :: (Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult)
                 -> OptionStyle tp
                 -> OptionStyle tp
set_opt_onset f s = s { opt_onset = f }

-- | Update the @opt_help@ field.
set_opt_help :: Doc
             -> OptionStyle tp
             -> OptionStyle tp
set_opt_help v s = s { opt_help = v }

-- | Update the @opt_default_value@ field.
set_opt_default :: ConcreteVal tp
              -> OptionStyle tp
              -> OptionStyle tp
set_opt_default v s = s { opt_default_value = Just v }


-- | An inclusive or exclusive bound.
data Bound r = Exclusive r
             | Inclusive r
             | Unbounded

-- | Standard option style for boolean-valued configuration options
boolOptSty :: OptionStyle BaseBoolType
boolOptSty = OptionStyle BaseBoolRepr
                        (\_ _ -> return optOK)
                        (text "Boolean")
                        Nothing

-- | Standard option style for real-valued configuration options
realOptSty :: OptionStyle BaseRealType
realOptSty = OptionStyle BaseRealRepr
                  (\_ _ -> return optOK)
                  (text "ℝ")
                  Nothing

-- | Standard option style for integral-valued configuration options
integerOptSty :: OptionStyle BaseIntegerType
integerOptSty = OptionStyle BaseIntegerRepr
                  (\_ _ -> return optOK)
                  (text "ℤ")
                  Nothing

stringOptSty :: OptionStyle BaseStringType
stringOptSty = OptionStyle BaseStringRepr
                  (\_ _ -> return optOK)
                  (text "string")
                  Nothing

checkBound :: Ord a => Bound a -> Bound a -> a -> Bool
checkBound lo hi a = checkLo lo a && checkHi a hi
 where checkLo Unbounded _ = True
       checkLo (Inclusive x) y = x <= y
       checkLo (Exclusive x) y = x <  y

       checkHi _ Unbounded     = True
       checkHi x (Inclusive y) = x <= y
       checkHi x (Exclusive y) = x <  y

docInterval :: Show a => Bound a -> Bound a -> Doc
docInterval lo hi = docLo lo <> text ", " <> docHi hi
 where docLo Unbounded      = text "(-∞"
       docLo (Exclusive r)  = text "(" <> text (show r)
       docLo (Inclusive r)  = text "[" <> text (show r)

       docHi Unbounded      = text "+∞)"
       docHi (Exclusive r)  = text (show r) <> text ")"
       docHi (Inclusive r)  = text (show r) <> text "]"


-- | Option style for real-valued options with upper and lower bounds
realWithRangeOptSty :: Bound Rational -> Bound Rational -> OptionStyle BaseRealType
realWithRangeOptSty lo hi = realOptSty & set_opt_onset vf
                                       & set_opt_help help
  where help = text "ℝ ∈" <+> docInterval lo hi
        vf :: Maybe (ConcreteVal BaseRealType) -> ConcreteVal BaseRealType -> IO OptionSetResult
        vf _ (ConcreteReal x)
          | checkBound lo hi x = return optOK
          | otherwise          = return $ optErr $
                                    text (show x) <+> text "out of range, expected real value in "
                                                  <+> docInterval lo hi

-- | Option style for real-valued options with a lower bound
realWithMinOptSty :: Bound Rational -> OptionStyle BaseRealType
realWithMinOptSty lo = realWithRangeOptSty lo Unbounded

-- | Option style for real-valued options with an upper bound
realWithMaxOptSty :: Bound Rational -> OptionStyle BaseRealType
realWithMaxOptSty hi = realWithRangeOptSty Unbounded hi

-- | Option style for integer-valued options with upper and lower bounds
integerWithRangeOptSty :: Bound Integer -> Bound Integer -> OptionStyle BaseIntegerType
integerWithRangeOptSty lo hi = integerOptSty & set_opt_onset vf
                                              & set_opt_help help
  where help = text "ℤ ∈" <+> docInterval lo hi
        vf :: Maybe (ConcreteVal BaseIntegerType) -> ConcreteVal BaseIntegerType -> IO OptionSetResult
        vf _ (ConcreteInteger x)
          | checkBound lo hi x = return optOK
          | otherwise          = return $ optErr $
                                    text (show x) <+> text "out of range, expected integer value in "
                                                  <+> docInterval lo hi

-- | Option style for integer-valued options with a lower bound
integerWithMinOptSty :: Bound Integer -> OptionStyle BaseIntegerType
integerWithMinOptSty lo = integerWithRangeOptSty lo Unbounded

-- | Option style for integer-valued options with an upper bound
integerWithMaxOptSty :: Bound Integer -> OptionStyle BaseIntegerType
integerWithMaxOptSty hi = integerWithRangeOptSty Unbounded hi

-- | A configuration style for options that must be one of a fixed set of text values
enumOptSty :: Set Text -> OptionStyle BaseStringType
enumOptSty elts = stringOptSty & set_opt_onset vf
                               & set_opt_help help
  where help = group (text "one of: " <+> align (sep $ map (dquotes . text . Text.unpack) $ Set.toList elts))
        vf :: Maybe (ConcreteVal BaseStringType) -> ConcreteVal BaseStringType -> IO OptionSetResult
        vf _ (ConcreteString x)
         | x `Set.member` elts = return optOK
         | otherwise = return $ optErr $
                            text "invalid setting" <+> text (show x) <+>
                            text ", expected one of:" <+>
                            align (sep (map (text . Text.unpack) $ Set.toList elts))

-- | A configuration syle for options that must be one of a fixed set of text values.
--   Associated with each string is a validation/callback action that will be run
--   whenever the named string option is selected.
listOptSty
  :: Map Text (IO OptionSetResult)
  -> OptionStyle BaseStringType
listOptSty values =  stringOptSty & set_opt_onset vf
                                  & set_opt_help help
  where help = group (text "one of: " <+> align (sep $ map (dquotes . text . Text.unpack . fst) $ Map.toList values))
        vf :: Maybe (ConcreteVal BaseStringType) -> ConcreteVal BaseStringType -> IO OptionSetResult
        vf _ (ConcreteString x) =
         fromMaybe
          (return $ optErr $
            text "invalid setting" <+> text (show x) <+>
            text ", expected one of:" <+>
            align (sep (map (text . Text.unpack . fst) $ Map.toList values)))
          (Map.lookup x values)


-- | A configuration style for options that are expected to be paths to an executable
--   image.  Configuration options with this style generate a warning message if set to a
--   value that cannot be resolved to an absolute path to an executable file in the
--   current OS environment.
executablePathOptSty :: OptionStyle BaseStringType
executablePathOptSty = stringOptSty & set_opt_onset vf
                                    & set_opt_help help
  where help = text "<path>"
        vf :: Maybe (ConcreteVal BaseStringType) -> ConcreteVal BaseStringType -> IO OptionSetResult
        vf _ (ConcreteString x) =
                 do me <- try (Env.findExecutable (Text.unpack x))
                    case me of
                       Right{} -> return $ optOK
                       Left e  -> return $ optWarn $ text $ ioeGetErrorString e


-- | A @ConfigDesc@ describes a configuration option before it is installed into
--   a @Config@ object.  It consists of a @ConfigOption@ name for the option,
--   an @OptionStyle@ describing the sort of option it is, and an optional
--   help message describing the semantics of this option.
data ConfigDesc where
  ConfigDesc :: ConfigOption tp -> OptionStyle tp -> Maybe Doc -> ConfigDesc

-- | The most general method for construcing a normal `ConfigDesc`.
mkOpt :: ConfigOption tp     -- ^ Fixes the name and the type of this option
      -> OptionStyle tp      -- ^ Define the style of this option
      -> Maybe Doc           -- ^ Help text
      -> Maybe (ConcreteVal tp) -- ^ A default value for this option
      -> ConfigDesc
mkOpt o sty h def = ConfigDesc o sty{ opt_default_value = def } h

-- | Construct an option using a default style with a given initial value
opt :: Pretty help
    => ConfigOption tp      -- ^ Fixes the name and the type of this option
    -> ConcreteVal tp       -- ^ Default value for the option
    -> help                 -- ^ An informational message describing this option
    -> ConfigDesc
opt o a help = mkOpt o (defaultOpt (configOptionType o))
                       (Just (pretty help))
                       (Just a)

-- | Construct an option using a default style with a given initial value.
--   Also provide a validation function to check new values as they are set.
optV :: forall tp help
      . Pretty help
     => ConfigOption tp      -- ^ Fixes the name and the type of this option
     -> ConcreteVal tp       -- ^ Default value for the option
     -> (ConcreteVal tp -> Maybe help)
         -- ^ Validation function.  Return `Just err` if the value to set
         --   is not valid.
     -> help                -- ^ An informational message describing this option
     -> ConfigDesc
optV o a vf h = mkOpt o (defaultOpt (configOptionType o)
                           & set_opt_onset onset)
                        (Just (pretty h))
                        (Just a)

   where onset :: Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult
         onset _ x = case vf x of
                       Nothing -> return optOK
                       Just z  -> return $ optErr $ pretty z

-- | Construct an option using a default style with no initial value.
optU :: Pretty help
     => ConfigOption tp    -- ^ Fixes the name and the type of this option
     -> help               -- ^ An informational message describing this option
     -> ConfigDesc
optU o h = mkOpt o (defaultOpt (configOptionType o)) (Just (pretty h)) Nothing

-- | Construct an option using a default style with no initial value.
--   Also provide a validation function to check new values as they are set.
optUV :: forall help tp.
   Pretty help =>
   ConfigOption tp {- ^ Fixes the name and the type of this option -} ->
   (ConcreteVal tp -> Maybe help) {- ^ Validation function.  Return `Just err` if the value to set is not valid. -} ->
   help                {- ^ An informational message describing this option -} ->
   ConfigDesc
optUV o vf h = mkOpt o (defaultOpt (configOptionType o)
                            & set_opt_onset onset)
                       (Just (pretty h))
                       Nothing
   where onset :: Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult
         onset _ x = case vf x of
                       Nothing -> return optOK
                       Just z  -> return $ optErr $ pretty z

------------------------------------------------------------------------
-- ConfigState

data ConfigLeaf where
  ConfigLeaf ::
    !(OptionStyle tp)              {- Style for this option -} ->
    IORef (Maybe (ConcreteVal tp)) {- State of the option -} ->
    Maybe Doc                      {- Help text for the option -} ->
    ConfigLeaf

-- | Main configuration data type.  It is organized as a trie based on the
--   name segments of the configuration option name.
data ConfigTrie where
  ConfigTrie ::
    !(Maybe ConfigLeaf) ->
    !ConfigMap ->
    ConfigTrie

type ConfigMap = Map Text ConfigTrie

freshLeaf :: [Text] -> ConfigLeaf -> ConfigTrie
freshLeaf [] l     = ConfigTrie (Just l) mempty
freshLeaf (a:as) l = ConfigTrie Nothing (Map.singleton a (freshLeaf as l))

-- | The given list of name segments defines a lens into a config trie.
adjustConfigTrie :: Functor t => [Text] -> (Maybe ConfigLeaf -> t (Maybe ConfigLeaf)) -> Maybe (ConfigTrie) -> t (Maybe ConfigTrie)
adjustConfigTrie     as f Nothing                 = fmap (freshLeaf as) <$> f Nothing
adjustConfigTrie (a:as) f (Just (ConfigTrie x m)) = Just . ConfigTrie x <$> adjustConfigMap a as f m
adjustConfigTrie     [] f (Just (ConfigTrie x m)) = g <$> f x
  where g Nothing | Map.null m = Nothing
        g x' = Just (ConfigTrie x' m)

-- | The given nonempty list of name segments (with the initial segment given as the first argument)
--   defines a lens into a @ConfigMap@.
adjustConfigMap :: Functor t => Text -> [Text] -> (Maybe ConfigLeaf -> t (Maybe ConfigLeaf)) -> ConfigMap -> t ConfigMap
adjustConfigMap a as f = Map.alterF (adjustConfigTrie as f) a

-- | Traverse an entire @ConfigMap@.  The first argument is
traverseConfigMap ::
  Applicative t =>
  [Text] {- ^ A REVERSED LIST of the name segments that represent the context from the root to the current @ConfigMap@. -} ->
  ([Text] -> ConfigLeaf -> t ConfigLeaf) {- ^ An action to apply to each leaf. The path to the leaf is provided. -} ->
  ConfigMap {- ^ ConfigMap to traverse -} ->
  t ConfigMap
traverseConfigMap revPath f = Map.traverseWithKey (\k -> traverseConfigTrie (k:revPath) f)

-- | Traverse an entire @ConfigTrie@.
traverseConfigTrie ::
  Applicative t =>
  [Text] {- ^ A REVERSED LIST of the name segments that represent the context from the root to the current @ConfigTrie@. -} ->
  ([Text] -> ConfigLeaf -> t ConfigLeaf) {- ^ An action to apply to each leaf. The path to the leaf is provided. -} ->
  ConfigTrie {- ^ @ConfigTrie@ to traverse -} ->
  t ConfigTrie
traverseConfigTrie revPath f (ConfigTrie x m) =
  ConfigTrie <$> traverse (f (reverse revPath)) x <*> traverseConfigMap revPath f m

-- | Traverse a subtree of a @ConfigMap@.  If an empty path is provided, the entire @ConfigMap@ will
--   be traversed.
traverseSubtree ::
  Applicative t =>
  [Text] {- ^ Path indicating the subtree to traverse -} ->
  ([Text] -> ConfigLeaf -> t ConfigLeaf) {- ^ Action to apply to each leaf in the indicated subtree.  The path to the leaf is provided. -} ->
  ConfigMap {- ^ @ConfigMap@ to traverse -} ->
  t ConfigMap
traverseSubtree ps0 f = go ps0 []
  where
  go     [] revPath = traverseConfigMap revPath f
  go (p:ps) revPath = Map.alterF (traverse g) p
     where g (ConfigTrie x m) = ConfigTrie x <$> go ps (p:revPath) m


-- | Add an option to the given @ConfigMap@.
insertOption :: MonadIO m => ConfigDesc -> ConfigMap -> m ConfigMap
insertOption (ConfigDesc (ConfigOption _tp (p:|ps)) sty h) m = adjustConfigMap p ps f m
  where
  f Nothing  =
       do ref <- liftIO (newIORef (opt_default_value sty))
          return (Just (ConfigLeaf sty ref h))
  f (Just _) = fail ("Option " ++ showPath ++ " already exists")

  showPath = Text.unpack (Text.intercalate "." (p:ps))


------------------------------------------------------------------------
-- Config

-- | The main configuration datatype.  It consists of an IORef
--   continaing the actual configuration data.
newtype Config = Config (IORef ConfigMap)

-- | Construct a new configuration from the given configuration
--   descriptions.
initialConfig :: Integer           -- ^ Initial value for the `verbosity` option
              -> [ConfigDesc]      -- ^ Option descriptions to install
              -> IO (Config)
initialConfig initVerbosity ts = do
   cfg <- Config <$> newIORef Map.empty
   extendConfig (builtInOpts initVerbosity ++ ts) cfg
   return cfg

-- | Extend an existing configuration with new options.  An error will be
--   raised if any of the given options clash with options that already exists.
extendConfig :: [ConfigDesc]
             -> Config
             -> IO ()
extendConfig ts (Config cfg) =
  (readIORef cfg >>= \m -> foldM (flip insertOption) m ts) >>= writeIORef cfg

-- | Verbosity of the simulator.  This option controls how much
--   informational and debugging output is generated.
--   0 yields low information output; 5 is extremely chatty.
verbosity :: ConfigOption BaseIntegerType
verbosity = configOption BaseIntegerRepr "verbosity"

-- | Built-in options that are installed in every @Config@ object.
builtInOpts :: Integer -> [ConfigDesc]
builtInOpts initialVerbosity =
  [ opt verbosity
        (ConcreteInteger initialVerbosity)
        (text "Verbosity of the simulator: higher values produce more detailed informational and debugging output.")
  ]

-- | Return an operation that will consult the current value of the
--   verbosity option, and will print a string to the given @Handle@
--   if the provided int is smaller than the current verbosity setting.
verbosityLogger :: Config -> Handle -> IO (Int -> String -> IO ())
verbosityLogger cfg h =
  do verb <- getOptionSetting verbosity cfg
     return $ \n msg ->
       do v <- getOpt verb
          when (toInteger n < v) (hPutStr h msg)

-- | A utility class for making working with option settings
--   easier.  The @tp@ argument is a @BaseType@, and the @a@
--   argument is an associcated Haskell type.
class Opt (tp :: BaseType) (a :: Type) | tp -> a where
  -- | Return the current value of the option, as a @Maybe@ value.
  getMaybeOpt :: OptionSetting tp -> IO (Maybe a)

  -- | Attempt to set the value of an option.  Return any errors
  --   or warnings.
  trySetOpt :: OptionSetting tp -> a -> IO OptionSetResult

  -- | Set the value of an option.  Return any generated warnings.
  --   Throw an exception if a validation error occurs.
  setOpt :: OptionSetting tp -> a -> IO [Doc]
  setOpt x v = trySetOpt x v >>= checkOptSetResult

  -- | Get the current value of an option.  Throw an exception
  --   if the option is not currently set.
  getOpt :: OptionSetting tp -> IO a
  getOpt x = maybe (fail msg) return =<< getMaybeOpt x
    where msg = "Option is not set: " ++ show (optionSettingName x)

-- | Throw an exception if the given @OptionSetResult@ indidcates
--   an error.  Otherwise, return any generated warnings.
checkOptSetResult :: OptionSetResult -> IO [Doc]
checkOptSetResult res =
  case optionSetError res of
    Just msg -> fail (show msg)
    Nothing -> return (toList (optionSetWarnings res))

instance Opt BaseStringType Text where
  getMaybeOpt x = fmap fromConcreteString <$> getOption x
  trySetOpt x v = setOption x (ConcreteString v)

instance Opt BaseNatType Natural where
  getMaybeOpt x = fmap fromConcreteNat <$> getOption x
  trySetOpt x v = setOption x (ConcreteNat v)

instance Opt BaseIntegerType Integer where
  getMaybeOpt x = fmap fromConcreteInteger <$> getOption x
  trySetOpt x v = setOption x (ConcreteInteger v)

instance Opt BaseBoolType Bool where
  getMaybeOpt x = fmap fromConcreteBool <$> getOption x
  trySetOpt x v = setOption x (ConcreteBool v)

-- | Given a @ConfigOption@ name, produce an @OptionSetting@
--   object for accessing and setting the value of that option.
--
--   An exception is thrown if the named option cannot be found
--   the @Config@ object, or if a type mismatch occurs.
getOptionSetting ::
  ConfigOption tp ->
  Config ->
  IO (OptionSetting tp)
getOptionSetting o@(ConfigOption tp (p:|ps)) (Config cfg) =
  getConst . adjustConfigMap p ps f =<< readIORef cfg
 where
  f Nothing  = Const (fail $ "Option not found: " ++ show o)
  f (Just x) = Const (leafToSetting x)

  leafToSetting (ConfigLeaf sty ref _h)
    | Just Refl <- testEquality (opt_type sty) tp = return $
      OptionSetting
      { optionSettingName = o
      , getOption  = readIORef ref
      , setOption = \v ->
          do old <- readIORef ref
             res <- opt_onset sty old v
             unless (isJust (optionSetError res)) (writeIORef ref (Just v))
             return res
      }
    | otherwise = fail ("Type mismatch retriving option " ++ show o ++
                         "\nExpected: " ++ show tp ++ " but found " ++ show (opt_type sty))

-- | Given a text name, produce an @OptionSetting@
--   object for accessing and setting the value of that option.
--
--   An exception is thrown if the named option cannot be found.
getOptionSettingFromText ::
  Text ->
  Config ->
  IO (Some OptionSetting)
getOptionSettingFromText nm (Config cfg) =
   case splitPath nm of
     Nothing -> fail "Illegal empty name for option"
     Just (p:|ps) -> getConst . adjustConfigMap p ps (f (p:|ps)) =<< readIORef cfg
  where
  f (p:|ps) Nothing  = Const (fail $ "Option not found: " ++ (Text.unpack (Text.intercalate "." (p:ps))))
  f path (Just x) = Const (leafToSetting path x)

  leafToSetting path (ConfigLeaf sty ref _h) = return $
    Some OptionSetting
         { optionSettingName = ConfigOption (opt_type sty) path
         , getOption = readIORef ref
         , setOption = \v ->
             do old <- readIORef ref
                res <- opt_onset sty old v
                unless (isJust (optionSetError res)) (writeIORef ref (Just v))
                return res
         }


-- | A @ConfigValue@ bundles together the name of an option with its current value.
data ConfigValue where
  ConfigValue :: ConfigOption tp -> ConcreteVal tp -> ConfigValue

-- | Given the name of a subtree, return all
--   the currently-set configurtion values in that subtree.
--
--   If the subtree name is empty, the entire tree will be traversed.
getConfigValues ::
  Text ->
  Config ->
  IO [ConfigValue]
getConfigValues prefix (Config cfg) =
  do m <- readIORef cfg
     let ps = Text.splitOn "." prefix
         f :: [Text] -> ConfigLeaf -> WriterT (Seq ConfigValue) IO ConfigLeaf
         f [] _ = fail $ "getConfigValues: illegal empty option name"
         f (p:path) l@(ConfigLeaf sty ref _h) =
            do liftIO (readIORef ref) >>= \case
                 Just x  -> tell (Seq.singleton (ConfigValue (ConfigOption (opt_type sty) (p:|path)) x))
                 Nothing -> return ()
               return l
     toList <$> execWriterT (traverseSubtree ps f m)


ppSetting :: [Text] -> Maybe (ConcreteVal tp) -> Doc
ppSetting nm v = fill 30 (text (Text.unpack (Text.intercalate "." nm))
                           <> maybe empty (\x -> text " = " <> ppConcrete x) v
                         )

ppOption :: [Text] -> OptionStyle tp -> Maybe (ConcreteVal tp) -> Maybe Doc -> Doc
ppOption nm sty x help =
   group (ppSetting nm x <//> indent 2 (opt_help sty)) <$$> maybe empty (indent 2) help

ppConfigLeaf :: [Text] -> ConfigLeaf -> IO Doc
ppConfigLeaf nm (ConfigLeaf sty ref help) =
  do x <- readIORef ref
     return $ ppOption nm sty x help

-- | Given the name of a subtree, compute help text for
--   all the options avaliable in that subtree.
--
--   If the subtree name is empty, the entire tree will be traversed.
configHelp ::
  Text ->
  Config ->
  IO [Doc]
configHelp prefix (Config cfg) =
  do m <- readIORef cfg
     let ps = Text.splitOn "." prefix
         f :: [Text] -> ConfigLeaf -> WriterT (Seq Doc) IO ConfigLeaf
         f nm leaf = do d <- liftIO (ppConfigLeaf nm leaf)
                        tell (Seq.singleton d)
                        return leaf
     toList <$> (execWriterT (traverseSubtree ps f m))
