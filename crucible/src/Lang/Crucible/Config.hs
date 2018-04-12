------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Config
-- Description : Declares attributes for simulator configuration settings.
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- This module provides access to simulator's persistent configuration settings,
-- both from the Haskell codebase of the simulator itself, and from within
-- client code running on the simulator.
--
-- Configurations are defined dynamically by combining a collection of configuration
-- option descriptions.  This allows disparate modules to define their own
-- configuration options, rather than having to define the options for all modules
-- in a central place.  Every configuration option has a name, which consists
-- of a nonempty sequence of period-separated strings.  The intention is that
-- option names should conform to a namespace hierarchy both for organizational
-- purposes and to avoid namespace conflicts.  For example, the options for
-- an \"asdf\" module might be named as:
--
--    * asdf.widget
--    * asdf.frob
--    * asdf.max_bound
--
-- At runtime, a configuration consists of a collection of nested finite maps
-- corresponding to the namespace tree of the existing options.  A configuration
-- option may be queried or set either by using a raw string representation of
-- the name, or by using a `ConfigOption` value, which provides a modicum of
-- type-safety over the basic dynamically-typed configuration maps.
--
-- When defining configuration options, there are two basic sorts to be aware of:
-- regular configuration options and list configuration options.  A regular option
-- the the usual choice.  Regular options have a name, and a Haskell type representing
-- the type of values that can be stored in the option.  In addition, each regular
-- option is associated to an `OptionStyle` which gives an interface for querying and
-- setting an option at Crucible-runtime as well as an operation to run whenever the
-- value of the option is changed (to e.g., check the validity of the new value, or
-- to take some specific action at the time of the change).  A variety of default
-- option styles are provided.
--
-- The second sort of option to be aware of is the \"list\" option.  A the possible
-- settings for a list option are drawn from an explicitly specified list.
-- Unlike the regular options, list options may have /overlapping definitions/.
-- More explicitly, note that an attempt to define two
-- regular option with the same name will result in an error when building the initial
-- configuration at startup; the regular options must all be disjoint.  However,
-- list options can overlap, and the possible settings defined in one module will be combined
-- with the settings defined in another.  For example, this is useful for allowing multiple
-- implementations of some common interface to register themselves as possible choices
-- for a single configuration option.
--
-- Every configuration comes with the built-in `verbosity` configuration option pre-defined.
-- A `Config` value is constructed using the `initialConfig` operation, which should
-- be given the initial verbosity value and a collection of configuration options to
-- install.  A configuration may be later extended with additionl options by using
-- the `extendConfig` operation.
--
-- Developer's note: we might want to add the following operations:
--
--   * a method for \"unsetting\" options to restore the default state of an option
--   * a method for removing options from a configuration altogether
--       (i.e., to undo extendConfig)
------------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Lang.Crucible.Config
  ( -- * Names of properties
    ConfigOption
  , configOption
  , configOptionType
  , configOptionName
  , configOptionText
  , configOptionNameParts

    -- * OptionSetResult
  , OptionSetResult(..)
  , optOK
  , optWarn
  , optErr

    -- * Defining option styles
  , OptionStyle(..)
  , set_opt_value
  , set_opt_onset
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
  , executablePathOptSty

    -- * Describing configuration options
  , ConfigDesc
  , mkOpt
  , opt
  , optV
  , optU
  , optUV
  , optList
  , optListStr
  , optListShow

    -- * Building and manipulating configurations
  , Config
  , initialConfig
  , extendConfig

  , getConfigValue
  , getConfigValue'
  , setConfigValue
  , readConfigValue
  , writeConfigValue

  , ConfigValue(..)
  , getConfigValues

  , configHelp

  -- * Concrete default options
  , verbosity
  ) where

import           Control.Applicative (Const(..))
import           Control.Exception
import           Control.Lens ((&))
import           Control.Monad.Fail (MonadFail)
import           Control.Monad.Identity
import           Control.Monad.IO.Class
import           Control.Monad.Writer.Strict hiding ((<>))
import           Data.Typeable
import           Data.Foldable (toList)
import           Data.IORef
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Semigroup (Semigroup(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           System.IO.Error ( ioeGetErrorString )

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

import           Lang.Crucible.BaseTypes
import qualified Lang.Crucible.Simulator.Utils.Environment as Env
import           Lang.Crucible.Solver.Concrete

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

configOptionType :: ConfigOption tp -> BaseTypeRepr tp
configOptionType (ConfigOption tp _) = tp

------------------------------------------------------------------------------
-- OptionSetResult

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

optOK :: OptionSetResult
optOK = OptionSetResult{ optionSetError = Nothing, optionSetWarnings = mempty }

optErr :: Doc -> OptionSetResult
optErr x = OptionSetResult{ optionSetError = Just x, optionSetWarnings = mempty }

optWarn :: Doc -> OptionSetResult
optWarn x = OptionSetResult{ optionSetError = Nothing, optionSetWarnings = Seq.singleton x }

-- | An option defines some metadata about how a configuration option behaves.
--   It contains a base Crucible type representation, which defines the runtime type
--   that is expected for setting and querying this option at runtime
--
--   The `opt_onset` operation is
--   executed whenever the value of the configuration option is set.  The old
--   value and the new value of the option are passed in.  Arbitrary IO actions
--   may be taken at this point.  If the returned @OptionSetResult@ value indicates
--   an error, the old value of the option is retained.
data OptionStyle tp =
  OptionStyle
  { opt_type :: BaseTypeRepr tp
    -- ^ Crucible type representation of this option

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
    --   style (e.g., its range of expected values), not necessarily information about a specific option.

  , opt_value :: Maybe (ConcreteVal tp)
    -- ^ This gives the value for the option
  }

defaultOpt :: BaseTypeRepr tp -> OptionStyle tp
defaultOpt tp =
  OptionStyle
  { opt_type = tp
  , opt_onset = \_ _ -> return mempty
  , opt_help = empty
  , opt_value = Nothing
  }

set_opt_onset :: (Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult)
                 -> OptionStyle tp
                 -> OptionStyle tp
set_opt_onset f s = s { opt_onset = f }

set_opt_help :: Doc
             -> OptionStyle tp
             -> OptionStyle tp
set_opt_help v s = s { opt_help = v }

set_opt_value :: ConcreteVal tp
              -> OptionStyle tp
              -> OptionStyle tp
set_opt_value v s = s { opt_value = Just v }


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


data ConfigDesc where
  NormalConfigDesc :: ConfigOption tp -> OptionStyle tp -> Maybe Doc -> ConfigDesc
  ListConfigDesc   :: ConfigOption BaseStringType -> ListOption -> ConfigDesc

data ListOption =
  ListOption
  { listopt_values :: Map Text (Doc, IO OptionSetResult)
  , listopt_help   :: Maybe Doc
  , listopt_value  :: Maybe Text
  }

checkListOption :: Text -> ListOption -> Text -> IO OptionSetResult
checkListOption fullname lopt val =
  case Map.lookup val (listopt_values lopt) of
    Nothing -> return $ optErr (text ("Unknown value for option " ++ Text.unpack fullname ++ ": " ++ Text.unpack val))
    Just (_, check) -> check

-- | The most general method for construcing a normal `ConfigDesc`.
mkOpt :: ConfigOption tp     -- ^ Fixes the name and the type of this option
      -> OptionStyle tp      -- ^ Define the style of this option
      -> Maybe Doc           -- ^ Help text
      -> ConfigDesc
mkOpt = NormalConfigDesc

-- | Construct an option using a default style with a given initial value
opt :: Pretty help
    => ConfigOption tp      -- ^ Fixes the name and the type of this option
    -> ConcreteVal tp       -- ^ Initial value for the option
    -> help                 -- ^ An informational message describing this option
    -> ConfigDesc
opt o a help = mkOpt o (defaultOpt (configOptionType o)
                           & set_opt_value a)
                       (Just (pretty help))

-- | Construct an option using a default style with a given initial value.
--   Also provide a validation function to check new values as they are set.
optV :: forall tp help
      . Pretty help
     => ConfigOption tp      -- ^ Fixes the name and the type of this option
     -> ConcreteVal tp       -- ^ Initial value for the option
     -> (ConcreteVal tp -> Maybe help)
         -- ^ Validation function.  Return `Just err` if the value to set
         --   is not valid.
     -> help                -- ^ An informational message describing this option
     -> ConfigDesc
optV o a vf h = mkOpt o (defaultOpt (configOptionType o)
                           & set_opt_onset onset
                           & set_opt_value a)
                        (Just (pretty h))

   where onset :: Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult
         onset _ x = case vf x of
                       Nothing -> return optOK
                       Just z  -> return $ optErr $ pretty z

-- | Construct an option using a default style with no initial value.
optU :: Pretty help
     => ConfigOption tp    -- ^ Fixes the name and the type of this option
     -> help               -- ^ An informational message describing this option
     -> ConfigDesc
optU o h = mkOpt o (defaultOpt (configOptionType o)) (Just (pretty h))

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
   where onset :: Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult
         onset _ x = case vf x of
                       Nothing -> return optOK
                       Just z  -> return $ optErr $ pretty z

-- | Construct a list configuration option.
optList :: Pretty help
        => ConfigOption BaseStringType -- ^ Fixes the name and the type of this option
        -> Map Text (help, IO OptionSetResult)
                             -- ^ Define the names and help descriptions, and an action to
                             --    run when the option is selected
        -> Maybe help        -- ^ An informational message describing this option
        -> Maybe Text        -- ^ Initial value for the option
        -> ConfigDesc
optList lopt vs0 h0 val = ListConfigDesc lopt (ListOption (fmap pp vs0) (fmap pretty h0) val)
 where
 pp (d,v) = (pretty d, v)

-- | Construct a list configuration option from a list of values.
--   The `Show` instance will be used to construct the strings by which
--   the values will be selected.  No help string will be associated to
--   each individual setting.
optListShow :: (Show a, Pretty help)
            => ConfigOption BaseStringType -- ^ Fixes the name and the type of this option
            -> [a]               -- ^ List of possible settings for this option
            -> help              -- ^ An informational message describing this option
            -> ConfigDesc
optListShow o xs h =
  optList o (Map.fromList (map (\x -> (Text.pack (show x), (empty, return mempty))) xs)) (Just (pretty h)) Nothing


-- | Construct a list configuration option from a list of strings.
optListStr :: Pretty help
           => ConfigOption BaseStringType -- ^ Fixes the name and the type of this option
           -> [String]             -- ^ List of possible settings for this option
           -> help                 -- ^ An informational message describing this option
           -> ConfigDesc
optListStr o xs h =
  optList o (Map.fromList (map (\x -> (Text.pack x, (empty, return mempty))) xs)) (Just (pretty h)) Nothing

------------------------------------------------------------------------
-- ConfigState

data ConfigLeaf where
  NormalLeaf :: !(OptionStyle tp) -> Maybe Doc -> ConfigLeaf
  ListLeaf   :: !(ListOption) -> ConfigLeaf

data ConfigTrie where
  ConfigTrie ::
    !(Maybe ConfigLeaf) ->
    !ConfigMap ->
    ConfigTrie

type ConfigMap = Map Text ConfigTrie

freshLeaf :: [Text] -> ConfigLeaf -> ConfigTrie
freshLeaf [] l     = ConfigTrie (Just l) mempty
freshLeaf (a:as) l = ConfigTrie Nothing (Map.singleton a (freshLeaf as l))

adjustConfigTrie :: Functor t => [Text] -> (Maybe ConfigLeaf -> t (Maybe ConfigLeaf)) -> Maybe (ConfigTrie) -> t (Maybe ConfigTrie)
adjustConfigTrie     as f Nothing                   = fmap (freshLeaf as) <$> f Nothing
adjustConfigTrie (a:as) f (Just (ConfigTrie x m)) = Just . ConfigTrie x <$> adjustConfigMap a as f m
adjustConfigTrie     [] f (Just (ConfigTrie x m)) = g <$> f x
  where g Nothing | Map.null m = Nothing
        g x' = Just (ConfigTrie x' m)

adjustConfigMap :: Functor t => Text -> [Text] -> (Maybe ConfigLeaf -> t (Maybe ConfigLeaf)) -> ConfigMap -> t ConfigMap
adjustConfigMap a as f = Map.alterF (adjustConfigTrie as f) a

traverseConfigMap :: Applicative t => [Text] -> ([Text] -> ConfigLeaf -> t ConfigLeaf) -> ConfigMap -> t ConfigMap
traverseConfigMap revPath f = Map.traverseWithKey (\k -> traverseConfigTrie (k:revPath) f)

traverseConfigTrie :: Applicative t => [Text] -> ([Text] -> ConfigLeaf -> t ConfigLeaf) -> ConfigTrie -> t ConfigTrie
traverseConfigTrie revPath f (ConfigTrie x m) =
  ConfigTrie <$> traverse (f (reverse revPath)) x <*> traverseConfigMap revPath f m

traverseSubtree :: Applicative t => [Text] -> ([Text] -> ConfigLeaf -> t ConfigLeaf) -> ConfigMap -> t ConfigMap
traverseSubtree ps0 f = go ps0 []
  where
  go     [] revPath = traverseConfigMap revPath f
  go (p:ps) revPath = Map.alterF (traverse g) p
     where g (ConfigTrie x m) = ConfigTrie x <$> go ps (p:revPath) m


mergeLeaf :: MonadFail m => [Text] -> ConfigLeaf -> ConfigLeaf -> m ConfigLeaf
mergeLeaf path = merge
  where
  showPath = Text.unpack (Text.intercalate "." path)

  merge (ListLeaf x) (ListLeaf y) = ListLeaf <$> mergeListOption x y
  merge _ _ = fail ("Option " ++ showPath ++ " already exists")

  mergeListOption xs ys
   | Set.null xykeys = return $
        ListOption
        { listopt_help = listopt_help xs <> listopt_help ys
        , listopt_values = Map.union (listopt_values xs) (listopt_values ys)
        , listopt_value = listopt_value xs <> listopt_value ys
        }

   | otherwise =
       fail ("List options overlap in " ++ showPath ++ ":\n" ++
                (Text.unpack (Text.intercalate ", " (Set.toList xykeys))))

    where
    xykeys = Set.intersection xkeys ykeys
    xkeys = Map.keysSet (listopt_values xs)
    ykeys = Map.keysSet (listopt_values ys)


insertOption :: MonadFail m => ConfigDesc -> ConfigMap -> m ConfigMap
insertOption desc = adjustConfigMap p ps f
  where
  ((p:|ps),leaf) = case desc of
                       NormalConfigDesc (ConfigOption _ d) x h -> (d, NormalLeaf x h)
                       ListConfigDesc   (ConfigOption _ d) x   -> (d, ListLeaf x)

  f Nothing  = return (Just leaf)
  f (Just x) = Just <$> mergeLeaf (p:ps) x leaf

--deleteOption :: ConfigOption tp -> ConfigMap -> ConfigMap
--deleteOption (ConfigOption _ (p:|ps)) = runIdentity . adjustConfigMap p ps (\_ -> return Nothing)

------------------------------------------------------------------------
-- Config

-- | The main configuration datatype.  It consists of an IORef
--   continaing the actual configuration maps.  It is therefore
--   not safe for concurrent use (FIXME?) unless otherwise synchronized.
newtype Config = Config (IORef ConfigMap)

emptyConfig :: IO Config
emptyConfig = Config <$> newIORef Map.empty

-- | Construct a new configuration from the given configuration
--   descriptions.
initialConfig :: Integer           -- ^ Initial value for the `verbosity` option
              -> [ConfigDesc]      -- ^ Option descriptions to install
              -> IO (Config)
initialConfig initVerbosity ts = do
   cfg <- emptyConfig
   extendConfig (builtInOpts initVerbosity ++ ts) cfg
   return cfg

-- | Extend an existing configuration with new options
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

builtInOpts :: Integer -> [ConfigDesc]
builtInOpts initialVerbosity =
  [ opt verbosity
        (ConcreteInteger initialVerbosity)
        (text "Verbosity of the simulator: higher values produce more detailed informational and debugging output.")
  ]

-- | Given the bare text name of a configuration option,
--   set its value.  This operation is intended to be used
--   to implement operations that access configuration options
--   from inside the Crucible simulator.
--
--   The returned @Doc@ values represent any warnings generated
--   while setting the configuration option.
writeConfigValue
        :: MonadIO m
        => Text            -- ^ The name of the option to set
        -> Config          -- ^ The configuration object to modify
        -> (forall tp. BaseTypeRepr tp -> m (ConcreteVal tp))
           -- ^ An operation to produce the new value for the option.
           --   This operation will be given the run-time type representative
           --   for the expected crucible type of the option.
        -> m [Doc]
writeConfigValue fullName (Config cfg) produceNewVal =
  case splitPath fullName of
    Nothing -> fail "writeConfigValue: empty config option"
    Just (x:|xs) ->
      do m <- liftIO (readIORef cfg)
         (m',res) <- runWriterT (adjustConfigMap x xs f m)
         case optionSetError res of
           Just msg -> fail (show msg)
           Nothing  ->
             do liftIO (writeIORef cfg m')
                return (toList (optionSetWarnings res))
 where
 f Nothing =
     do tell (optErr (text ("Unknown option: " ++ (Text.unpack fullName))))
        return Nothing
 f (Just (NormalLeaf lopt h)) =
     do val <- lift (produceNewVal (opt_type lopt))
        tell =<< liftIO (opt_onset lopt (opt_value lopt) val)
        return (Just (NormalLeaf lopt{ opt_value = Just val } h))
 f (Just (ListLeaf lopt)) =
     do ConcreteString val <- lift (produceNewVal BaseStringRepr)
        tell =<< liftIO (checkListOption fullName lopt val)
        return (Just (ListLeaf lopt{ listopt_value = Just val }))

-- | Given the bare text name of a configuration option, read its current value.
--   This operation is intended to be used
--   to implement operations that access configuration options
--   from inside the Crucible simulator.  This operation will fall the `fail`
--   method of monad `m` if the specified option does not have a current value.
readConfigValue
        :: forall m a
         . MonadIO m
        => Text            -- ^ The name of the option to set
        -> Config          -- ^ The configuration object to modify
        -> (forall tp. Maybe (ConcreteVal tp) -> m a)
                           -- ^ A continuation to run.  The continuation
                           --   is given the run-time type representative of the
                           --   Crucible type of this option, and its current value.
        -> m a
readConfigValue fullName (Config cfg) k = do
  case splitPath fullName of
    Nothing ->
         fail "readConfigValue: empty config option"
    Just (x:|xs) ->
      do m <- liftIO (readIORef cfg)
         getConst (adjustConfigMap x xs f m)

 where
 f Nothing = Const (fail ("Unknown option: " ++ (Text.unpack fullName)))
 f (Just (NormalLeaf lopt _)) = Const (k (opt_value lopt))
 f (Just (ListLeaf lopt))     = Const (k (fmap ConcreteString (listopt_value lopt)))


-- | Read the current value of a configuration option.
getConfigValue' :: ConfigOption tp
                -> Config
                -> IO (ConcreteVal tp)
getConfigValue' o cfg =
  do v <- getConfigValue o cfg
     case v of
       Nothing -> fail ("Option " ++ show o ++ " is not set")
       Just x  -> return x

-- | Read the current value of a configuration option.
getConfigValue :: ConfigOption tp
               -> Config
               -> IO (Maybe (ConcreteVal tp))
getConfigValue o@(ConfigOption tp (x:|xs)) (Config cfg) =
  do m <- liftIO (readIORef cfg)
     getConst (adjustConfigMap x xs f m)
 where
 f Nothing = Const (fail ("Unknown option: " ++ show o))
 f (Just (NormalLeaf lopt _h)) =
     case testEquality tp (opt_type lopt) of
       Nothing   -> Const (fail ("getConfigValue: type mismatch in option " ++ show o ++
                                 "\nExpected " ++ show tp ++ " but found " ++ show (opt_type lopt)))
       Just Refl -> Const (return (opt_value lopt))
 f (Just (ListLeaf lopt)) =
     case testEquality tp BaseStringRepr of
       Nothing   -> Const (fail ("getConfigValue: type mismatch in option " ++ show o ++
                                 "\nExpected " ++ show tp ++ " but found string."))
       Just Refl -> Const (return (fmap ConcreteString (listopt_value lopt)))


-- | Set the value of a configuration option.
setConfigValue :: ConfigOption tp
               -> Config
               -> ConcreteVal tp
               -> IO [Doc]
setConfigValue o@(ConfigOption tp (x:|xs)) (Config cfg) newval =
  do m <- liftIO (readIORef cfg)
     (m',res) <- runWriterT (adjustConfigMap x xs f m)
     case optionSetError res of
       Just msg -> fail (show msg)
       Nothing  ->
         do liftIO (writeIORef cfg m')
            return (toList (optionSetWarnings res))
 where
 f Nothing =
     do tell (optErr (text ("Unknown option: " ++ show o)))
        return Nothing

 f (Just (NormalLeaf lopt h)) =
     case testEquality tp (opt_type lopt) of
       Nothing   ->
         do tell (optErr (text ("setConfigValue: type mismatch in option " ++ show o ++
                            "\nExpected " ++ show tp ++ " but found " ++ show (opt_type lopt))))
            return (Just (NormalLeaf lopt h))
       Just Refl ->
         do tell =<< liftIO (opt_onset lopt (opt_value lopt) newval)
            return (Just (NormalLeaf lopt{ opt_value = Just newval } h))

 f (Just (ListLeaf lopt)) =
     case newval of
       ConcreteString newstr ->
         do tell =<< liftIO (checkListOption (configOptionText o) lopt newstr)
            return (Just (ListLeaf lopt{ listopt_value = Just newstr }))
       _ ->
         do tell (optErr (text ("setConfigValue: type mismatch in option " ++ show o ++
                                "\nExpected " ++ show tp ++ " but found string value.")))
            return (Just (ListLeaf lopt))

data ConfigValue where
  ConfigValue :: ConfigOption tp -> ConcreteVal tp -> ConfigValue

getConfigValues :: Text -> Config -> IO [ConfigValue]
getConfigValues prefix (Config cfg) =
  do m <- readIORef cfg
     let ps = Text.splitOn "." prefix
         f (p:path) (NormalLeaf lopt _) =
            case opt_value lopt of
              Nothing -> mempty
              Just x  -> Const (Seq.singleton (ConfigValue (ConfigOption (opt_type lopt) (p:|path)) x))
         f (p:path) (ListLeaf lopt) =
            case listopt_value lopt of
              Nothing -> mempty
              Just x  -> Const (Seq.singleton (ConfigValue (ConfigOption BaseStringRepr (p:|path)) (ConcreteString x)))
     return $! toList (getConst (traverseSubtree ps f m))

ppSetting :: [Text] -> Maybe (ConcreteVal tp) -> Doc
ppSetting nm v = fill 30 (text (Text.unpack (Text.intercalate "." nm))
                           <> maybe empty (\x -> text " = " <> ppConcrete x) v
                         )

ppOption :: [Text] -> OptionStyle tp -> Maybe Doc -> Doc
ppOption nm lopt help =
   group (ppSetting nm (opt_value lopt) <//> indent 2 (opt_help lopt)) <$$> maybe empty (indent 2) help

ppListOption :: [Text] -> ListOption -> Doc
ppListOption nm lopt =
   group (ppSetting nm (fmap ConcreteString (listopt_value lopt)) </> maybe empty (indent 2) (listopt_help lopt))
     <$$> indent 4 (sep (map listhelp (Map.toList (listopt_values lopt))))

 where
 listhelp (x, (help,_)) = text (Text.unpack x) <//> indent 4 help

ppConfigLeaf :: [Text] -> ConfigLeaf -> Doc
ppConfigLeaf nm (NormalLeaf lopt help) = ppOption nm lopt help
ppConfigLeaf nm (ListLeaf lopt) = ppListOption nm lopt

configHelp :: Text -> Config -> IO [Doc]
configHelp prefix (Config cfg) =
  do m <- readIORef cfg
     let ps = Text.splitOn "." prefix
         f :: [Text] -> ConfigLeaf -> Const (Seq Doc) ConfigLeaf
         f nm leaf = Const (Seq.singleton (ppConfigLeaf nm leaf))
         docs = getConst (traverseSubtree ps f m)
     return $! toList docs
