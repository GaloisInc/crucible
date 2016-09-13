------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Config
-- Description : Declares attributes for simulator configuration settings.
-- Copyright   : (c) Galois, Inc 2015
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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Lang.Crucible.Config
  ( -- * Names of properties
    ConfigOption
  , configOption
  , configOptionName
  , configOptionNameParts

    -- * Defining option styles
  , OptionStyle(..)
  , set_optsty_onset
  , Optionable(..)
  , Bound(..)
  , boolOptSty
  , integralOptSty
  , realOptSty
  , textOptSty
  , stringOptSty
  , realWithRangeOptSty
  , realWithMinOptSty
  , realWithMaxOptSty
  , integralWithRangeOptSty
  , integralWithMinOptSty
  , integralWithMaxOptSty
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
  , setConfigValue
  , readConfigValue
  , writeConfigValue

  , ConfigValue(..)
  , getConfigValues

  , configHelp
  , configHelpString
  , configOptionHelp

  -- * Concrete default options
  , verbosity
  ) where

import           Control.Exception
import           Data.Typeable
import           Data.Maybe (fromMaybe)
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.IORef
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           System.IO.Error ( ioeGetErrorString )
import           Foreign.C.Types (CInt)

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.Crucible.Simulator.RegValue (RegValue)
import qualified Lang.Crucible.Simulator.Utils.Environment as Env
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.MonadVerbosity

#if !MIN_VERSION_base(4,8,0)
import           Data.Functor
#endif

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
--   asdfFrob :: ConfigOption Float
--   asdfFrob = configOption "asdf.frob"
--
--   asdfMaxBound :: ConfigOption Integer
--   asdfMaxBound = configOption "asdf.max_bound"
--
--   asdfWidget :: ConfigOption Widget
--   asdfWidged = configOption "asdf.widget"
-- @
data ConfigOption a where
  ConfigOption :: (Typeable a, Show a)
               => [Text]
               -> ConfigOption a

-- | Construct a `ConfigOption` from a string name.  Idomatic useage is
--   to define a single top-level `ConfigOption` value in the module where the option
--   is defined to consistently fix its name and type for all subsequent uses.
configOption :: (Show a, Typeable a) => String -> ConfigOption a
configOption nm =
   let nms = Text.splitOn "." (Text.pack nm) in
   if any Text.null nms
      then error "config options cannot have an empty name"
      else ConfigOption nms

-- | Get the individual dot-separated segments of an option's name.
configOptionNameParts :: ConfigOption a -> [Text]
configOptionNameParts (ConfigOption xs) = xs

-- | Reconstruct the original string name of this option.
configOptionName :: ConfigOption a -> String
configOptionName (ConfigOption xs) = Text.unpack $ Text.intercalate "." $ xs

------------------------------------------------------------------------
-- OptionDefinition

-- | An option style defines some metadata about how a configuration option behaves.
--   It contains a Crucible type representation, which defines the runtime type
--   that is expected for setting and querying this option at runtime, as well as
--   a pair of operations for converting the Haskell option value to and from
--   Crucible runtime values of the given type.
--
--   The `optsty_onset` operation is
--   executed whenever the value of the configuration option is set.  The old
--   value and the new value of the option are passed in.  Arbitrary IO actions
--   may be taken at this point.  If \"onset\" returns `Nothing`, then setting
--   the configuration option will succeed.  If `Just` is returned, then the
--   configuration option will /NOT/ be set, and the returned Doc will instead be
--   rendered to the user as an error message instead.
data OptionStyle m opt =
  forall tp. OptionStyle
  { optsty_tyr       :: TypeRepr tp
        -- ^ Crucible type representation of this option

  , optsty_onset :: Maybe opt -> opt -> m (Maybe Doc)
    -- ^ An operation for validating new option values.
    -- The first argument is the current value of the option (if any).
    -- The second argument is the new value.
    -- If the validation fails, the operation should return a doc
    -- describing why validation failed.
    -- If the validation suceeds, then the operation should return @Nothing@.

  , optsty_extract   :: forall sym . IsExprBuilder sym => sym -> opt -> IO (RegValue sym tp)
        -- ^ An operation for turning the Haskell option value into a crucible value.

  , optsty_insert    :: forall sym. IsExprBuilder sym => sym -> RegValue sym tp -> IO opt
        -- ^ An operation for turning a Crucible value into a Haskell value for the option.

  , optsty_help      :: Doc
        -- ^ Documentation for the option to be displayed in the event a user asks for information
        --   about this option.  This message should contain information relevant to all options in this
        --   style (e.g., its range of expected values), not necessarily information about a specific option.

  , optsty_default   :: Maybe opt
        -- ^ If set, this gives a default value for the option to use when no explict value has been given.
  }

(&) :: a -> (a -> b) -> b
(&) x f = f x

set_optsty_onset :: (Maybe opt -> opt -> m (Maybe Doc))
                 -> OptionStyle m opt
                 -> OptionStyle m opt
set_optsty_onset f s = s { optsty_onset = f }

set_optsty_help :: Doc
                 -> OptionStyle m opt
                 -> OptionStyle m opt
set_optsty_help v s = s { optsty_help= v }


-- | This class associates basic option styles to some common Haskell types
class Optionable a where
  optStyle :: forall m . Monad m => OptionStyle m a

instance Optionable Bool where
  optStyle = boolOptSty

instance Optionable Integer where
  optStyle = integralOptSty

instance Optionable CInt where
  optStyle = integralOptSty

instance Optionable Int where
  optStyle = integralOptSty

instance Optionable Text where
  optStyle = textOptSty

instance Optionable String where
  optStyle = stringOptSty


-- | An inclusive or exclusive bound.
data Bound r = Exclusive r
             | Inclusive r
             | Unbounded

-- | Standard option style for boolean-valued configuration options
boolOptSty :: Monad m => OptionStyle m Bool
boolOptSty = OptionStyle BoolRepr
                          (\_ _ -> return Nothing)
                          (\sym b -> return $ if b then truePred sym else falsePred sym)
                          (\_ x -> maybe (fail "expected constant boolean value ") return (asConstantPred x))
                          (text "Boolean")
                          Nothing

-- | Standard option style for real-valued configuration options
realOptSty :: (Monad m, Show a, Typeable a, Fractional a, Real a) => OptionStyle m a
realOptSty = OptionStyle RealValRepr
                  (\_ _ -> return Nothing)
                  (\sym a -> realLit sym $ toRational a)
                  (\_ a -> maybe (fail "expected constant rational value") (return . fromRational) (asRational a))
                  (text "ℝ")
                  Nothing


-- | Standard option style for integral-valued configuration options
integralOptSty :: (Monad m, Show a, Typeable a, Integral a) => OptionStyle m a
integralOptSty = OptionStyle IntegerRepr
                  (\_ _ -> return Nothing)
                  (\sym a -> intLit sym (fromIntegral a))
                  (\_ x -> maybe (fail "expected constant integral value") (return . fromInteger) (asInteger x))
                  (text "ℤ")
                  Nothing

-- | Standard option style for text-valued configuration options
textOptSty :: Monad m => OptionStyle m Text
textOptSty = OptionStyle StringRepr
                  (\_ _ -> return Nothing)
                  (\_ a -> return a)
                  (\_ a -> return a)
                  (text "String")
                  Nothing


-- | Standard option style for string-valued configuration options
stringOptSty :: Monad m => OptionStyle m String
stringOptSty = OptionStyle StringRepr
                  (\_ _ -> return Nothing)
                  (\_ a -> return $ Text.pack a)
                  (\_ a -> return $ Text.unpack a)
                  (text "String")
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


type IsRealOpt a = (Show a, Typeable a, Fractional a, Real a)

-- | Option style for real-valued options with upper and lower bounds
realWithRangeOptSty :: forall m a
                     . (Monad m, IsRealOpt a)
                    => Bound a -> Bound a -> OptionStyle m a
realWithRangeOptSty lo hi = realOptSty & set_optsty_onset vf
                                       & set_optsty_help help
  where help = text "ℝ ∈" <+> docInterval lo hi
        vf :: Monad m => Maybe a -> a -> m (Maybe Doc)
        vf _ x
          | checkBound lo hi x = return $ Nothing
          | otherwise          = return $ Just $
                                    text (show x) <+> text "out of range, expected real value in "
                                                  <+> docInterval lo hi

-- | Option style for real-valued options with a lower bound
realWithMinOptSty :: (Monad m, IsRealOpt a)
                  => Bound a -> OptionStyle m a
realWithMinOptSty lo = realWithRangeOptSty lo Unbounded

-- | Option style for real-valued options with an upper bound
realWithMaxOptSty :: (Monad m, IsRealOpt a) => Bound a -> OptionStyle m a
realWithMaxOptSty hi = realWithRangeOptSty Unbounded hi

type IsIntegralOpt a = (Show a, Typeable a, Integral a)

-- | Option style for integer-valued options with upper and lower bounds
integralWithRangeOptSty :: forall m a
                         . (Monad m, IsIntegralOpt a)
                        => Bound a -> Bound a -> OptionStyle m a
integralWithRangeOptSty lo hi = integralOptSty & set_optsty_onset vf
                                               & set_optsty_help help
  where help = text "ℤ ∈" <+> docInterval lo hi
        vf :: Monad m => Maybe a -> a -> m (Maybe Doc)
        vf _ x
          | checkBound lo hi x = return $ Nothing
          | otherwise          = return $ Just $
                                    text (show x) <+> text "out of range, expected integer value in "
                                                  <+> docInterval lo hi

-- | Option style for integer-valued options with a lower bound
integralWithMinOptSty :: (Monad m, IsIntegralOpt a) => Bound a -> OptionStyle m a
integralWithMinOptSty lo = integralWithRangeOptSty lo Unbounded

-- | Option style for integer-valued options with an upper bound
integralWithMaxOptSty :: (Monad m, IsIntegralOpt a) => Bound a -> OptionStyle m a
integralWithMaxOptSty hi = integralWithRangeOptSty Unbounded hi

-- | A configuration style for options that must be one of a fixed set of text values
enumOptSty :: Monad m => Set Text -> OptionStyle m Text
enumOptSty elts = textOptSty & set_optsty_onset vf
                             & set_optsty_help help
  where help = group (text "one of: " <+> align (sep $ map (dquotes . text . Text.unpack) $ Set.toList elts))
        vf :: Monad m => Maybe Text -> Text -> m (Maybe Doc)
        vf _ x
         | x `Set.member` elts = return Nothing
         | otherwise = return $ Just $ text "invalid setting" <+> text (show x) <+>
                                       text ", expected one of:"
                                       <+> align (sep (map (text . Text.unpack) $ Set.toList elts))

-- | A configuration style for options that are expected to be paths to an executable
--   image.  Configuration options with this style generate a warning message if set to a
--   value that cannot be resolved to an absolute path to an executable file in the
--   current OS environment.
executablePathOptSty :: MonadVerbosity m => OptionStyle m FilePath
executablePathOptSty = stringOptSty & set_optsty_onset vf
                                    & set_optsty_help help
  where help = text "<path>"
        vf :: MonadVerbosity m => Maybe FilePath -> FilePath -> m (Maybe Doc)
        vf _ x = do me <- liftIO $ try (Env.findExecutable x)
                    case me of
                       Left e  -> showWarning (ioeGetErrorString e)
                       Right{} -> return ()
                    return Nothing


------------------------------------------------------------------------
-- ConfigDesc

-- | A `ConfigDesc` is the runtime datastructure that describes a configuration
--   option before it is inserted into a `Config` object.
data ConfigDesc m where
  ConfigTree :: Text -> [ConfigDesc m] -> ConfigDesc m
  ConfigList :: (Show opt, Ord opt, Typeable opt)
             => Text
             -> [(Text,Doc,opt)]
             -> Doc
             -> ConfigDesc m
  ConfigLeaf :: (Show opt, Typeable opt)
             => Text
             -> OptionStyle m opt
             -> Maybe opt
             -> Doc
             -> ConfigDesc m

-- | The most general method for construcing a `ConfigDesc`.
mkOpt :: Pretty help
      => ConfigOption a     -- ^ Fixes the name and the type of this option
      -> Maybe a            -- ^ Give an optional initial value for the option
      -> OptionStyle m a    -- ^ Define the style of this option
      -> help               -- ^ An informational message describing this option
      -> ConfigDesc m
mkOpt (ConfigOption [])  _      _    _ = error "impossible: empty config option name"
mkOpt (ConfigOption [x]) a    sty help = ConfigLeaf x sty a (pretty help)
mkOpt (ConfigOption (x:xs)) a sty help = ConfigTree x [mkOpt (ConfigOption xs) a sty help]

-- | Construct an option using a default style with a given initial value
opt :: (Monad m, Optionable a, Pretty help)
    => ConfigOption a       -- ^ Fixes the name and the type of this option
    -> a                    -- ^ Initial value for the option
    -> help                 -- ^ An informational message describing this option
    -> ConfigDesc m
opt o a = mkOpt o (Just a) optStyle

-- | Construct an option using a default style with a given initial value.
--   Also provide a validation function to check new values as they are set.
optV :: forall a help m
      . (Monad m, Optionable a, Pretty help)
     => ConfigOption a      -- ^ Fixes the name and the type of this option
     -> a                   -- ^ Initial value for the option
     -> (a -> m (Maybe help))
         -- ^ Validation function.  Return `Just err` if the value to set
         --   is not valid.
     -> help                -- ^ An informational message describing this option
     -> ConfigDesc m
optV o a vf = mkOpt o (Just a) (optStyle & set_optsty_onset onset)
   where onset :: Monad m => Maybe a -> a -> m (Maybe Doc)
         onset _ x = liftM (fmap pretty) (vf x)

-- | Construct an option using a default style with no initial value.
optU :: (Monad m, Optionable a, Pretty help)
     => ConfigOption a      -- ^ Fixes the name and the type of this option
     -> help                -- ^ An informational message describing this option
     -> ConfigDesc m
optU o = mkOpt o Nothing optStyle

-- | Construct an option using a default style with no initial value.
--   Also provide a validation function to check new values as they are set.
optUV :: forall a help m
       . (Monad m, Optionable a, Pretty help)
      => ConfigOption a      -- ^ Fixes the name and the type of this option
      -> (a -> m (Maybe help))
                             -- ^ Validation function.  Return `Just err` if the value to set
                             --   is not valid.
      -> help                -- ^ An informational message describing this option
      -> ConfigDesc m
optUV o vf = mkOpt o Nothing (optStyle & set_optsty_onset onset)
   where onset :: Maybe a -> a -> m (Maybe Doc)
         onset _ x = liftM (fmap pretty) (vf x)

-- | Construct a list configuration option.
optList :: (Show a, Ord a, Typeable a, Pretty help)
        => ConfigOption a    -- ^ Fixes the name and the type of this option
        -> [(Text,help,a)]   -- ^ Define the names, help descriptions and values
                             --   for the possible settings of this option
        -> help              -- ^ An informational message describing this option
        -> ConfigDesc m
optList (ConfigOption [])      _    _ = error "impossible: empty config option name"
optList (ConfigOption [n])    xs help = ConfigList n xs' (pretty help)
    where xs' = map f xs
          f (nm,h,a) = (nm, pretty h, a)
optList (ConfigOption (n:ns)) xs help = ConfigTree n [optList (ConfigOption ns) xs help]


-- | Construct a list configuration option from a list of values.
--   The `Show` instance will be used to construct the strings by which
--   the values will be selected.  No help string will be associated to
--   each individual setting.
optListShow :: (Show a, Ord a, Typeable a, Pretty help)
            => ConfigOption a    -- ^ Fixes the name and the type of this option
            -> [a]               -- ^ List of possible settings for this option
            -> help              -- ^ An informational message describing this option
            -> ConfigDesc m
optListShow o xs h = optList o (map (\x -> (Text.pack $ show x, empty, x)) xs) (pretty h)

-- | Construct a list configuration option from a list of strings.
optListStr :: Pretty help
           => ConfigOption String  -- ^ Fixes the name and the type of this option
           -> [String]             -- ^ List of possible settings for this option
           -> help                 -- ^ An informational message describing this option
           -> ConfigDesc m
optListStr o xs h = optList o (map (\x -> (Text.pack x, empty, x)) xs) (pretty h)


------------------------------------------------------------------------
-- ConfigState

-- | Runtime state of a configuration.
type ConfigState m = Map Text (ConfigStateNode m)

data ConfigStateNode m where
  ConfigStateNode :: ConfigState m
                  -> ConfigStateNode m
  ConfigStateList :: (Show opt, Ord opt, Typeable opt)
                  => opt
                  -> Map Text opt
                  -> Map opt Text
                  -> Map Text Doc
                  -> Doc
                  -> ConfigStateNode m
  ConfigStateLeaf :: (Show opt, Typeable opt)
                  => OptionStyle m opt
                  -> Maybe opt
                  -> Doc
                  -> ConfigStateNode m

------------------------------------------------------------------------
-- Config

-- | The main configuration datatype.  It consists of an IORef
--   continaing the actual configuration maps.  It is therefore
--   not safe for concurrent use (FIXME?) unless otherwise synchronized.
newtype Config m = Config (IORef (ConfigState m))

emptyConfig :: IO (Config m)
emptyConfig = Config <$> newIORef Map.empty

-- | Construct a new configuration from the given configuration
--   descriptions.
initialConfig :: Monad m
              => Int             -- ^ Initial value for the `verbosity` option
              -> [ConfigDesc m]    -- ^ Option descriptions to install
              -> IO (Config m)
initialConfig initVerbosity ts = do
   cfg <- emptyConfig
   extendConfig (builtInOpts initVerbosity ++ ts) cfg
   return cfg

-- | Extend an existing configuration with new options
extendConfig :: [ConfigDesc m]
             -> Config m
             -> IO ()
extendConfig ts (Config cfg) =
  (readIORef cfg >>= \m -> foldM (flip insertConfig) m ts) >>= writeIORef cfg

-- | Main workhorse of the configuration setup algorithms.
--   Given a single new configuration description, insert it into
--   the given configuration state.
insertConfig :: ConfigDesc m -> ConfigState m -> IO (ConfigState m)
insertConfig = go
 where ins1 m (txt,_,x) =
          case Map.lookup txt m of
             Just _ -> fail $ unwords ["option value alread exists:", show x]
             Nothing -> return $ Map.insert txt x m
       ins2 m (txt,_,x) =
          case Map.lookup x m of
             Just _ -> fail $ unwords ["option value alreay exists:", show x]
             Nothing -> return $ Map.insert x txt m

       insdoc m (txt,help,_) = return $ Map.insert txt help m

       go :: ConfigDesc m -> ConfigState m -> IO (ConfigState m)
       go (ConfigTree _ []) m = return m
       go (ConfigTree nm ts) m = do
--              putStrLn $ unwords ["inserting option", Text.unpack nm]
              m'<- case Map.lookup nm m of
                      Nothing -> return Map.empty
                      Just (ConfigStateNode m') -> return m'
                      _ -> fail "insertConfig: incompatible option specifications"
              m'' <- foldM (flip go) m' ts
              return $ Map.insert nm (ConfigStateNode m'') m

       go (ConfigList _ [] _) m = return m
       go (ConfigList nm ls@((_, _, init_a :: a):_) help) m = do
--              putStrLn $ unwords ["inserting option", Text.unpack nm]
              r <- case Map.lookup nm m of
                       Nothing -> do
                          m1 <- foldM ins1 Map.empty ls
                          m2 <- foldM ins2 Map.empty ls
                          mdoc <- foldM insdoc Map.empty ls
                          return $ ConfigStateList init_a m1 m2 mdoc help

                       Just (ConfigStateList (v :: a') m1 m2 mdoc help')
                          | Just (Refl :: a :~: a') <- eqT -> do
                            m1' <- foldM ins1 m1 ls
                            m2' <- foldM ins2 m2 ls
                            mdoc' <- foldM insdoc mdoc ls
                            return $ ConfigStateList v m1' m2' mdoc' help'

                       _ -> fail "insertConfig: incompatible option specifications"
              return $ Map.insert nm r m

       go (ConfigLeaf nm sty st help) m = do
--              putStrLn $ unwords ["inserting option", Text.unpack nm]
              r <- case Map.lookup nm m of
                       Nothing -> return (ConfigStateLeaf sty st help)
                       _ -> fail "insertConfig: incompatible option specifications"
              return $ Map.insert nm r m

-- | Datatype wrapper to capture the current status of a configuration option.
data ConfigValue m where
  ConfigValue :: (Show opt, Typeable opt)
              => ConfigOption opt
              -> OptionStyle m opt
              -> opt
              -> ConfigValue m

-- | Get all the configuration values relevant to a given configuration option name.
--   If the name specifies an individual option, just the value of that option will
--   be returned.  If the name specifies a subtree, the values of all immediate
--   leaf options in the tree will be returned, but not any leaf values in decendent trees.
--
--   The name argument supports a basic form of name globbing.  If the name looks like
--   \"some.tree.\*\" then all leaf options appearing in any subtree of \"some.tree\" will
--   be returned in addition to just the immediate leaf options.  If the name looks like
--   \"some.*.asdf\" then all leaf options named \"asdf\" in an immediate subtree of \"some\"
--   will be returned.  More general forms of globbing are not supported.
getConfigValues
   :: forall m
    . Monad m
   => Text
   -> Config m
   -> IO [ConfigValue m]
getConfigValues fullName (Config cfg) = readIORef cfg >>= go fullParts []
  where fullParts
           | fullName == "" = []
           | otherwise      = Text.splitOn "." fullName

        go []     nms m   = getValues False nms m
        go ["*"]  nms m   = getValues True  nms m
        go ("*":xs) nms m = concat <$> sequence
                              [ go xs (nms++[nm]) m' | ( nm, ConfigStateNode m' ) <- Map.toList m ]
        go (x:xs) nms m   = case Map.lookup x m of
                              Just (ConfigStateNode m') -> go xs (nms++[x]) m'
                              _ -> fail $ unwords ["Configuration subtree not found:", Text.unpack fullName]

        getValues b nms m = concat <$> mapM (getValue b nms) (Map.toList m)

        getValue :: Bool -> [Text] -> (Text, ConfigStateNode m) -> IO [ConfigValue m]
        getValue False   _ (  _, ConfigStateNode _) = return []
        getValue True  nms ( nm, ConfigStateNode m) = getValues True (nms++[nm]) m
        getValue _       _ (  _, ConfigStateLeaf _ Nothing _) = return []
        getValue _     nms ( nm, ConfigStateLeaf sty (Just o) _) =
              return [ConfigValue (ConfigOption (nms ++ [nm])) sty o]
        getValue _ nms (nm, ConfigStateList o inmap outmap docmap help) =
              let sty = dualMapsOptionStyle inmap outmap docmap help in
              return [ConfigValue (ConfigOption (nms ++ [nm])) sty o]

dualMapsOptionStyle
   :: forall m opt
    . (Monad m, Show opt, Ord opt, Typeable opt)
   => Map Text opt
   -> Map opt Text
   -> Map Text Doc
   -> Doc
   -> OptionStyle m opt
dualMapsOptionStyle inmap outmap docmap help =
      OptionStyle StringRepr vf extract insert help' Nothing
  where vf :: Monad m => Maybe opt -> opt -> m (Maybe Doc)
        vf _ x
         | Just _ <- Map.lookup x outmap = return Nothing
         | otherwise = return $ Just $ text "unrecognized option value" <+> text (show x)
                                       <+> text "expected one of"
                                       <+> sep (map (text . Text.unpack . fst) (Map.toList inmap))

        help' = help <$$> indent 2 (sep (map listhelp (Map.toList docmap)))
        listhelp (x, h) = text (Text.unpack x) <//> indent 4 h

        insert :: forall sym. sym -> Text -> IO opt
        insert _sym t
         | Just v <- Map.lookup t inmap = return v
         | otherwise = fail $ unwords ["illegal option value:", show t]

        extract :: forall sym. sym -> opt -> IO Text
        extract _sym v
         | Just t <- Map.lookup v outmap = return t
         | otherwise = fail $ unwords ["unrecognized option value:", show v]


-- | This single operation traverses a configuration state to get and update the value
--   of an option.   Different instantiations of this basic traversal operation
--   give the different query/set operations below.
adjustConfiguration
   :: (Monad m, Monad m')
   => String
   -> Text
   -> [Text]
   -> ConfigState m'
   -> (forall b opt. (Show opt, Typeable opt)
           => OptionStyle m' opt
           -> Maybe opt
           -> Doc
           -> (Maybe opt -> m b)
           -> m b
           -> m (a,b))
   -> m (a, Maybe (ConfigState m'))
adjustConfiguration fullName x xs m cont = do
  (a,z) <-
    case Map.lookup x m of
      Just (ConfigStateNode m')
         | x':xs' <- xs -> do
               (a,z) <- adjustConfiguration fullName x' xs' m' cont
               return (a, fmap ConfigStateNode z)

      Just (ConfigStateList v inmap outmap docmap help)
         | [] <- xs ->
             let sty = (dualMapsOptionStyle inmap outmap docmap help) in
             cont sty
                  (Just v)
                  help
                  (\newv -> case newv of
                               Nothing -> fail $ unwords ["option", fullName, "must have a value"]
                               Just v' -> return $ Just $ ConfigStateList v' inmap outmap docmap help)
                  (return Nothing)

      Just (ConfigStateLeaf sty v help)
         | [] <- xs ->
             cont sty
                  v
                  help
                  (\newv -> return $ Just $ ConfigStateLeaf sty newv help)
                  (return Nothing)

      _ -> fail $ unwords $ ["config option not found:", fullName]

  return (a, fmap (\q -> Map.insert x q m) z)

-- | Given the bare text name of a configuration option,
--   set its value.  This operation is intended to be used
--   to implement operations that access configuration options
--   from inside the Crucible simulator.
writeConfigValue
        :: forall m sym
         . (MonadVerbosity m, IsExprBuilder sym)
        => sym             -- ^ The expression builder
        -> Text            -- ^ The name of the option to set
        -> Config m        -- ^ The configuration object to modify
        -> (forall tp. TypeRepr tp -> m (RegValue sym tp))
           -- ^ An operation to produce the new value for the option.
           --   This operation will be given the run-time type representative
           --   for the expected crucible type of the option.
        -> m ()
writeConfigValue sym fullName (Config cfg) produceNewVal = do
  let nms = Text.splitOn "." fullName
  case nms of
    [] -> fail "writeConfigValue: empty config option"
    (x:xs) -> do
      st <- liftIO (readIORef cfg)
      ((),st') <- adjustConfiguration (Text.unpack fullName) x xs st
                    (\(OptionStyle tpr onset _ insert _ _) mold _help adjust _noadjust -> do
                           newval <- produceNewVal tpr
                           v <- liftIO (insert sym newval)
                           valid <- onset mold v
                           case valid of
                             Just msg -> fail $ show msg
                             Nothing  -> do
                                 b <- adjust (Just v)
                                 return ((),b)
                    )
      liftIO $ writeIORef cfg (fromMaybe st st')

-- | Given the bare text name of a configuration option, read its current value.
--   This operation is intended to be used
--   to implement operations that access configuration options
--   from inside the Crucible simulator.  This operation will fall the `fail`
--   method of monad `m` if the specified option does not have a current value.
readConfigValue
        :: forall m' sym a
         . (Monad m', IsExprBuilder sym)
        => sym             -- ^ The expression builder
        -> Text            -- ^ The name of the option to set
        -> Config m'       -- ^ The configuration object to modify
        -> (forall tp. TypeRepr tp -> RegValue sym tp -> IO a)
                           -- ^ A continuation to run.  The continuation
                           --   is given the run-time type representative of the
                           --   Crucible type of this option, and its current value.
        -> IO a
readConfigValue sym fullName (Config cfg) k = do
  let nms = Text.splitOn "." fullName
  case nms of
    [] -> fail "readConfigValue: empty config option"
    (x:xs) -> do
      st <- readIORef cfg
      (a,_) <- adjustConfiguration (Text.unpack fullName) x xs st
               (\(OptionStyle tpr _ extract _ _ defaultVal) mo _help _adjust noadjust -> do
                  a <-
                    case maybe defaultVal Just mo of
                      Just o ->  do
                        k tpr =<< extract sym o
                      Nothing ->
                        fail $ unwords ["config option not set:", Text.unpack fullName]
                  b <- noadjust
                  return (a,b))
      return a

-- | Read the current value of a configuration option.  This operation
--   with call `fail` in the monad `m` if the specified option does not have a current value.
getConfigValue :: forall m opt
                . Monad m
               => ConfigOption opt
               -> Config m
               -> IO opt
getConfigValue (ConfigOption []) _ = fail "getConfigValue: empty config option"
getConfigValue cl@(ConfigOption (x:xs)) (Config cfg) = do
  st <- readIORef cfg
  (a,_) <- adjustConfiguration
              (configOptionName cl) x xs st
              (\sty (m :: Maybe opt') _help _adjust noadjust -> do
                 case eqT of
                   Just (Refl :: opt :~: opt') -> do
                     case maybe (optsty_default sty) Just m of
                       Nothing -> fail $ unwords ["config option not set:", configOptionName cl]
                       Just o -> do
                          b <- noadjust
                          return (o, b)
                   _ -> fail $ unwords ["type mismatch when looking up option:", configOptionName cl]
              )
  return a

-- | Set the value of a configuration option.
setConfigValue :: forall m opt
                . MonadIO m
               => ConfigOption opt
               -> Config m
               -> opt
               -> m ()
setConfigValue (ConfigOption []) _ _ = fail "setConfigValue: empty config option"
setConfigValue cl@(ConfigOption (x:xs)) (Config cfg) newoptval = do
  st <- liftIO (readIORef cfg)
  ((),st') <- adjustConfiguration
              (configOptionName cl) x xs st
              (\sty (mold :: Maybe opt') _help adjust _noadjust -> do
                 case eqT of
                   Just (Refl :: opt :~: opt') -> do
                      valid <- optsty_onset sty mold newoptval
                      case valid of
                         Just msg -> fail $ show msg
                         Nothing -> do
                           b <- adjust (Just newoptval)
                           return ((), b)
                   _ -> fail $ unwords ["type mistmatch when setting option:", configOptionName cl]
              )
  liftIO (writeIORef cfg (fromMaybe st st'))

-- | Given the name of a configuration option, get a document describing the option
--   and its legal values.
configOptionHelp :: Monad m => Text -> Config m -> IO Doc
configOptionHelp fullName (Config cfg) = do
  let nms = Text.splitOn "." fullName
  case nms of
    [] -> fail "configOptionHelp: empty config option"
    (x:xs) -> do
      st <- liftIO (readIORef cfg)
      (doc,_) <- adjustConfiguration (Text.unpack fullName) x xs st
                    (\sty mold help _adjust noadjust -> do
                            b <- noadjust
                            let doc = group
                                      (  (fill 30 (text (Text.unpack fullName) <>
                                               maybe empty (\v -> text " = " <> text (show v)) mold))
                                         <//>
                                         indent 2 (optsty_help sty)
                                         <$$>
                                         indent 2 help
                                      )
                            return (doc,b)
                    )
      return doc


-- | Render the help document returned by `configHelp` as as string
configHelpString :: Config m -> IO String
configHelpString cfg = do
   doc <- configHelp cfg
   return $ displayS (renderPretty 0.8 80 doc) []

-- | Render a help document describing all the options installed in the given configuration.
configHelp :: Config m -> IO Doc
configHelp (Config cfg) = do
   m <- readIORef cfg
   return $ configStateHelp [] m

configStateHelp :: [Text] -> ConfigState m -> Doc
configStateHelp prefix m = vcat $ map node $ Map.toList m
  where nmdoc :: Show a => Text -> Maybe a -> Doc
        nmdoc nm v = fill 30 (text (Text.unpack (Text.intercalate "." (prefix ++ [nm])))
                              <> maybe empty (\x -> text " = " <> text (show x)) v
                             )

        node (nm, ConfigStateNode m') = configStateHelp (prefix ++ [nm]) m'
        node (nm, ConfigStateLeaf sty v help) =
                   group (nmdoc nm v <//> indent 2 (optsty_help sty)) <$$> indent 2 help
        node (nm, ConfigStateList v _ _ docmap help) =
                   group (nmdoc nm (Just v) </> indent 2 help) <$$> indent 4 (sep (map listhelp (Map.toList docmap)))

        listhelp (x, help) = text (Text.unpack x) <//> indent 4 help

-- | Verbosity of the simulator.  This option controls how much
--   informational and debugging output is generated.
--   0 yields low information output; 5 is extremely chatty.
verbosity :: ConfigOption Int
verbosity = configOption "verbosity"

builtInOpts :: Monad m => Int -> [ConfigDesc m]
builtInOpts initialVerbosity =
  [ mkOpt        verbosity        (Just initialVerbosity)    integralOptSty{ optsty_default = Just 0 }
    (text "Verbosity of the simulator: higher values produce more detailed informational and debugging output.")
  ]
