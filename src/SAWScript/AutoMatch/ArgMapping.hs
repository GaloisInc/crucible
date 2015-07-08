{-# LANGUAGE CPP #-}

module SAWScript.AutoMatch.ArgMapping
  ( ArgMapping
  , typeBins
  , nameLocs
  , makeArgMapping
  , removeName
  , lookupName
  , lookupType
  , emptyArgMapping
  , isEmptyArgMapping ) where

import qualified Data.Map as Map
import           Data.Map   (Map)
import qualified Data.Set as Set
import           Data.Set   (Set)

import Data.Maybe
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

-- | A bidirectional mapping representing what arguments have what types at what positions in a declaration
--   Abstract, because we preserve the invariant that the maps contained are coherent.
data ArgMapping =
   ArgMapping { typeBins_ :: Map Type (Set (Name, Int))
              , nameLocs_ :: Map Name (Int, Type) }
              deriving (Show)

typeBins :: ArgMapping -> Map Type (Set (Name, Int))
typeBins = typeBins_

nameLocs :: ArgMapping -> Map Name (Int, Type)
nameLocs = nameLocs_

-- | Make an argMapping from a list of Args
makeArgMapping :: [Arg] -> ArgMapping
makeArgMapping =
   ArgMapping <$> foldr (uncurry (\k -> Map.insertWith Set.union k . Set.singleton)) Map.empty
                  . map (\(i, a) -> (argType a, (argName a, i)))
                  . zip [0..]
              <*> foldr (uncurry Map.insert) Map.empty
                  . map (\(i, a) -> (argName a, (i, argType a)))
                  . zip [0..]

-- | Remove a name from an ArgMapping
removeName :: Name -> ArgMapping -> ArgMapping
removeName name mapping =
   fromMaybe mapping $ do
      (nameIndex, nameType) <- Map.lookup name (nameLocs mapping)
      return $ ArgMapping
         (deleteFromSetMap nameType (name, nameIndex) (typeBins mapping))
         (Map.delete name (nameLocs mapping))

-- | Look up a name's type and position in the original declaration
lookupName :: Name -> ArgMapping -> Maybe (Int, Type)
lookupName name (ArgMapping _ nls) = Map.lookup name nls

-- | Look up all the names of a given type and their indices
lookupType :: Type -> ArgMapping -> Maybe (Set (Name, Int))
lookupType typ (ArgMapping tbs _) = Map.lookup typ tbs

-- | The empty ArgMapping
emptyArgMapping :: ArgMapping
emptyArgMapping = makeArgMapping []

-- | Test if an ArgMapping is empty
isEmptyArgMapping :: ArgMapping -> Bool
isEmptyArgMapping (ArgMapping t n) =
  Map.null t && Map.null n
