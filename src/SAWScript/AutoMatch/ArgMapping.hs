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

import Control.Monad
import Data.Maybe

import SAWScript.AutoMatch.Declaration

data ArgMapping =
   ArgMapping { typeBins_ :: Map Type (Set (Name, Int))
              , nameLocs_ :: Map Name (Int, Type) }
              deriving (Show)

typeBins :: ArgMapping -> Map Type (Set (Name, Int))
typeBins = typeBins_

nameLocs :: ArgMapping -> Map Name (Int, Type)
nameLocs = nameLocs_

makeArgMapping :: [Arg] -> ArgMapping
makeArgMapping =
   ArgMapping <$> foldr (uncurry (\k -> Map.insertWith Set.union k . Set.singleton)) Map.empty
                  . map (\(i, a) -> (argType a, (argName a, i)))
                  . zip [0..]
              <*> foldr (uncurry Map.insert) Map.empty
                  . map (\(i, a) -> (argName a, (i, argType a)))
                  . zip [0..]

removeName :: Name -> ArgMapping -> ArgMapping
removeName name mapping =
   fromMaybe mapping $ do
      (nameIndex, nameType) <- Map.lookup name (nameLocs mapping)
      return $ ArgMapping
         (Map.update (mfilter (not . Set.null) . Just . Set.delete (name, nameIndex))
                     nameType
                     (typeBins mapping))
         (Map.delete name (nameLocs mapping))

lookupName :: Name -> ArgMapping -> Maybe (Int, Type)
lookupName name (ArgMapping _ nls) = Map.lookup name nls

lookupType :: Type -> ArgMapping -> Maybe (Set (Name, Int))
lookupType typ (ArgMapping tbs _) = Map.lookup typ tbs

emptyArgMapping :: ArgMapping
emptyArgMapping = makeArgMapping []

isEmptyArgMapping :: ArgMapping -> Bool
isEmptyArgMapping (ArgMapping t n) =
  Map.null t && Map.null n
