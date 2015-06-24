module SAWScript.AutoMatch.Util where

import qualified Data.Set as Set
import           Data.Set   (Set)
import qualified Data.Map as Map
import           Data.Map   (Map)

import Data.Maybe
import Data.List
import Control.Monad (mfilter)
import Control.Arrow ( (&&&) )

import SAWScript.AutoMatch.Declaration

-- Some project-specific utilities...

bitSeqType :: Integer -> Type
bitSeqType i = TCon (TC TCSeq) [TCon (TC (TCNum i)) [],TCon (TC TCBit) []]

formatIndexedArg :: Bool -> Name -> Type -> Int -> String
formatIndexedArg paren name typ index =
   lparen ++ show (Arg name typ) ++ rparen ++ " " ++ formatIndex index
   where
      lparen = if paren then "(" else ""
      rparen = if paren then ")" else ""

formatIndex :: Int -> String
formatIndex index = "arg. #" ++ show index ++ ""

corresponds :: String
corresponds = " <-> "

-- Some general utilities...

assertJust :: Maybe a -> a
assertJust = fromMaybe (error "assertJust: Impossible! A call to assertJust was made when it was not, in fact, *just*ified!")

both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)

for :: [a] -> (a -> b) -> [b]
for = flip map

interspersingForM :: Monad m => m b -> [a] -> (a -> m b) -> m [b]
interspersingForM between each = sequence . intersperse between . for each

interspersingForM_ :: Monad m => m b -> [a] -> (a -> m b) -> m ()
interspersingForM_ between each = sequence_ . intersperse between . for each

before :: Monad m => m b -> m a -> m a
before = (>>)

after :: Monad m => m b -> m a -> m a
after mb ma = ma >>= \x -> mb >> return x

frame :: Monad m => m b -> m a -> m a
frame mb = before mb . after mb

fencepostForM :: Monad m => m b -> [a] -> (a -> m b) -> m [b]
fencepostForM between each = frame between . interspersingForM between each

fencepostForM_ :: Monad m => m b -> [a] -> (a -> m b) -> m ()
fencepostForM_ between each = frame between . interspersingForM_ between each

returning :: (Monad m) => a -> m b -> m a
returning a mb = mb >> return a

fastIntersect :: (Ord a) => [a] -> [a] -> [a]
fastIntersect xs ys = Set.toList $ Set.fromList xs `Set.intersection` Set.fromList ys

symmetricDifference :: (Ord a) => Set a -> Set a -> Set a
symmetricDifference s t =
   Set.difference (Set.union s t) (Set.intersection s t)

deleteFromSetMap :: (Ord k, Ord v) => k -> v -> Map k (Set v) -> Map k (Set v)
deleteFromSetMap k v =
  Map.update (mfilter (not . Set.null) . Just . Set.delete v) k

tabulateBy :: (Ord k, Ord v) => (v -> k) -> [v] -> Map k (Set v)
tabulateBy f = Map.fromListWith Set.union . map (f &&& Set.singleton)

sharedKeys :: (Ord k) => Map k v -> Map k v -> [k]
sharedKeys = curry $ Set.toList . uncurry Set.intersection . both Map.keysSet

associateSetWith :: (Ord k) => (k -> v) -> Set k -> Map k v
associateSetWith f = Map.fromAscList . map (id &&& f) . Set.toAscList

yes, no :: [String]
(yes, no) =
   let yes' = ["y","yes","yep","yeah","okay","ok","mkay","ay","positive"]
       no'  = ["n","no","nope","nah","nay","negative"]
   in case fastIntersect yes' no' of
         [] -> (yes', no')
         _  -> error "Internal error: English synonyms for 'yes' and 'no' cannot overlap."
