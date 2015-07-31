{-# LANGUAGE CPP #-}

module SAWScript.AutoMatch.Util where

import qualified Data.Set as Set
import           Data.Set   (Set)
import qualified Data.Map as Map
import           Data.Map   (Map)

import Data.Maybe
import Data.List
import Control.Monad (mfilter)
import Control.Arrow ( (&&&) )

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import SAWScript.AutoMatch.Declaration

-- Some project-specific utilities...

-- | Cryptol type for a bit sequence of a given length
bitSeqType :: Integer -> Type
bitSeqType i = TCon (TC TCSeq) [TCon (TC (TCNum i)) [],TCon (TC TCBit) []]

-- | How to print out a single argument of a given type which occurs at a particular index
formatIndexedArg :: Bool -> Name -> Type -> Int -> String
formatIndexedArg paren name typ index =
   lparen ++ show (Arg name typ) ++ rparen ++ " " ++ formatIndex index
   where
      lparen = if paren then "(" else ""
      rparen = if paren then ")" else ""

-- | How to print out an index for an argument
formatIndex :: Int -> String
formatIndex index = "arg. #" ++ show index ++ ""

-- | The symbol we use for saying things correspond to each other between modules
corresponds :: String
corresponds = " <-> "

-- Some general utilities...

-- | Like fromJust, but with an error message which makes you feel worse about yourself
assertJust :: Maybe a -> a
assertJust = fromMaybe (error "assertJust: Impossible! A call to assertJust was made when it was not, in fact, *just*ified!")

-- | Apply a function to both sides of a homogeneous pair
both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)

-- | Like forM, but without the M @(flip map)@
for :: [a] -> (a -> b) -> [b]
for = flip map

-- | Intersperse the given monadic action between each element of the list processed
interspersingForM :: Monad m => m b -> [a] -> (a -> m b) -> m [b]
interspersingForM between each = sequence . intersperse between . for each

-- | Like interspersingForM, but throws away result
interspersingForM_ :: Monad m => m b -> [a] -> (a -> m b) -> m ()
interspersingForM_ between each = sequence_ . intersperse between . for each

-- | Non-operator version of @(>>)@
before :: Monad m => m b -> m a -> m a
before = (>>)

-- | Execute second argument first, then first argument, returning second argument's result
after :: Monad m => m b -> m a -> m a
after mb ma = ma >>= \x -> mb >> return x

-- | Do the first action before and after the second action, returning the second action's result
frame :: Monad m => m b -> m a -> m a
frame mb = before mb . after mb

-- | Like interspersingForM, but also does the interspersed action before and after
fencepostForM :: Monad m => m b -> [a] -> (a -> m b) -> m [b]
fencepostForM between each = frame between . interspersingForM between each

-- | Like fencepostForM, but throws away the result
fencepostForM_ :: Monad m => m b -> [a] -> (a -> m b) -> m ()
fencepostForM_ between each = frame between . interspersingForM_ between each

-- | Do the monadic action, returning a particular other value
returning :: (Monad m) => a -> m b -> m a
returning a mb = mb >> return a

-- | Use a Set to intersect two lists quickly
fastIntersect :: (Ord a) => [a] -> [a] -> [a]
fastIntersect xs ys = Set.toList $ Set.fromList xs `Set.intersection` Set.fromList ys

-- | Calculate the symmetric difference between two sets
symmetricDifference :: (Ord a) => Set a -> Set a -> Set a
symmetricDifference s t =
   Set.difference (Set.union s t) (Set.intersection s t)

-- | Delete a value from a map of sets, pruning the key if it was the last item in that set
deleteFromSetMap :: (Ord k, Ord v) => k -> v -> Map k (Set v) -> Map k (Set v)
deleteFromSetMap k v =
  Map.update (mfilter (not . Set.null) . Just . Set.delete v) k

-- | Given a mapping from values to keys, transform a list of values
--   into a mapping from keys to sets of values mapped to that key
tabulateBy :: (Ord k, Ord v) => (v -> k) -> [v] -> Map k (Set v)
tabulateBy f = Map.fromListWith Set.union . map (f &&& Set.singleton)

-- | Calculate the list of keys shared between two maps
sharedKeys :: (Ord k) => Map k v -> Map k v -> [k]
sharedKeys = curry $ Set.toList . uncurry Set.intersection . both Map.keysSet

-- | Given a Set and a function from its elements to some other thing, turn it into a map
--   In other words: calculate the image of the function over the set
associateSetWith :: (Ord k) => (k -> v) -> Set k -> Map k v
associateSetWith f = Map.fromAscList . map (id &&& f) . Set.toAscList

-- | Squish two applicative actions into one which returns a tuple
pairA :: (Applicative f) => f a -> f b -> f (a,b)
pairA = (<*>) . fmap (,)

-- | All the different ways of saying yes and no
--   Lists must be disjoint or there are runtime errors in your future...
yes, no :: [String]
(yes, no) =
   let yes' = ["y","yes","yep","yeah","okay","ok","mkay","ay","positive"]
       no'  = ["n","no","nope","nah","nay","negative"]
   in case fastIntersect yes' no' of
         [] -> (yes', no')
         _  -> error "Internal error: English synonyms for 'yes' and 'no' cannot overlap."
