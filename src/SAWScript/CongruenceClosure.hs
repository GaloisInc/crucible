{-# LANGUAGE DoAndIfThenElse #-}
module SAWScript.CongruenceClosure 
  ( -- * Functor type classes
    EqFoldable(..)
  , OrdFoldable(..)
  , ShowFoldable(..)
  , Foldable(..)
  , Traversable(..)
    -- * Term
  , Term(..)
  , evalTermM
    -- * CCSet
  , CCSet
  , empty
  , findEquivalent
  , areEquivalent
  , checkEquivalence
  , insertTerm
  , insertEquation
  , insertEquivalenceClass
  , union
  , fromSet
  , toSet
  , fromList
  , toList
  ) where

import Control.Applicative ((<$), (<$>))
import qualified Control.Monad.State as MTL
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable hiding (toList)
import Data.Traversable
import Prelude hiding (const, mapM)


-- Functor typeclass extensions {{{1

class EqFoldable f where
  -- | Compares equality of arguments.
  fequal :: Eq x => f x -> f x -> Bool

class EqFoldable f => OrdFoldable f where
  -- | Compares arguments.
  fcompare :: Ord x => f x -> f x -> Ordering

class ShowFoldable f where
  fshow :: Show x => f x -> String
  fshow x = fshows x ""
  fshows :: Show x => f x -> ShowS
  fshows x = (fshow x ++)

-- Term {{{1

-- | A term with the given operator.
newtype Term f = Term { unTerm :: f (Term f) }

instance EqFoldable f => Eq (Term f) where
  Term x == Term y = x `fequal` y

instance OrdFoldable f => Ord (Term f) where
  (Term x) `compare` (Term y) = x `fcompare` y

instance ShowFoldable app => Show (Term app) where
  showsPrec _ (Term x) s = "Term " ++ fshows x s

-- | Evaluate a term using the given monadic computation.
evalTermM :: (Monad m, Traversable f) => (f v -> m v) -> Term f -> m v
evalTermM fn (Term t) = fn =<< mapM (evalTermM fn) t

-- Class {{{1

newtype Class = Class Integer
  deriving (Eq, Ord)

-- ClassApp {{{1

newtype ClassApp f = ClassApp (f Class)

instance EqFoldable f => Eq (ClassApp f) where
  ClassApp x == ClassApp y = x `fequal` y

instance OrdFoldable f => Ord (ClassApp f) where
  (ClassApp x) `compare` (ClassApp y) = x `fcompare` y

-- CCSet {{{1

data CCSet f = CC {
         -- | Number of classes added so far.
         ccCnt :: !Integer
         -- | Maps representative to equivalent terms that were added to set.
       , ccElementMap :: !(Map Class (Set (Term f)))
         -- | Maps classes to the representative.
       , ccRepMap :: !(Map Class Class)
         -- | Maps applications to the representative.
       , ccAppMap :: !(Map (ClassApp f) Class)
       }

instance OrdFoldable f => Eq (CCSet f) where
  x == y = toSet x == toSet y

instance OrdFoldable f => Ord (CCSet f) where
  x `compare` y = toSet x `compare` toSet y

instance (OrdFoldable f, ShowFoldable f) => Show (CCSet f) where
  show cc = "fromList " ++ show (toList cc)

-- | Return empty set.
empty :: CCSet f
empty = CC { ccCnt = 0
           , ccElementMap = Map.empty
           , ccRepMap = Map.empty
           , ccAppMap = Map.empty
           }

-- | Returns all terms equivalent to term in set.
-- N.B. The list may be empty if the term is not in the set.
findEquivalent :: (OrdFoldable f, Traversable f)
               => Term f -> CCSet f -> Set (Term f)
findEquivalent t cc =
  case getExistingClass cc t of
    Just cl -> Map.findWithDefault Set.empty cl (ccElementMap cc)
    Nothing -> Set.empty

-- | Returns true if the two terms are considered equivalent.
areEquivalent :: (OrdFoldable f, Traversable f) 
              => Term f -> Term f -> CCSet f -> Bool
areEquivalent x y cc =
  flip MTL.evalState cc $ do
    xCl <- getClass x
    yCl <- getClass y
    return (xCl == yCl)

-- | Checks that all terms in the list are equivalent, and returns
-- a pair of inequivalent terms if a counterexample is found.
checkEquivalence :: (OrdFoldable f, Traversable f) 
                 => [Term f] -> CCSet f -> Maybe (Term f, Term f)
checkEquivalence (x:y:r) cc
  | areEquivalent x y cc = checkEquivalence (y:r) cc
  | otherwise = Just (x,y)
checkEquivalence _ _ = Nothing

-- | Insert term into set.
insertTerm :: (OrdFoldable f, Traversable f) => Term f -> CCSet f -> CCSet f
insertTerm = MTL.execState . getClass

-- | Assert that two terms are equal.
insertEquation :: (OrdFoldable f, Traversable f)
               => Term f -> Term f -> CCSet f -> CCSet f
insertEquation x y cc =
  flip MTL.execState cc $ do
    xCl <- getClass x
    yCl <- getClass y
    MTL.modify $ processEquivalences [(xCl, yCl)]

-- | Assert all elements in list are equal.
insertEquivalenceClass :: (OrdFoldable f, Traversable f)
                       => [Term f] -> CCSet f -> CCSet f
insertEquivalenceClass [] s = s
insertEquivalenceClass [x] s = insertTerm x s
insertEquivalenceClass (x:y:r) s =
  insertEquivalenceClass (y:r) $! insertEquation x y s

-- | Take union of two equivalence classes.
union :: (OrdFoldable f, Traversable f) => CCSet f -> CCSet f -> CCSet f
union x y =
  foldl' (\s cl -> insertEquivalenceClass (Set.toList cl) s)
         x
         (Map.elems (ccElementMap y))

fromSet :: (OrdFoldable f, Traversable f) => Set (Set (Term f)) -> CCSet f
fromSet = Set.fold (insertEquivalenceClass . Set.toList) empty

toSet :: OrdFoldable f => CCSet f -> Set (Set (Term f))
toSet = Set.fromList . Map.elems . ccElementMap

-- | Create a congruence closure set from the double list of terms,
-- where each list of terms denotes an equivalence class.
fromList :: (OrdFoldable f, Traversable f) => [[Term f]] -> CCSet f
fromList = foldl' (flip insertEquivalenceClass) empty

-- | Convert a congruence closure set into a double list of terms.
toList :: OrdFoldable f => CCSet f -> [[Term f]]
toList = map Set.toList . Set.toList . toSet

-- CCSet implementation {{{1

-- | Returns a class for term if one exists.
getExistingClass :: (OrdFoldable f, Traversable f) => CCSet f -> Term f -> Maybe Class
getExistingClass cc = evalTermM (\app -> Map.lookup (ClassApp app) (ccAppMap cc))

type Pair t = (t,t)

processEquivalences :: (Functor f, OrdFoldable f)
                    => [Pair Class] -> CCSet f -> CCSet f
processEquivalences [] cc = cc
processEquivalences ((x,y):rest) cc
  | xCl == yCl = processEquivalences rest cc
  | otherwise =
    processEquivalences
      ([ (l,r) | l:rl <- Map.elems appClassListMap, r <- rl ] ++ rest)
      (cc { ccElementMap = Map.fromListWith Set.union
                         $ map (\(cl,tl) -> (mapFn cl, tl))
                         $ Map.toList (ccElementMap cc)
          , ccRepMap = Map.insert xCl yCl $ Map.map mapFn repMap
          , ccAppMap = Map.map head appClassListMap
          })
 where repMap = ccRepMap cc
       xCl = Map.findWithDefault x x repMap
       yCl = Map.findWithDefault y y repMap
       mapFn z = if z == xCl then yCl else z
       appClassListMap = Map.fromListWith (++)
         [ (ClassApp (mapFn <$> app), [mapFn cl]) 
         | (ClassApp app,cl) <- Map.toList (ccAppMap cc) ]

type Comp f = MTL.State (CCSet f)

-- | Add term to equivalence class.
addTerm :: OrdFoldable f => Class -> Term f -> Comp f ()
addTerm cl t = do
  MTL.modify $ \cc ->
    cc { ccElementMap 
          = Map.insertWith Set.union cl (Set.singleton t)
          $ ccElementMap cc }

getClass :: (OrdFoldable f, Traversable f) => Term f -> Comp f Class
getClass (Term t) = do
  app <- ClassApp <$> mapM getClass t
  appMap <- MTL.gets ccAppMap
  case Map.lookup app appMap of
    Just cl -> cl <$ addTerm cl (Term t)
    Nothing -> do
      cc <- MTL.get
      let cnt = ccCnt cc
      let cl = Class cnt
      MTL.put cc { ccCnt = cnt + 1
                 , ccAppMap = Map.insert app cl (ccAppMap cc)
                 }
      cl <$ addTerm cl (Term t)
