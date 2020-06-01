module Crux.Loops where

import qualified Data.Map as Map

data Tree a = Node { node :: a, children :: Forest a }
                    deriving Show

type Forest a = [Tree a]

findLoops :: Eq a => [a] -> Forest a
findLoops = go []
  where
  go prev steps =
    case steps of
      [] -> reverse prev
      x : xs ->
        case break ((x ==) . node) prev of
          (inner,_:prev') -> go (Node x [] : Node x (reverse inner) : prev') xs
          _               -> go (Node x [] : prev) xs


annotate :: Ord a => Forest a -> [ ([Int],a) ]
annotate = go [] Map.empty [] []
  where
  go ns iters prevIters rest todo =
    case todo of
      [] -> rest
      tree : trees ->
        let a = node tree
            n = Map.findWithDefault 1 a iters
            ns' = n : ns
            rest' = go ns (Map.insert a (n+1) iters) prevIters rest trees
        in (reverse ns', a) :
              go ns' Map.empty (iters : prevIters) rest' (children tree)


annotateLoops :: Ord a => [a] -> [ ([Int],a) ]
annotateLoops = annotate . findLoops


