module Lang.MATLAB.Utils.List
  ( drop1
  , defIndex
  , setIndex
  ) where

-- | Remove element at given index in list.
drop1 :: Int -> [a] -> [a]
drop1 _ [] = []
drop1 n (e:l) | n <= 0 = l
              | otherwise = e:drop1 (n-1) l

-- | Get element at index falling back to default if needed.
defIndex :: [a] -> Int -> a -> a
defIndex [] _ d = d
defIndex (e:l) i d | i <= 0 = e
                   | otherwise = defIndex l (i-1) d

-- | Set value at given index in array or leave array unmodified if index
-- is out of range.
setIndex :: [a] -> Int -> a -> [a]
setIndex [] _ _ = []
setIndex (e:l) i v | i <= 0 = v:l
                   | otherwise = e:setIndex l (i-1) v
