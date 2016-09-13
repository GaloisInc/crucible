{-# LANGUAGE CPP #-}
module Lang.MATLAB.Utils.PrettyPrint
  ( commas
  , semicolons
  , ppShow
  , ppMatrix
  , AlignmentFunction
  , leftAlign
  , rightAlign
  , ppAlignedMatrix
  , alignMatrixRows
  , ppNameEqual
  , padLengths
  , padToMinLength
  , ppFrac
  , warn
  , ppFn
    -- * Re-exports
  , Doc
  ) where

import Control.Exception
import qualified Data.Foldable as Fold
import Control.Monad.IO.Class
import Data.Maybe
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))
import qualified Data.Vector as V

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif

ppFn :: String -> [Doc] -> Doc
ppFn f a = text f <> parens (commas a)

-- | Print a comma separated list.
commas :: Fold.Foldable f => f Doc -> Doc
commas l = fromMaybe PP.empty $ Fold.foldl go Nothing l
  where go Nothing y = Just y
        go (Just x) y = Just (x <> char ',' <+> y)

semicolons :: [Doc] -> Doc
semicolons [] = PP.empty
semicolons (h:r) = foldl (\x y -> x <> char ';' <+> y) h r

ppShow :: Show a => a -> Doc
ppShow = text . show


-- | Pretty print commas separated elements, and semicolon terminated rows.
ppMatrix :: [[Doc]] -> Doc
ppMatrix m = hsep (ppRow `fmap` m)
  where ppRow r = commas r <> char ';'

type AlignmentFunction = Int -> String -> String

-- | @leftAlign s n@ inserts @n@ spaces after @s@.
leftAlign :: AlignmentFunction
leftAlign l s = s ++ replicate l ' '

-- | @rightAlign n s@ inserts @n@ spaces before @s@.
rightAlign :: AlignmentFunction
rightAlign n s = replicate n ' ' ++ s

-- | Pretty print a matrix with the given values.
-- First argument is number of rows, second is number of columns.
-- Third argument takes rows and columns and is zero-based.
ppAlignedMatrix :: Int -- ^ Number of rows
                -> Int -- ^ Number of columns
                -> (Int -> AlignmentFunction)
                   -- ^ Get alignment for each column
                -> (Int -> Int -> String)
                   -- ^ Get text of each cell given row and column indices(0-based)
                -> Doc
ppAlignedMatrix rc cc alignFn f = vcat $ V.toList $ v
  where v = alignMatrixRows rc cc alignFn (fmap (max 6)) f

-- | Pretty print a matrix with the given values.
-- First argument is number of rows, second is number of columns.
-- Third argument takes rows and columns and is zero-based.
alignMatrixRows :: Int -- ^ Number of rows
                -> Int -- ^ Number of columns
                -> (Int -> AlignmentFunction)
                   -- ^ Get alignment for each column
                -> (V.Vector Int -> V.Vector Int)
                   -- ^ Adjust width of each column given maximum widths.
                -> (Int -> Int -> String)
                   -- ^ Get text of each cell given row and column indices(0-based)
                -> V.Vector Doc
alignMatrixRows rc cc alignFn colWidthFn f = ppRow <$> rf
  where -- Get strings for each column
        cv = V.generate cc $ \c ->
               V.generate rc $ \r ->
                 f r c
        alignments = V.generate cc alignFn
        -- Get length of each string
        cl :: V.Vector (V.Vector Int)
        cl = fmap length <$> cv
        -- Get maximum width of each column (minimum 6)
        cw :: V.Vector Int
        cw = colWidthFn (V.maximum <$> cl)
        -- Get amount of padding to add to each entry in the column.
        cp :: V.Vector (V.Vector Int)
        cp = V.zipWith (\w c -> fmap (w -) c) cw cl
        -- Get columns after adding padding
        cf :: V.Vector (V.Vector String)
        cf = V.zipWith3 V.zipWith alignments cp cv
        -- Compute transpose of cf
        rf :: V.Vector (V.Vector String)
        rf = V.generate (fromIntegral rc) $ \r ->
               V.generate (fromIntegral cc) $ \c -> cf V.! c V.! r
        -- Pretty print each row.
        ppRow :: V.Vector String -> Doc
        ppRow v = hsep $ V.toList $ text <$> v

-- | Pretty print a named value
ppNameEqual :: String -> Doc -> Doc
ppNameEqual nm v =
  text (nm ++ " =") <> line <> line <> indent 4 v <> line

-- | Insert char before string to reach given length.
padToMinLength :: Int -> Char -> String -> String
padToMinLength n c s | l < n = replicate (n-l) c ++ s
                     | True  = s
  where l = length s

-- | Pad spaces before each string so that all strings have an equal length.
padLengths :: [String] -> [String]
padLengths cw = zipWith rightAlign ((m -) <$> cl) cw
  where cl = length <$> cw
        m = maximum cl

------------------------------------------------------------------------
-- ppFrac

-- | Print a decimal number using the same rules as Matlab

ppFrac :: RealFrac a => a -> String
ppFrac r
      -- Whole numbers up with an absolute value up to 1 billion are
      -- printed without an exponent.
    | f == 0 && abs n < 10^(9::Int) = show (n :: Integer)
      -- Fractional numbers above 1000 are printed with an exponent.
    | abs r >= 1000 = printPosExponent r
      -- print with no exponent, but scaled to 4 digits after decimal
      -- point in precisiion
    | abs r >= 0.001 = printFixedPrecision r 4 ""
    | otherwise = printNegExponent r -- print with negative exponent.
  where (n,f) = properFraction r

-- | @printFixedPrecision v n@ prints @v@ with @n@ digits of
-- precision to the right of the decimal point.
printFixedPrecision :: RealFrac a => a -> Int -> ShowS
printFixedPrecision v n
    = prefix
    . shows q
    . showChar '.'
    . showString (pad0 n (abs r))
  where prefix | v >= 0 = id
               | otherwise = showChar '-'
        s = (round (abs v * 10^n)) :: Integer
        (q, r) = s `quotRem` (10^n)

printPosExponent :: RealFrac a => a -> String
printPosExponent = go 0
  where go n v
          | abs v >= 10 = go (n+1) (v/10)
          | otherwise = printFixedPrecision v 4 ("e" ++ pad0 2 n)

printNegExponent :: RealFrac a => a -> String
printNegExponent = go 0
  where go n v
          | abs v < 1 = go (n+1) (10*v)
          | otherwise = printFixedPrecision v 4 ("e-" ++ pad0 2 n)

pad0 :: Int -> Integer -> String
pad0 n v = assert (v >= 0) $ padToMinLength n '0' (show v)

warn :: MonadIO m => String -> m ()
warn msg = liftIO $ putStrLn $ "Warning: " ++ msg
