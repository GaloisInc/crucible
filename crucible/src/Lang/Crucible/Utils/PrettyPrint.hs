module Lang.Crucible.Utils.PrettyPrint
  ( commas
  , ppFn
  ) where

import Data.Maybe
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

ppFn :: String -> [Doc] -> Doc
ppFn f a = text f <> parens (commas a)

-- | Print a comma separated list.
commas :: Foldable f => f Doc -> Doc
commas l = fromMaybe PP.empty $ foldl go Nothing l
  where go Nothing y = Just y
        go (Just x) y = Just (x <> char ',' <+> y)
