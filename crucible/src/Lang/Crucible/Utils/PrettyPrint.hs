module Lang.Crucible.Utils.PrettyPrint
  ( commas
  , ppFn
  ) where

import Data.Maybe
import Prettyprinter as PP

ppFn :: String -> [Doc ann] -> Doc ann
ppFn f a = pretty f <> parens (commas a)

-- | Print a comma separated list.
commas :: Foldable f => f (Doc ann) -> Doc ann
commas l = fromMaybe mempty $ foldl go Nothing l
  where go Nothing y = Just y
        go (Just x) y = Just (x <> pretty ',' <+> y)
