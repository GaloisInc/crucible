module SAWScript.AutoMatch.Declaration 
  ( Type(..)
  , Name
  , Arg(..)
  , Decl(..)
  , Sig
  , sigArgs
  , sigOut
  , declSig
  ) where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Arrow ( (&&&) )

data Type = Array Type
          | Pointer Type
          | Int |  Long |  Short |  Char | Bool
          | UInt | ULong | UShort | UChar
          | Double | Float | Void
          deriving (Eq, Ord, Show)

type Name = String

data Arg = Arg { argName :: Name
               , argType :: Type }
               deriving (Eq, Ord)

instance Show Arg where
   showsPrec d (Arg n t) =
      showParen (d > app_prec) $
         showString n
         . showString " : "
         . showsPrec (app_prec + 1) t
      where app_prec = 10

data Decl = Decl { declName :: Name
                 , declType :: Type
                 , declArgs :: [Arg] }
                 deriving (Eq, Ord)

instance Show Decl where
   showsPrec d (Decl n t as) =
      showParen (d > app_prec) $
         showString n
         . showString " : "
         . showString "("
         . showString (intercalate ", " (map show as))
         . showString ")"
         . showString " -> "
         . showsPrec (app_prec + 1) t
      where
         app_prec = 10

data Sig = Sig { sigArgs_ :: Map Type Int
               , sigOut_  :: Type }
               deriving (Eq, Ord)

sigArgs :: Sig -> Map Type Int
sigArgs = sigArgs_

sigOut :: Sig -> Type
sigOut  = sigOut_

declSig :: Decl -> Sig
declSig (Decl _ t as) =
  flip Sig t $
    foldr (uncurry (Map.insertWith (const succ))) Map.empty $
      map (argType &&& const 1) as
