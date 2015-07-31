module SAWScript.AutoMatch.Declaration 
  ( Type(..), TCon(..), TC(..)
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

import Cryptol.TypeCheck.AST (Type(..), TCon(..), TC(..))
import Cryptol.Utils.PP

-- | Names are strings
type Name = String

-- | Arguments are names with (Cryptol) types
data Arg = Arg { argName :: Name
               , argType :: Type }
               deriving (Eq, Ord)

instance Show Arg where
   showsPrec d (Arg n t) =
      showParen (d > app_prec) $
         showString n
         . showString " : "
         . showString (pretty t)
      where app_prec = 10

-- | Declarations have a name, a return type, and a list of arguments
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
         . showString (pretty t)
      where
         app_prec = 10

-- | The signature of a declaration is the multiset of its argument types crossed with its return type
data Sig = Sig { sigArgs_ :: Map Type Int
               , sigOut_  :: Type }
               deriving (Eq, Ord)

sigArgs :: Sig -> Map Type Int
sigArgs = sigArgs_

sigOut :: Sig -> Type
sigOut  = sigOut_

-- | Compute the signature of a declaration
declSig :: Decl -> Sig
declSig (Decl _ t as) =
  flip Sig t $
    foldr (uncurry (Map.insertWith (const succ))) Map.empty $
      map (argType &&& const 1) as
