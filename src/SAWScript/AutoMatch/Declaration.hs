module SAWScript.AutoMatch.Declaration where

import Data.List

data Type = Array Type
          | Pointer Type
          | Int |  Long |  Short |  Char
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
