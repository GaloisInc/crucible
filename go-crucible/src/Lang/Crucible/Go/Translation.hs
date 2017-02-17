{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}

module Lang.Crucible.Go.Translation where

import Language.Go.AST
import Language.Go.Types hiding (Complex)
import qualified Language.Go.Types as Go

import Lang.Crucible.RegCFG
import Lang.Crucible.Core
import Lang.Crucible.Generator
import Lang.Crucible.Types
import Lang.Crucible.BaseTypes
import Data.Parameterized.Some
import Data.Parameterized.NatRepr
import Data.Int
import Data.Maybe

-- | Translate a Go type to a Crucible type
translateType :: forall a. Int32 {-Target architecture word size-}
              -> ValueType
              -> (forall tp. TypeRepr tp -> a)
              -> a
translateType wordSize typ = typeAsRepr (instantiateWordSize wordSize typ)

instantiateWordSize :: Int32 -> ValueType -> ValueType
instantiateWordSize wordSize typ = case typ of
  Int Nothing signed -> Int (Just wordSize) signed
  _                  -> typ

typeAsRepr :: forall a. ValueType
           -> (forall tp. TypeRepr tp -> a)
           -> a
typeAsRepr typ lifter = injectType $ toTypeRepr typ
   where injectType :: Some TypeRepr -> a
         injectType (Some x) = lifter x

toTypeRepr :: forall a. ValueType
           -> Some TypeRepr
toTypeRepr typ = case typ of
  Int (Just width) _ -> case someNat (fromIntegral width) of
    Just (Some w) | Just LeqProof <- isPosNat w -> Some (BVRepr w)
    _ -> error $ unwords ["invalid integer width",show width]
  Float width -> Some RealValRepr
  Boolean -> Some BoolRepr
  Go.Complex width -> undefined
  Iota -> Some IntegerRepr
  Nil -> Some (MaybeRepr AnyRepr)
  String -> Some $ VectorRepr $ BVRepr (knownNat :: NatRepr 8)
  Function mrecvtyp paramtyps mspreadtyp returntyps -> undefined -- Ctx.Assignment????
  Array _ typ -> typeAsRepr typ $ \t -> Some $ VectorRepr t
  Struct fields -> undefined
  Pointer typ -> Some $ ReferenceRepr AnyRepr
  Go.Interface sig -> undefined
  Map keyType valueType -> undefined
  Slice typ -> typeAsRepr typ $ \t -> Some $ StructRepr undefined
  Channel _ typ -> toTypeRepr typ
  BuiltIn name -> undefined -- ^ built-in function
  Alias (TypeName (Just bind) _ _) -> undefined
