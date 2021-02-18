{-|
Module      : Lang.Crucible.Go.TransUtil
Description : Go translation 
Maintainer  : abagnall@galois.com
Stability   : experimental

This file contains helper functions used by the translation module.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Go.TransUtil where

import           Control.Monad.Fail (MonadFail)
import           Control.Monad.Identity
import           Control.Monad.State

import           Data.BitVector.Sized
import           Data.Functor.Product
import           Data.Maybe (fromMaybe)
import           Data.Text as T hiding (foldl, length, reverse, zip)
import qualified Data.Vector as V

import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.TraversableFC

import           Debug.Trace (trace)

import           What4.Utils.StringLiteral

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Generator as Gen
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types

import           Language.Go.AST
import           Language.Go.Rec
import           Language.Go.Types
import           Lang.Crucible.Go.Encodings
import           Lang.Crucible.Go.Types

-- | Use this function (or one of its variants) to assert that an
-- expression has a certain type. Unit values may be coerced to
-- Nothing values of a Maybe type. Floats may be cast (usually from
-- float literals being double by default but allowed to implicitly
-- cast to single precision). It may be useful in the future to do a
-- type inference pass, inferring the actual eventual types of
-- "untyped constants", to obviate the need for this coercion
-- stuff. It seems that the Go typechecker is doing this for us for
-- integer constants but not floats or nil.
asTypeEither :: TypeRepr b
             -> Gen.Expr Go s a
             -> Either (Some TypeRepr, Some (Gen.Expr Go s)) (Gen.Expr Go s b)
asTypeEither repr e =
  -- trace ("coercing " ++ show (exprType e) ++ " to " ++ show repr) $
  case testEquality (exprType e) repr of
    Just Refl -> Right e
    Nothing ->
      -- When the types are not equal, try to coerce the value.
      case (e, exprType e, repr) of
        -- Send unit to Nothing.
        (Gen.App C.EmptyApp, _repr, MaybeRepr repr') ->
          Right $ Gen.App $ C.NothingValue repr'
        -- Coerce floats (usually double to float)
        (_e, FloatRepr _fi, FloatRepr fi) ->
          Right $ Gen.App $ C.FloatCast fi C.RNE e
        _ -> Left (Some repr, Some e)

asTypeMaybe :: TypeRepr b -> Gen.Expr Go s a -> Maybe (Gen.Expr Go s b)
asTypeMaybe repr e = case asTypeEither repr e of
  Left _x -> Nothing
  Right e' -> Just e'

asType :: TypeRepr b -> Gen.Expr Go s a -> Gen.Expr Go s b
asType repr e =
  case asTypeMaybe repr e of
    Just e' -> e'
    Nothing -> error $ "asType fail: expression " ++ show e ++ " of type "
               ++ show (exprType e) ++ " incompatible with type " ++ show repr

-- | CPS version of asType
asType' :: TypeRepr b -> Gen.Expr Go s a -> (Gen.Expr Go s b -> c) -> c
asType' repr e k = k $ asType repr e

-- | asTypeEither lifted to assignments.
asTypesEither :: CtxRepr ctx'
              -> Assignment (Gen.Expr Go s) ctx
              -> Either (Some TypeRepr, Some (Gen.Expr Go s))
              (Assignment (Gen.Expr Go s) ctx')
asTypesEither Empty Empty = Right Empty
asTypesEither (reprs :> repr) (es :> e) =
  (:>) <$> asTypesEither reprs es <*> asTypeEither repr e

-- | asTypeMaybe lifted to assignments.
asTypesMaybe :: CtxRepr ctx' ->
                Assignment (Gen.Expr Go s) ctx ->
                Maybe (Assignment (Gen.Expr Go s) ctx')
asTypesMaybe Empty Empty = Just Empty
asTypesMaybe (reprs :> repr) (es :> e) =
  pure (:>) <*> asTypesMaybe reprs es <*> asTypeMaybe repr e

asTypes :: CtxRepr ctx' ->
           Assignment (Gen.Expr Go s) ctx ->
           Assignment (Gen.Expr Go s) ctx'
asTypes ctx assignment = case asTypesEither ctx assignment of
  Right assignment' -> assignment'
  Left (Some repr, Some e)->
    error $ "asTypes: " ++ show e ++ " incompatible with " ++ show repr

-- | CPS version of asTypes
asTypes' :: CtxRepr ctx' ->
            Assignment (Gen.Expr Go s) ctx ->
            (Assignment (Gen.Expr Go s) ctx' -> a) -> a
asTypes' ctxRepr assignment k = k $ asTypes ctxRepr assignment

tryAsBV :: Gen.Expr Go s tp
        -> (forall w. (1 <= w) => NatRepr w -> Gen.Expr Go s (BVType w) -> b)
        -> b
        -> b
tryAsBV e k b = case exprType e of
  BVRepr w -> k w e
  _repr -> b

tryAsStringRepr :: TypeRepr tp
                -> (forall si. StringInfoRepr si ->
                     TypeRepr (StringType si) -> b)
               -> b
               -> b
tryAsStringRepr repr k b = case repr of
  StringRepr si -> k si repr
  _repr -> b

tryAsString :: Gen.Expr Go s tp
            -> (forall si. StringInfoRepr si ->
                 Gen.Expr Go s (StringType si) -> b)
            -> b
            -> b
tryAsString e k b = case exprType e of
  StringRepr si -> k si e
  _repr -> b

tryAsPointer :: Gen.Expr Go s tp
             -> (forall a. TypeRepr a -> Gen.Expr Go s (PointerType a) -> b)
             -> b
             -> b
tryAsPointer e k b = case exprType e of
  -- TODO: this could probably be made cleaner
  MaybeRepr (VariantRepr
             (Ctx.Empty :> ReferenceRepr repr :> StructRepr
               (Ctx.Empty :> ReferenceRepr (VectorRepr repr') :> NatRepr))) ->
    case testEquality repr repr' of
      Just Refl -> k repr e
      Nothing -> b
  _repr -> b

asPointer :: MonadFail m
          => Gen.Expr Go s tp
          -> (forall a. Gen.Expr Go s (PointerType a) -> m b)
          -> m b
asPointer e k = tryAsPointer e (\_repr ptr -> k ptr) $
  fail $ "asPointerType: expected pointer, got " ++ show e

tryAsReference :: Gen.Expr Go s tp
            -> (forall a. TypeRepr a -> Gen.Expr Go s (ReferenceType a) -> b)
            -> b
            -> b
tryAsReference e k b = case exprType e of
  ReferenceRepr repr -> k repr e
  _repr -> b

tryAsVector :: Gen.Expr Go s tp
         -> (forall a. TypeRepr a -> Gen.Expr Go s (VectorType a) -> b)
         -> b
         -> b
tryAsVector e k b = case exprType e of
  VectorRepr repr -> k repr e
  _repr -> b

tryAsArray :: Gen.Expr Go s tp
           -> (forall a. TypeRepr a -> Gen.Expr Go s (ArrayType a) -> b)
           -> b
           -> b
tryAsArray e k b = case exprType e of
  ReferenceRepr (VectorRepr repr) -> k repr e
  _repr -> b

tryAsArrayRepr :: TypeRepr tp
               -> (forall a. (tp ~ ArrayType a) =>
                    TypeRepr (ArrayType a) -> b)
               -> b
               -> b
tryAsArrayRepr repr k b = case repr of
  ReferenceRepr (VectorRepr _repr) -> k repr
  _repr -> b

tryAsArrayOffsetRepr :: TypeRepr tp
                     -> (forall a. (tp ~ ArrayOffset a) =>
                          TypeRepr (ArrayOffset a) -> b)
                     -> b
                     -> b
tryAsArrayOffsetRepr repr k b = case repr of
  StructRepr (Ctx.Empty :> arrRepr :> NatRepr) ->
    tryAsArrayRepr arrRepr (\arrRepr' -> k repr) b
  _repr -> b


tryAsPointerRepr :: TypeRepr tp
                 -> (forall a. (tp ~ PointerType a) =>
                      TypeRepr (PointerType a) -> b)
                 -> b
                 -> b
tryAsPointerRepr repr k b = case repr of
  MaybeRepr (VariantRepr (Empty :> ReferenceRepr repr1 :> arrayOffsetRepr)) ->
    tryAsArrayOffsetRepr arrayOffsetRepr
    (\arrayOffsetRepr' -> case arrayOffsetRepr' of
        StructRepr (Ctx.Empty :> ReferenceRepr (VectorRepr repr2) :> NatRepr) ->
          case testEquality repr1 repr2 of
            Just Refl -> k repr
            Nothing -> b
    ) b
  _repr -> b

tryAsSliceRepr :: TypeRepr tp
               -> (forall a. (tp ~ SliceType a) =>
                    TypeRepr (SliceType a) -> b)
               -> b
               -> b
tryAsSliceRepr repr k b = case repr of
  MaybeRepr
    (StructRepr (Ctx.Empty :> ptrRepr :> NatRepr :> NatRepr :> NatRepr)) ->
    tryAsPointerRepr ptrRepr
    (\ptrRepr' -> case ptrRepr' of
        PointerRepr arrRepr ->
          tryAsArrayRepr arrRepr
          (\arrRepr' -> case arrRepr of
              ArrayRepr _repr' -> k repr
          ) b
    ) b
  _repr -> b

tryAsSlice :: Gen.Expr Go s tp
           -> (forall a. (tp ~ SliceType a) =>
               TypeRepr a -> Gen.Expr Go s (SliceType a) -> b)
           -> b
           -> b
tryAsSlice e k b = tryAsSliceRepr (exprType e)
                   (\repr -> k (sliceElementRepr repr) e
                   ) b


index4_0 :: Index (EmptyCtx ::> a ::> b ::> c ::> d) a
index4_0 = skipIndex $ skipIndex $ skipIndex baseIndex

index4_1 :: Index (EmptyCtx ::> a ::> b ::> c ::> d) b
index4_1 = skipIndex $ skipIndex $ nextIndex $ incSize zeroSize

index4_2 :: Index (EmptyCtx ::> a ::> b ::> c ::> d) c
index4_2 = skipIndex $ nextIndex $ incSize $ incSize zeroSize

index4_3 :: Index (EmptyCtx ::> a ::> b ::> c ::> d) d
index4_3 = lastIndex knownSize


-- | Slice projections
nonNilSliceArray :: Gen.Expr Go s (NonNilSliceType tp)
                 -> GoGenerator s ret
                    (Gen.Expr Go s (PointerType (ArrayType tp)))
nonNilSliceArray slice = case exprType slice of
  StructRepr (Empty :> arrPtrRepr :> NatRepr :> NatRepr :> NatRepr) ->
    return $ Gen.App $ C.GetStruct slice index4_0 arrPtrRepr

nonNilSliceBegin :: Gen.Expr Go s (NonNilSliceType tp)
                 -> GoGenerator s ret (Gen.Expr Go s NatType)
nonNilSliceBegin slice = case exprType slice of
  StructRepr (Empty :> arrPtrRepr :> NatRepr :> NatRepr :> NatRepr) ->
    return $ Gen.App $ C.GetStruct slice index4_1 NatRepr

nonNilSliceEnd :: Gen.Expr Go s (NonNilSliceType tp)
               -> GoGenerator s ret (Gen.Expr Go s NatType)
nonNilSliceEnd slice = case exprType slice of
  StructRepr (Empty :> arrPtrRepr :> NatRepr :> NatRepr :> NatRepr) ->
    return $ Gen.App $ C.GetStruct slice index4_2 NatRepr

nonNilSliceCapacity :: Gen.Expr Go s (NonNilSliceType tp)
                    -> GoGenerator s ret (Gen.Expr Go s NatType)
nonNilSliceCapacity slice = case exprType slice of
  StructRepr (Empty :> arrPtrRepr :> NatRepr :> NatRepr :> NatRepr) ->
    return $ Gen.App $ C.GetStruct slice index4_3 NatRepr

sliceArray :: Gen.Expr Go s (SliceType tp)
           -> GoGenerator s ret (Gen.Expr Go s (PointerType (ArrayType tp)))
sliceArray slice = maybeElim' slice nonNilSliceArray

sliceBegin :: Gen.Expr Go s (SliceType tp)
           -> GoGenerator s ret (Gen.Expr Go s NatType)
sliceBegin slice = maybeElim' slice nonNilSliceBegin

sliceEnd :: Gen.Expr Go s (SliceType tp)
         -> GoGenerator s ret (Gen.Expr Go s NatType)
sliceEnd slice = maybeElim' slice nonNilSliceEnd

sliceCapacity :: Gen.Expr Go s (SliceType tp)
              -> GoGenerator s ret (Gen.Expr Go s NatType)
sliceCapacity slice = maybeElim' slice nonNilSliceCapacity


writeVectorElements :: Gen.Expr Go s (VectorType tp)
                    -> [SomeGoExpr s]
                    -> GoGenerator s ret (Gen.Expr Go s (VectorType tp))
writeVectorElements vec es =
  foldM (\v (i, Some (GoExpr _loc e)) -> asType' repr e $ \e' ->
            return $ Gen.App $ C.VectorSetEntry repr v (intNat i) e')
  vec $ zip [0..] es
  where
    repr = vectorElementRepr $ exprType vec

newArray :: Gen.Expr Go s tp -- ^ default element value
         -> Gen.Expr Go s NatType -- ^ size
         -> GoGenerator s ret (Gen.Expr Go s (ArrayType tp))
newArray value size =
  Gen.newRef $ Gen.App $ C.VectorReplicate (exprType value) size value

newSlice :: Gen.Expr Go s tp -- ^ default element value
         -> Gen.Expr Go s NatType -- ^ size
         -> Gen.Expr Go s NatType -- ^ capacity
         -> GoGenerator s ret (Gen.Expr Go s (SliceType tp))
newSlice value size cap = do
  arr <- newArray value size
  ptr <- newRefPointer arr
  sliceValue ptr (Just $ Gen.App $ C.NatLit 0)
    (Just $ Gen.App $ C.NatSub size $ Gen.App $ C.NatLit 1)
    (Just cap)

mkTranslatedExpr :: TypeRepr ret
                 -> (forall s. GoGenerator s ret (SomeGoExpr s))
                 -> Translated Expr
mkTranslatedExpr retRepr gen = TranslatedExpr $ SomeGoGenerator retRepr gen

mkTranslatedStmt :: TypeRepr ret
                 -> (forall s. GoGenerator s ret ())
                 -> Translated Stmt
mkTranslatedStmt retRepr gen = TranslatedStmt $ SomeGoGenerator retRepr gen

intNat :: Int -> Gen.Expr Go s NatType
intNat = Gen.App . C.NatLit . fromInteger . toInteger

runTranslated :: forall f s a. Product f TranslateM a
              -> TranslateM' (Translated a)
runTranslated = runTranslateM . proj2

failIfNotEqual :: forall k f m a (b :: k).
                  (MonadFail m, Show (f a), Show (f b), TestEquality f)
               => f a -> f b -> String -> m (a :~: b)
failIfNotEqual r1 r2 str
  | Just Refl <- testEquality r1 r2 = return Refl
  | otherwise =
    fail $ str ++ ": mismatch between " ++ show r1 ++ " and " ++ show r2

runSomeGoGenerator :: TypeRepr ret -> SomeGoGenerator s a -> GoGenerator s ret a
runSomeGoGenerator retRepr (SomeGoGenerator repr gen) = do
  Refl <- failIfNotEqual retRepr repr
          "runSomeGoGenerator: checking return type"
  gen

runTranslatedStmt :: TypeRepr ret -> Translated Stmt -> GoGenerator s ret ()
runTranslatedStmt repr (TranslatedStmt gen) = runSomeGoGenerator repr gen

runTranslatedBlock :: TypeRepr ret -> Translated Block -> GoGenerator s ret ()
runTranslatedBlock repr (TranslatedBlock gen) = runSomeGoGenerator repr gen

unTranslatedExpr :: Translated Expr
                 -> (forall s. SomeGoGenerator s (SomeGoExpr s))
unTranslatedExpr (TranslatedExpr gen) = gen

runTranslatedExpr :: TypeRepr ret
                  -> Translated Expr
                  -> GoGenerator s ret (SomeGoExpr s)
runTranslatedExpr repr texpr = case texpr of
  TranslatedExpr gen -> runSomeGoGenerator repr gen
  TranslatedUnbound qual name ->
    fail $ "runTranslatedExpr: unexpected unbound identifier: " ++
    show qual ++ " " ++ show name

runTranslatedExpr' :: TypeRepr ret
                   -> Translated Expr
                   -> GoGenerator s ret (Either (Ident, Ident) (SomeGoExpr s))
runTranslatedExpr' repr texpr = case texpr of
  TranslatedExpr gen -> Right <$> runSomeGoGenerator repr gen
  TranslatedUnbound qual name -> return $ Left (qual, name)

coerceAssignment :: CtxRepr expectedCtx ->
                    Assignment (Gen.Expr Go s) ctx ->
                    Assignment (Gen.Expr Go s) expectedCtx
coerceAssignment expectedCtx assignment =
  case asTypesEither expectedCtx assignment of
    Right assignment' -> assignment'
    Left (Some repr, Some e) ->
      error $ "coerceAssignment: " ++ show e ++
      " incompatible with " ++ show repr

withAssignment :: [SomeGoExpr s]
               -> (forall args. CtxRepr args ->
                   Assignment (Gen.Expr Go s) args -> a)
               -> a
withAssignment [] k = k Empty Empty
withAssignment (Some (GoExpr _loc e) : es) k =
  withAssignment es $ \ctx assignment ->
  k (ctx :> exprType e) (assignment :> e)

-- | Note that we don't have to consider the case when both sides are
-- untyped because all untyped constants are fully evaluated by Go's
-- typechecker.
unify_exprs :: MonadFail m => Type -> Type -> SomeGoExpr s -> SomeGoExpr s
            -> m (Type, SomeExprPair s)
unify_exprs t1 t2 (Some (GoExpr _loc1 e1)) (Some (GoExpr _loc2 e2)) =
  case (t1, t2) of
    (BasicType (BasicUntyped _ukind), _) ->
      return (t2, Some $ PairIx (asType (exprType e2) e1) e2)
    (_, BasicType (BasicUntyped _ukind)) ->
      return (t1, Some $ PairIx e1 $ asType (exprType e1) e2)
    _ ->
      if t1 == t2 then
        return (t1, Some $ PairIx e1 $ asType (exprType e1) e2)
      else
        fail $ "unify_exprs: incompatible types: " ++ show t1 ++ ", " ++ show t2

mkVector :: Int -- ^ size
         -> Gen.Expr Go s tp -- ^ initial value
         -> Gen.Expr Go s (VectorType tp)
mkVector len value =
  Gen.App $ C.VectorLit (exprType value) $ V.replicate len value

zeroVector :: Int -> Type -> TypeRepr tp ->
              GoGenerator s ret (Gen.Expr Go s (VectorType tp))
zeroVector len tp repr = do
  zero <- zeroValue' tp repr
  return $ mkVector len zero

zeroValue :: Type -> TypeRepr a -> Maybe (Gen.Expr Go s a)
zeroValue tp repr = Gen.App <$> case repr of
  UnitRepr -> return C.EmptyApp
  BoolRepr -> return $ C.BoolLit False
  BVRepr w -> return $ C.BVLit w $ mkBV w 0
  FloatRepr SingleFloatRepr -> return $ C.FloatLit 0.0
  FloatRepr DoubleFloatRepr -> return $ C.DoubleLit 0.0
  StringRepr UnicodeRepr -> return $ C.StringLit $ UnicodeLiteral ""
  MaybeRepr repr -> return $ C.NothingValue repr
  StructRepr ctx ->
    let tps = case tp of
          StructType ts -> ts
          TupleType ts -> ts in
      C.MkStruct ctx <$> traverseWithIndex
      (\ix x -> zeroValue (typeOfNameType $ tps !! indexVal ix) x) ctx
  VectorRepr repr ->
    let (tp', len) = case tp of
          ArrayType n t -> (t, n) in
      C.VectorLit repr . V.replicate len <$> zeroValue tp' repr
  _ -> Nothing

zeroValue' :: MonadFail m => Type -> TypeRepr a -> m (Gen.Expr Go s a)
zeroValue' tp repr =
  maybe (fail $ "zeroValue': no zero value for type " ++ show tp
         ++ " with repr " ++ show repr) return $ zeroValue tp repr

indexedAssignment :: Assignment f ctx
                  -> Assignment (Product (Index ctx) f) ctx
indexedAssignment =
  runIdentity . traverseWithIndex (\ix x -> return $ Pair ix x)

indexedList :: Assignment f ctx -> [Some (Product (Index ctx) f)]
indexedList = toListFC Some . indexedAssignment

someIndexVal :: Assignment f ctx -> Int -> Some (Product (Index ctx) f)
someIndexVal assignment i = reverse (indexedList assignment) !! i

withIndex :: Assignment f ctx
          -> Int
          -> (forall tp. Index ctx tp -> f tp -> a)
          -> a
withIndex assignment i k = case someIndexVal assignment i of
  Some (Pair ix x) -> k ix x

-- | Elimination principle for non-nil pointers.
nonNilPointerElim :: TypeRepr a
                  -> (Gen.Expr Go s (ReferenceType tp) ->
                       GoGenerator s ret (Gen.Expr Go s a))
                  -> (Gen.Expr Go s (ArrayOffset tp) ->
                       GoGenerator s ret (Gen.Expr Go s a))
                  -> Gen.Expr Go s (NonNilPointerType tp)
                  -> GoGenerator s ret (Gen.Expr Go s a)
nonNilPointerElim repr f g ptr = do
  continue_lbl <- Gen.newLambdaLabel' repr
  ref_lbl <- Gen.newLambdaLabel' $ ReferenceRepr ptrRepr
  arr_lbl <- Gen.newLambdaLabel' $ ArrayOffsetRepr ptrRepr
  Gen.defineLambdaBlock ref_lbl $ \ref ->
    f ref >>= Gen.jumpToLambda continue_lbl
  Gen.defineLambdaBlock arr_lbl $ \arr ->
    g arr >>= Gen.jumpToLambda continue_lbl
  Gen.continueLambda continue_lbl $
    Gen.branchVariant ptr $ Ctx.empty :> ref_lbl :> arr_lbl
  where
    ptrRepr = nonNilPointerElementRepr $ exprType ptr

-- | Non-nil pointer elimination principle with no return value.
nonNilPointerElim_ :: (Gen.Expr Go s (ReferenceType tp) ->
                        GoGenerator s ret ())
                   -> (Gen.Expr Go s (ArrayOffset tp) ->
                        GoGenerator s ret ())
                   -> Gen.Expr Go s (NonNilPointerType tp)
                   -> GoGenerator s ret ()
nonNilPointerElim_ f g ptr = do
  continue_lbl <- Gen.newLabel
  ref_lbl <- Gen.newLambdaLabel' $ ReferenceRepr ptrRepr
  arr_lbl <- Gen.newLambdaLabel' $ ArrayOffsetRepr ptrRepr
  Gen.defineLambdaBlock ref_lbl $ \ref ->
    f ref >> Gen.jump continue_lbl
  Gen.defineLambdaBlock arr_lbl $ \arr ->
    g arr >> Gen.jump continue_lbl
  Gen.continue continue_lbl $
    Gen.branchVariant ptr $ Ctx.empty :> ref_lbl :> arr_lbl
  where
    ptrRepr = nonNilPointerElementRepr $ exprType ptr

pointerElim :: TypeRepr a
            -> (Gen.Expr Go s (ReferenceType tp) ->
                 GoGenerator s ret (Gen.Expr Go s a))
            -> (Gen.Expr Go s (ArrayOffset tp) ->
                 GoGenerator s ret (Gen.Expr Go s a))
            -> Gen.Expr Go s (PointerType tp)
            -> GoGenerator s ret (Gen.Expr Go s a)
pointerElim repr f g ptr =
  maybeElim' ptr $ nonNilPointerElim repr f g

pointerElim_ :: (Gen.Expr Go s (ReferenceType tp) ->
                  GoGenerator s ret ())
             -> (Gen.Expr Go s (ArrayOffset tp) ->
                  GoGenerator s ret ())
             -> Gen.Expr Go s (PointerType tp)
             -> GoGenerator s ret ()
pointerElim_ f g ptr =
  maybeElim' ptr $ nonNilPointerElim_ f g

maybeElim :: TypeRepr a -- ^ result type repr
          -> GoGenerator s ret (Gen.Expr Go s a) -- ^ Nothing case
          -> (Gen.Expr Go s tp ->
               GoGenerator s ret (Gen.Expr Go s a)) -- ^ Just case
          -> Gen.Expr Go s (MaybeType tp) -- ^ discriminee
          -> GoGenerator s ret (Gen.Expr Go s a)
maybeElim repr x f e = Gen.caseMaybe e repr (Gen.MatchMaybe f x)

-- maybeElim_ :: GoGenerator s ret () -- ^ Nothing case
--            -> (Gen.Expr Go s tp -> GoGenerator s ret ()) -- ^ Just case
--            -> Gen.Expr Go s (MaybeType tp) -- ^ discriminee
--            -> GoGenerator s ret ()
-- maybeElim_ repr x f e = Gen.caseMaybe_ e (Gen.MatchMaybe f x)

maybeElim' :: Gen.Expr Go s (MaybeType tp)
           -> (Gen.Expr Go s tp -> GoGenerator s ret a)
           -> GoGenerator s ret a
maybeElim' e f =
  Gen.fromJustExpr e err_msg >>= f
  where
    err_msg = Gen.App $ C.StringLit $ UnicodeLiteral $ T.pack $
              "attempt to use nil value " ++ show e

arrayOffsetArray :: Gen.Expr Go s (ArrayOffset tp)
                 -> Gen.Expr Go s (ArrayType tp)
arrayOffsetArray e = case exprType e of
  StructRepr (Empty :> arr_repr :> NatRepr) ->
    Gen.App $ C.GetStruct e (skipIndex baseIndex) arr_repr

arrayOffsetIndex :: Gen.Expr Go s (ArrayOffset tp)
                 -> Gen.Expr Go s NatType
arrayOffsetIndex e = case exprType e of
  StructRepr (Empty :> _arr_repr :> NatRepr) ->
    Gen.App $ C.GetStruct e (lastIndex knownSize) NatRepr

readNonNilPointer :: Gen.Expr Go s (NonNilPointerType tp)
                  -> GoGenerator s ret (Gen.Expr Go s tp)
readNonNilPointer ptr =
  nonNilPointerElim (nonNilPointerElementRepr $ exprType ptr)
  Gen.readRef readArrayOffset ptr

readPointer :: Gen.Expr Go s (PointerType tp)
            -> GoGenerator s ret (Gen.Expr Go s tp)
readPointer ptr =
  pointerElim (pointerElementRepr $ exprType ptr)
  Gen.readRef readArrayOffset ptr


writePointer :: Gen.Expr Go s (PointerType tp)
             -> Gen.Expr Go s tp
             -> GoGenerator s ret ()
writePointer ptr value =
  pointerElim_ (`Gen.writeRef` value) (`writeArrayOffset` value) ptr

readArrayOffset :: Gen.Expr Go s (ArrayOffset tp)
                -> GoGenerator s ret (Gen.Expr Go s tp)
readArrayOffset e = case exprType e of
  ArrayOffsetRepr repr -> do
    arr <- Gen.readRef $ arrayOffsetArray e
    return $ Gen.App $ C.VectorGetEntry repr arr $ arrayOffsetIndex e

writeArrayOffset :: Gen.Expr Go s (ArrayOffset tp)
                 -> Gen.Expr Go s tp
                 -> GoGenerator s ret ()
writeArrayOffset arrOffset value = case exprType arrOffset of
  ArrayOffsetRepr repr -> do
    let arr = arrayOffsetArray arrOffset
    vec <- Gen.readRef arr
    Gen.writeRef arr $
      Gen.App $ C.VectorSetEntry (arrayElementRepr $ exprType arr)
      vec (arrayOffsetIndex arrOffset) value

natToBV :: (1 <= w)
        => NatRepr w
        -> Gen.Expr ext s NatType
        -> Gen.Expr ext s (BVType w)
natToBV w n = Gen.App $ C.IntegerToBV w $ Gen.App $ C.NatToInteger n

intToBV :: (1 <= w)
        => NatRepr w
        -> Gen.Expr ext s IntegerType
        -> Gen.Expr ext s (BVType w)
intToBV w n = Gen.App $ C.IntegerToBV w n


zeroBV :: (1 <= w) => NatRepr w -> Gen.Expr ext s (BVType w)
zeroBV w = Gen.App $ C.BVLit w $ mkBV w 0

mkBasicConst :: PosNat -> BasicConst -> Some (Gen.Expr Go s)
mkBasicConst n@(PosNat w LeqProof) c = case c of
  BasicConstBool b -> Some $ Gen.App $ C.BoolLit b
  BasicConstString str ->
    Some $ Gen.App $ C.StringLit $ UnicodeLiteral str
  BasicConstInt i -> Some $ Gen.App $ C.BVLit w $ mkBV w i
  -- Cast the numerator and denominator to float and divide.
  BasicConstFloat num denom ->
    case (mkBasicConst n num, mkBasicConst n denom) of
      (Some num', Some denom') -> asType' (BVRepr w) num' $ \num'' ->
        asType' (BVRepr w) denom' $ \denom'' ->
        Some $ Gen.App $ C.FloatDiv DoubleFloatRepr C.RNE
        (Gen.App $ C.FloatFromBV DoubleFloatRepr C.RNE num'')
        (Gen.App $ C.FloatFromBV DoubleFloatRepr C.RNE denom'')
  BasicConstComplex real imag ->
    error "mkBasicConst: complex numbers not yet supported"

-- | Make a pointer from a statically known location.
mkLocPointer :: MonadFail m => GoLoc s tp -> m (Gen.Expr Go s (PointerType tp))
mkLocPointer loc = case loc of
  GoLocRef ref -> return $ mkRefPointer ref
  GoLocArray arr ix -> return $ mkArrayOffsetPointer arr ix
  GoLocGlobal _glob ->
    fail "mkLocPointer: can't make pointer from global address"
  GoLocPointer ptr -> return ptr

-- | Make a pointer from a reference expression.
mkRefPointer :: Gen.Expr Go s (ReferenceType tp)
             -> Gen.Expr Go s (PointerType tp)
mkRefPointer ref = case exprType ref of
    ReferenceRepr repr ->
      Gen.App $ C.JustValue (NonNilPointerRepr repr) $ Gen.App $
      C.InjectVariant (PointerCtxRepr repr) (skipIndex baseIndex) ref

-- | Make a pointer from an array+offset.
mkArrayOffsetPointer :: Gen.Expr Go s (ArrayType tp)
                     -> Gen.Expr Go s NatType
                     -> Gen.Expr Go s (PointerType tp)
mkArrayOffsetPointer arr ix = case exprType arr of
  ReferenceRepr (VectorRepr repr) ->
    Gen.App $ C.JustValue (NonNilPointerRepr repr) $
    Gen.App $ C.InjectVariant (PointerCtxRepr repr) (nextIndex knownSize) $
    Gen.App $ C.MkStruct (ArrayOffsetCtxRepr repr) $ Ctx.empty :> arr :> ix

-- | Allocate a new reference with the given initial value and create
-- a pointer from it.
newRefPointer :: Gen.Expr Go s tp
              -> GoGenerator s ret (Gen.Expr Go s (PointerType tp))
newRefPointer value = mkRefPointer <$> Gen.newRef value

typeWidth :: Type -> Maybe PosNat
typeWidth (BasicType (BasicInt (Just i))) = intToPosNat i
typeWidth (BasicType (BasicUInt (Just i))) = intToPosNat i
typeWidth (BasicType (BasicFloat i)) = intToPosNat i
typeWidth _tp = Nothing

-- -- | Array element access.
-- arrayGet :: TypeRepr tp
--          -> Gen.Expr Go s NatType
--          -> Gen.Expr Go s (ArrayType tp)
--          -> GoGenerator s ret (Gen.Expr Go s tp)
-- arrayGet repr ix arr = do
--   vec <- Gen.readRef arr
--   return $ Gen.App $ C.VectorGetEntry repr vec ix

-- | Array element access with bounds checking.
arrayGetSafe :: TypeRepr tp
             -> Gen.Expr Go s NatType
             -> Gen.Expr Go s (ArrayType tp)
             -> GoGenerator s ret (Gen.Expr Go s tp)
arrayGetSafe repr ix arr = do
  vec <- Gen.readRef arr
  Gen.ifte' repr (Gen.App $ C.NatLt ix $ Gen.App $ C.VectorSize vec)
    (return $ Gen.App $ C.VectorGetEntry repr vec ix) $
    Gen.reportError $ Gen.App $ C.StringLit "array index out of bounds"

-- | Provide default values for begin, end, and capacity.
sliceValue :: Gen.Expr Go s (PointerType (ArrayType tp))
           -> Maybe (Gen.Expr Go s NatType) -- ^ begin
           -> Maybe (Gen.Expr Go s NatType) -- ^ end
           -> Maybe (Gen.Expr Go s NatType) -- ^ capacity
           -> GoGenerator s ret (Gen.Expr Go s (SliceType tp))
sliceValue arr_ptr begin end cap = do
  arr <- readPointer arr_ptr
  vec <- Gen.readRef arr
  let begin' = fromMaybe (Gen.App $ C.NatLit 0) begin
      end' = fromMaybe (Gen.App $ C.VectorSize vec) end
      cap' = fromMaybe (Gen.App $ C.NatSub end' begin') cap
  checkSliceRange begin' end' cap'
  let repr = arrayElementRepr $ exprType arr
  return $ Gen.App $ C.JustValue (NonNilSliceRepr repr) $ Gen.App $
    C.MkStruct (SliceCtxRepr repr) $
    Ctx.empty :> arr_ptr :> begin' :> end' :> cap'

checkSliceRange :: Gen.Expr Go s NatType -- ^ begin
                -> Gen.Expr Go s NatType -- ^ end
                -> Gen.Expr Go s NatType -- ^ capacity
                -> GoGenerator s ret ()
checkSliceRange begin end cap =
  Gen.ifte_ (Gen.App $ C.NatLt end begin)
  (do let msg = Gen.App $ C.StringLit "slice end < begin"
      Gen.addPrintStmt msg >> Gen.reportError msg) $
  Gen.ifte_ (Gen.App $ C.NatLe cap end)
  (do let msg = Gen.App $ C.StringLit "slice cap <= end"
      Gen.addPrintStmt msg >> Gen.reportError msg) $
  return ()

sliceValue' :: Gen.Expr Go s (PointerType (ArrayType tp))
            -> Int -- ^ begin
            -> Int -- ^ end
            -> Int -- ^ capacity
            -> GoGenerator s ret (Gen.Expr Go s (SliceType tp))
sliceValue' ptr begin end cap =
  trace "sliceValue'" $
  trace ("ptr:" ++ show ptr) $
  trace ("begin: " ++ show begin) $
  trace ("end: " ++ show end) $
  trace ("cap: " ++ show cap) $
  if end < begin then
    fail $ "sliceValue': invalid begin and end indices. begin=" ++
    show begin ++ ", end=" ++ show end
  else if cap <= end then
    fail $ "sliceValue: end index exceeds capacity"
  else do
    let repr = arrayElementRepr $ pointerElementRepr $ exprType ptr
    return $ Gen.App $ C.JustValue (NonNilSliceRepr repr) $
      Gen.App $ C.MkStruct (SliceCtxRepr repr) $
      Ctx.empty :> ptr :> intNat begin :> intNat end :> intNat cap
