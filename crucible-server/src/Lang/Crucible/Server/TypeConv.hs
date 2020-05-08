-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.TypeConv
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Operations to translate between the protocol-buffer represntation
-- of types and the internal Crucible representation.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.Crucible.Server.TypeConv where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import Control.Lens
import Control.Monad
import qualified Data.Sequence as Seq
import Data.Foldable( toList )

import Data.HPB
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some

import What4.Interface

import Lang.Crucible.FunctionName
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Types

import qualified Lang.Crucible.Proto as P



getTail :: MonadFail m => String -> Seq a -> m (Seq a, a)
getTail msg s =
  case Seq.viewr s of
    Seq.EmptyR -> fail msg
    h Seq.:> t -> return (h, t)

------------------------------------------------------------------------
-- Positions

fromProtoPos :: P.Position -> ProgramLoc
fromProtoPos p =
  case p^.P.position_code of
    P.InternalPos ->
      let nm = p^.P.position_functionName
       in mkProgramLoc (functionNameFromText nm) InternalPos
    P.SourcePos ->
      let path = p^.P.position_path
          line = fromIntegral $ p^.P.position_line
          col  = fromIntegral $ p^.P.position_col
          nm   = p^.P.position_functionName
       in mkProgramLoc (functionNameFromText nm) $ SourcePos path line col
    P.BinaryPos ->
      let path = p^.P.position_path
          addr = p^.P.position_addr
          nm   = p^.P.position_functionName
       in mkProgramLoc (functionNameFromText nm) $ BinaryPos path addr
    P.OtherPos ->
      let str  = p^.P.position_value
          nm   = p^.P.position_functionName
       in mkProgramLoc (functionNameFromText nm) $ OtherPos str

toProtoPos :: ProgramLoc -> P.Position
toProtoPos pl =
  case plSourceLoc pl of
    InternalPos ->
      mempty & P.position_code .~ P.InternalPos
             & P.position_functionName .~ functionName (plFunction pl)
    SourcePos path line col ->
      mempty & P.position_code .~ P.SourcePos
             & P.position_path .~ path
             & P.position_line .~ fromIntegral line
             & P.position_col  .~ fromIntegral col
             & P.position_functionName .~ functionName (plFunction pl)
    BinaryPos path addr ->
      mempty & P.position_code .~ P.BinaryPos
             & P.position_path .~ path
             & P.position_addr .~ fromIntegral addr
             & P.position_functionName .~ functionName (plFunction pl)
    OtherPos str ->
      mempty & P.position_code  .~ P.OtherPos
             & P.position_value .~ str

------------------------------------------------------------------------
-- Type conversion

-- | Convert protocol var type to Interface type.
varTypeFromProto :: MonadFail m => P.VarType -> m (Some BaseTypeRepr)
varTypeFromProto tp =
  case tp^.P.varType_id of
    P.BitvectorVarType -> do
      let wv = tp^.P.varType_width
      when (wv == 0) $ do
        fail $ "Bitvector variables must have a positive width."
      case someNat wv of
        Just (Some w) | Just LeqProof <- isPosNat w -> do
          return $ Some (BaseBVRepr w)
        _ -> error "Illegal type width"
    P.BoolVarType    -> return $ Some BaseBoolRepr
    P.IntegerVarType -> return $ Some BaseIntegerRepr
    P.RealVarType    -> return $ Some BaseRealRepr


-- Given a protocol vartype, wrap a "Vector" type operator
-- for each dimension on top of the base type
crucibleTypeFromProtoVarType :: MonadFail m => P.VarType -> m (Some TypeRepr)
crucibleTypeFromProtoVarType tp = do
   let dims = tp^.P.varType_dimensions
   Some vtp <- varTypeFromProto tp
   let basetp = baseToType vtp
   wrapVectors (toList dims) (Some basetp)

 where wrapVectors [] basetp = return basetp
       wrapVectors (_:xs) basetp = do
           Some t <- wrapVectors xs basetp
           return (Some (VectorRepr t))

------------------------------------------------------------------------
-- Converting from a protocol buffer type.

fromProtoTypeSeq :: MonadFail m => Seq P.CrucibleType -> m (Some CtxRepr)
fromProtoTypeSeq s0 = do
  case Seq.viewr s0 of
    Seq.EmptyR -> return (Some Ctx.empty)
    s Seq.:> tp -> do
      Some ctx <- fromProtoTypeSeq s
      Some rep <- fromProtoType tp
      return $ Some $ ctx Ctx.:> rep

fromProtoType :: MonadFail m => P.CrucibleType -> m (Some TypeRepr)
fromProtoType tp = do
  let params = tp^.P.crucibleType_params
  case tp^.P.crucibleType_id of
    P.UnitType -> do
      return $ Some UnitRepr
    P.BoolType -> do
      return $ Some BoolRepr
    P.NatType  -> do
      return $ Some NatRepr
    -- TODO: Eliminate this type
    P.PosNatType -> do
      return $ Some NatRepr
    P.IntegerType -> do
      return $ Some IntegerRepr
    P.RealType -> do
      return $ Some RealValRepr
    P.ComplexType -> do
      return $ Some ComplexRealRepr
    P.BitvectorType -> do
      case someNat (tp^.P.crucibleType_width) of
        Just (Some w) | Just LeqProof <- isPosNat w -> return $ Some $ BVRepr w
        _ -> error "Could not parse bitwidth."

    P.HalfFloatType -> do
      return $ Some $ FloatRepr HalfFloatRepr
    P.SingleFloatType -> do
      return $ Some $ FloatRepr SingleFloatRepr
    P.DoubleFloatType -> do
      return $ Some $ FloatRepr DoubleFloatRepr
    P.QuadFloatType -> do
      return $ Some $ FloatRepr QuadFloatRepr
    P.X86_80FloatType -> do
      return $ Some $ FloatRepr X86_80FloatRepr
    P.DoubleDoubleFloatType -> do
      return $ Some $ FloatRepr DoubleDoubleFloatRepr

    P.CharType -> do
      return $ Some CharRepr
    P.StringType -> do
      return $ Some (StringRepr UnicodeRepr)
    P.FunctionHandleType -> do
      (args, ret) <- getTail "Missing return type." params
      Some arg_ctx <- fromProtoTypeSeq args
      Some ret_tp  <- fromProtoType ret
      return $ Some $ FunctionHandleRepr arg_ctx ret_tp

    P.MaybeType -> do
      when (Seq.length params /= 1) $ do
        fail $ "Expected single parameter to Maybe."
      Some etp <- fromProtoType (params `Seq.index` 0)
      return $ Some $ MaybeRepr etp
    P.VectorType -> do
      when (Seq.length params /= 1) $ do
        fail $ "Expected single parameter to Vector"
      Some etp <- fromProtoType (params `Seq.index` 0)
      return $ Some $ VectorRepr etp
    P.StructType -> do
      Some ctx <- fromProtoTypeSeq params
      return $ Some $ StructRepr ctx
    P.WordMapType -> do
      when (Seq.length params /= 1) $ do
        fail $ "Expected single parameter to WordMap"
      Some etp <- fromProtoType (params `Seq.index` 0)
      case asBaseType etp of
        AsBaseType bt ->
          case someNat (tp^.P.crucibleType_width) of
            Just (Some w) | Just LeqProof <- isPosNat w ->
                return $ Some $ WordMapRepr w bt
            _ -> error $ unwords ["Invalid word map type: ", show etp]
        _ -> error "Could not parse bitwidth."

    P.StringMapType -> do
      when (Seq.length params /= 1) $ do
        fail $ "Expected single parameter to StringMapType"
      Some etp <- fromProtoType (params `Seq.index` 0)
      return $ Some $ StringMapRepr etp

------------------------------------------------------------------------
-- Generating a protocol buffer type.

mkType :: P.CrucibleTypeId -> P.CrucibleType
mkType tp = mempty & P.crucibleType_id .~ tp

mkType1 :: P.CrucibleTypeId -> TypeRepr tp -> P.CrucibleType
mkType1 tp param = mkType tp & setTypeParams (Seq.singleton (mkProtoType param))

setTypeParams :: Seq P.CrucibleType -> P.CrucibleType -> P.CrucibleType
setTypeParams params = P.crucibleType_params .~ params

ctxReprToSeq :: CtxRepr ctx -> Seq (Some TypeRepr)
ctxReprToSeq c =
  case Ctx.viewAssign c of
    Ctx.AssignEmpty -> Seq.empty
    Ctx.AssignExtend ctx r -> ctxReprToSeq ctx Seq.|> Some r

mkProtoTypeSeq :: CtxRepr ctx -> Seq P.CrucibleType
mkProtoTypeSeq c = (\(Some tp) -> mkProtoType tp) <$> ctxReprToSeq c

mkProtoType :: TypeRepr tp -> P.CrucibleType
mkProtoType tpr =
  case tpr of
    UnitRepr ->
      mkType P.UnitType
    BoolRepr ->
      mkType P.BoolType
    NatRepr ->
      mkType P.NatType
    IntegerRepr ->
      mkType P.IntegerType
    RealValRepr ->
      mkType P.RealType
    ComplexRealRepr ->
      mkType P.ComplexType
    BVRepr w ->
      mkType P.BitvectorType & P.crucibleType_width .~ fromIntegral (widthVal w)
    FloatRepr repr -> mkType c_type
      where c_type = case repr of
                       HalfFloatRepr   -> P.HalfFloatType
                       SingleFloatRepr -> P.SingleFloatType
                       DoubleFloatRepr -> P.DoubleFloatType
                       QuadFloatRepr   -> P.QuadFloatType
                       X86_80FloatRepr -> P.X86_80FloatType
                       DoubleDoubleFloatRepr -> P.DoubleDoubleFloatType
    CharRepr ->
      mkType P.CharType
    StringRepr UnicodeRepr ->
      mkType P.StringType
    FunctionHandleRepr args ret -> do
      let params = mkProtoTypeSeq args Seq.|> mkProtoType ret
      mkType P.FunctionHandleType & setTypeParams params

    MaybeRepr  tp -> mkType1 P.MaybeType tp
    VectorRepr tp -> mkType1 P.VectorType tp
    WordMapRepr w tp ->
       -- FIXME, better handling of base types
       mkType1 P.WordMapType (baseToType tp) & P.crucibleType_width .~ fromIntegral (widthVal w)

    StructRepr ctx ->
      mkType P.StructType & setTypeParams (mkProtoTypeSeq ctx)

    StringMapRepr tp -> mkType1 P.StringMapType tp

    _ -> error $ unwords ["crucible-server: type not yet supported", show tpr]
