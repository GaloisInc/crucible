{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module CrucibleProtobufTrace.What4Encodings (
    encodeProto,
    expr_id,
    encodeLabeledPred,
    SymExprWrapper(SymExprWrapper),
)
where

import qualified CrucibleProtobufTrace.ProtoDefs.SymExpr as ProtoS
import qualified CrucibleProtobufTrace.ProtoDefs.Common as ProtoC

import           CrucibleProtobufTrace.Encoding (ProtoEncoding, encodeProto)
import           CrucibleProtobufTrace.GlobalEncodingState (getOutDirRef)

import           Data.ProtoLens (defMessage)
import           Data.ProtoLens.Prism ( (#), _Just )
import           Lens.Micro ((&), (.~))
import           What4.Expr (ExprBuilder, FloatIEEE, Flags, FloatReal, FloatUninterpreted, Expr)
import           What4.Expr.Builder (exprMaybeId, exprType, SymExpr)
import           Data.Parameterized.Nonce (Nonce (indexValue))
import qualified What4.ProgramLoc as What4
import           What4.ProgramLoc
import           What4.BaseTypes (BaseTypeRepr (..))
import           Data.Word (Word64)
import           What4.BaseTypes (BaseBVType, BaseIntegerType, NatRepr (natValue), BaseBoolType, BaseFloatType, FloatingPointPrecision)
import           What4.FunctionName (functionName)
import           What4.Interface (SymNat, natToIntegerPure, BaseTypeRepr (BaseBVRepr, BaseBoolRepr, BaseIntegerRepr, BaseFloatRepr), IsExpr (printSymExpr, asBV), asConstantPred, asInteger, FloatPrecision, asFloat, asRational)

import qualified Text.Printf (printf)
import qualified System.Directory (doesFileExist, doesDirectoryExist, createDirectory)
import           System.FilePath ((</>))
import           What4.Serialize.Printer (Result(resSExpr, resFreeVarEnv, resSymFnEnv), printSExpr, Config (Config), serializeExprWithConfig, jsonEncodeFreeVarEnv, jsonEncodeFreeSymFnEnv)
import           Data.Text (unpack, Text, pack)
import           What4.LabeledPred (LabeledPred (LabeledPred))
import qualified Text.Printf as Text
import           Data.Sequence (singleton)
import           Data.BitVector.Sized
import           Numeric (showHex)
import           LibBF (bfToString, forceExp, showFrac, showFree, showFreeMin)

-- SymExpr Wrapper
newtype SymExprWrapper sym t = SymExprWrapper (SymExpr sym t)

instance ProtoEncoding What4.Position ProtoC.Position where
    encodeProto (SourcePos file line column) = return $
        defMessage
            & ProtoC.maybe'source .~ _Just # (
                defMessage
                    & ProtoC.file .~ file
                    & ProtoC.line .~ (fromIntegral line)
                    & ProtoC.column .~ (fromIntegral column)
                )
    encodeProto (BinaryPos filename addr) = return $
        defMessage
            & ProtoC.maybe'binary .~ _Just # (
                defMessage
                    & ProtoC.file .~ filename
                    & ProtoC.address .~ (fromIntegral addr)
                )
    encodeProto (OtherPos desc) = return $
        defMessage
            & ProtoC.maybe'other .~ _Just # (
                defMessage
                    & ProtoC.descriptor .~ desc
                )
    encodeProto (InternalPos) = return $
        defMessage
            & ProtoC.maybe'internal .~ _Just # defMessage

instance ProtoEncoding (BaseTypeRepr tp) ProtoS.ExpressionSort where
    encodeProto (BaseBVRepr w) = return $
        defMessage
            & ProtoS.maybe'sortBv .~ _Just # (
                    defMessage
                        & ProtoS.bits .~ (fromIntegral $ natValue w)
                )
    encodeProto (BaseBoolRepr) = return $
        defMessage
            & ProtoS.maybe'sortBool .~ _Just # defMessage

    encodeProto (BaseIntegerRepr) = return $
        defMessage
            & ProtoS.maybe'sortInt .~ _Just # defMessage

    encodeProto _ = error "unsupported sort"

instance ProtoEncoding What4.ProgramLoc ProtoC.ProgramLoc where
    encodeProto loc = do
        encoded_pos <- (encodeProto $ plSourceLoc loc)
        return $ defMessage
            & ProtoC.functionName .~ (functionName (plFunction loc))
            & ProtoC.position .~ encoded_pos

instance ProtoEncoding (Maybe What4.ProgramLoc) ProtoC.MaybeProgramLoc where
    encodeProto (Just loc) = do
        encoded_loc <- encodeProto loc
        return $ defMessage & ProtoC.programLoc .~ encoded_loc

    encodeProto Nothing = return $ defMessage & ProtoC.missing .~ defMessage

instance ProtoEncoding (Nonce s t) ProtoS.ExpressionID where
  encodeProto nonce = return
    $ defMessage
        & ProtoS.maybe'serializedId .~ _Just # (indexValue nonce)

expr_id :: (sym ~ (ExprBuilder s t st)) => SymExpr sym val -> IO ProtoS.ExpressionID
expr_id expr = do
    out_dir <- getOutDirRef
    case (exprMaybeId expr) of
            Just id_ -> do
                let dirPath = out_dir </> "expressions"
                let filePath = dirPath </> Text.Printf.printf "expr_%s" (show (indexValue id_))
                System.Directory.doesDirectoryExist dirPath >>= \x ->
                    case x of
                        True -> return ()
                        False -> System.Directory.createDirectory dirPath

                System.Directory.doesFileExist filePath >>= \exists ->
                    case exists of
                        False -> do
                            let cfg = Config True True
                            let serialized_result = serializeExprWithConfig cfg expr
                            putStrLn $ Text.printf "Serializing to %s" filePath
                            let freevars =      jsonEncodeFreeVarEnv $ resFreeVarEnv serialized_result
                            let freefuncs =     jsonEncodeFreeSymFnEnv $ resSymFnEnv serialized_result
                            let serializedenv = Text.printf "{\"free_vars\": %s, \"free_funcs\": %s}" freevars freefuncs
                            let serialized = printSExpr (singleton serializedenv) (resSExpr serialized_result)
                            writeFile filePath (unpack serialized)
                        _ -> return ()
                return $ defMessage & ProtoS.maybe'serializedId .~ _Just # (indexValue id_)
            Nothing -> case (exprType expr) of

                What4.Interface.BaseBoolRepr -> return
                    $ defMessage
                        & ProtoS.maybe'boolConst .~ _Just # case (asConstantPred expr) of
                            Just x -> defMessage & ProtoS.value .~ x
                            Nothing -> error ("expr_id: expression has no ID: " ++ (show $ printSymExpr expr))

                What4.Interface.BaseIntegerRepr -> return
                    $ defMessage
                        & ProtoS.maybe'intConst .~ _Just # case (asInteger expr) of
                            Just x -> defMessage & ProtoS.value .~ (fromIntegral x)
                            Nothing -> error ("expr_id: expression has no ID: " ++ (show $ printSymExpr expr))

                What4.Interface.BaseBVRepr w -> return
                    $ defMessage
                        & ProtoS.maybe'bvConst .~ _Just # case (asBV expr) of
                            Just (BV x) -> defMessage
                                         & ProtoS.hexValue .~ (pack $ showHex x "")
                                         & ProtoS.width .~ (fromIntegral $ natValue w)
                            Nothing -> error ("expr_id: expression has no ID: " ++ (show $ printSymExpr expr))
                What4.Interface.BaseFloatRepr fpp -> return
                    $ defMessage
                        & ProtoS.maybe'floatConst .~ _Just # case (What4.Interface.asFloat expr) of
                            Just x -> defMessage
                                        & ProtoS.value .~ (pack $ show x)
                            Nothing -> error ("expr_id: expression has no ID: " ++ (show $ printSymExpr expr))
                _ -> error ("expr_id: expression has unsupported type: " ++ (show $ printSymExpr expr))

instance (sym ~ (ExprBuilder s t st)) => ProtoEncoding (SymExprWrapper sym BaseBoolType) ProtoS.BoolExpression where
    encodeProto (SymExprWrapper expr) = do
        _id <- expr_id expr
        return $ defMessage
                    & ProtoS.id .~ _id
                    & ProtoS.boolType .~ defMessage

instance (sym ~ (ExprBuilder s t st)) => ProtoEncoding (SymExprWrapper sym BaseIntegerType) ProtoS.IntExpression where
    encodeProto (SymExprWrapper expr) = do
        _id <- expr_id expr
        return $ defMessage
                    & ProtoS.id .~ _id
                    & ProtoS.intType .~ defMessage


--  FUCK IT, I have no fucking clue how to do floats

-- instance (sym ~ ExprBuilder s t (Flags FloatIEEE)) => ProtoEncoding (SymExprWrapper sym (SymInterpretedFloatType sym fi)) ProtoS.FloatExpression where
--     encodeProto (SymExprWrapper expr) = do
--         _id <- expr_id expr
--         return $ defMessage
--                     & ProtoS.id .~ _id
--                     & ProtoS.floatType .~ defMessage

instance (sym ~ (ExprBuilder s t str)) => ProtoEncoding (SymNat sym) ProtoS.IntExpression where
    encodeProto n = encodeProto (SymExprWrapper (natToIntegerPure n))



instance (sym ~ (ExprBuilder s t st)) => ProtoEncoding (SymExprWrapper sym (BaseBVType w)) ProtoS.BVExpression where
    encodeProto (SymExprWrapper expr) = do
        _id <- expr_id expr
        return $ defMessage
            & ProtoS.id .~ _id
            & ProtoS.bvType .~ (
                defMessage
                    & (ProtoS.bits .~ x)
            )
        where
            x :: Word64
            x = case (exprType expr) of
                What4.Interface.BaseBVRepr w -> fromIntegral $ natValue w

encodeLabeledPred :: (sym ~ (ExprBuilder s t st)) => LabeledPred (SymExpr sym BaseBoolType) msg -> (msg -> Text) -> IO ProtoS.LabeledPredicate
encodeLabeledPred (LabeledPred pred_ msg) encMsg = do
    _id <- expr_id pred_
    return $ defMessage
        & ProtoS.predicateExpressionId .~ _id
        & ProtoS.message .~ (encMsg msg)

