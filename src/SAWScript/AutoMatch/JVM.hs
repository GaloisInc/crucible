{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.AutoMatch.JVM where

import qualified Language.JVM.Parser as JVM

import qualified Verifier.Java.Simulator as JSS hiding (lookupClass)
--import Verifier.Java.SAWBackend

--import Verifier.SAW.Recognizer
--import Verifier.SAW.FiniteValue
--import Verifier.SAW.SCTypeCheck
--import Verifier.SAW.SharedTerm

--import qualified SAWScript.CongruenceClosure as CC

--import SAWScript.JavaExpr
--import SAWScript.JavaMethodSpec
--import SAWScript.JavaMethodSpecIR

import SAWScript.Builtins
import SAWScript.Options
--import SAWScript.Proof
--import SAWScript.TypedTerm
--import SAWScript.Utils
--import SAWScript.Value as SS

--import SAWScript.JavaBuiltins

--import Data.IORef
--import Data.Maybe

import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

import Control.Monad
import Data.Maybe

getDeclsJVM :: BuiltinContext -> Options -> JSS.Class -> {- JavaSetup () -> -} IO (String,[Decl])
getDeclsJVM _bic _opts cls {- _setup -} =

   return . (JSS.className cls,) . catMaybes . for (JSS.classMethods cls) $ \method ->
      do returnType <- jssTypeToStdType =<< JSS.methodReturnType method
         argTypes <- mapM jssTypeToStdType $ JSS.methodParameterTypes method
         let argIndices = map (JSS.localIndexOfParameter method) [0 .. length argTypes - 1]
         tableEntries <- forM argIndices $ JSS.lookupLocalVariableByIdx method 0
         let args = zipWith Arg (map JSS.localName tableEntries) argTypes
         return $ Decl (JSS.methodName method) returnType args

   where

      jssTypeToStdType = \case
         JVM.ArrayType _    -> Nothing -- TODO: Handle array types
         JVM.BooleanType    -> Just $ TCon (TC TCBit) []
         JVM.ByteType       -> Just $ bitSeqType 8
         JVM.CharType       -> Just $ bitSeqType 16 -- TODO: Not sure about this equivalence
         JVM.ClassType _str -> Nothing -- TODO: Support classes as records?
         JVM.DoubleType     -> Nothing -- We don't support floating point types
         JVM.FloatType      -> Nothing -- We don't support floating point types
         JVM.IntType        -> Just $ bitSeqType 32
         JVM.LongType       -> Just $ bitSeqType 64
         JVM.ShortType      -> Just $ bitSeqType 16
