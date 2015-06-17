{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.AutoMatch.JVM where

import qualified Language.JVM.Parser as JVM

--import qualified Verifier.Java.Codebase as CB hiding (lookupClass)
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
import SAWScript.AutoMatch

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
         JVM.ArrayType t    -> Array <$> jssTypeToStdType t
         JVM.BooleanType    -> Just Bool
         JVM.ByteType       -> Just UChar -- TODO: not sure about this equivalence...
         JVM.CharType       -> Just Char
         JVM.ClassType _str -> Nothing
         JVM.DoubleType     -> Just Double
         JVM.FloatType      -> Just Float
         JVM.IntType        -> Just Int
         JVM.LongType       -> Just Long
         JVM.ShortType      -> Just Short

printMatchesJVM :: BuiltinContext -> Options -> JSS.Class -> JSS.Class -> {- JavaSetup () -> -} IO ()
printMatchesJVM bic opts leftClass rightClass {- _setup -} = do
   leftDecls  <- getDeclsJVM bic opts leftClass
   rightDecls <- getDeclsJVM bic opts rightClass
   print =<< interactIO (matchModules leftDecls rightDecls)
