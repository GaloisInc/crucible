{- |
Module           : Lang.Crucible.JVM.Class
Description      : Translation of JVM AST into Crucible control-flow graph
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : huffman@galois.com
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -haddock #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Lang.Crucible.JVM.Class where

import Data.Maybe (maybeToList)
import Data.Semigroup(Semigroup(..),(<>))
import Control.Monad.State.Strict
import Control.Monad.ST
import Control.Monad.Reader
import Control.Lens hiding (op, (:>))
import Data.Int (Int32)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Vector(Vector)
import qualified Data.Vector as V
import Data.String (fromString)
import Data.Text (Text)
import Data.Word


-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr as NR


-- jvm-parser
import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

-- crucible
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Backend
import           Lang.Crucible.Panic

-- crucible-jvm
import           Lang.Crucible.JVM.Types
import           Lang.Crucible.JVM.ClassRefs
import           Lang.Crucible.JVM.Generator

-- what4
import           What4.ProgramLoc (Position(InternalPos))


import Debug.Trace


{-

The functions in this module work with the values of type JVMClass and JVMClassTable
to maintain the dynamic information related to the class table, including the
initialization status and the values of the static variables.

-}


---------------------------------------------------------------------------------
--
-- | Runtime representation of class information (i.e. JVMClass)
--

-- | initialization status values
notStarted, started, initialized, erroneous :: JVMInitStatus f 
notStarted   = App $ BVLit knownRepr 0
started      = App $ BVLit knownRepr 1
initialized  = App $ BVLit knownRepr 2
erroneous    = App $ BVLit knownRepr 3


-- | Expression for the class name
classNameExpr :: J.Class -> JVMString s
classNameExpr c = App $ TextLit $ fromString (J.unClassName (J.className c))

methodKeyNameExpr :: J.MethodKey -> JVMString s
methodKeyNameExpr c = App $ TextLit $ fromString (J.methodKeyName c)


-- | Method table
type JVMMethodTable s = Expr JVM s JVMMethodTableType


emptyMethodTable :: JVMMethodTable s
emptyMethodTable = App (EmptyStringMap knownRepr)

-- add a function handle to the method table
insertMethodTable :: (JVMString s, Expr JVM s AnyType) -> JVMMethodTable s -> JVMMethodTable s
insertMethodTable (s, v) sm = App (InsertStringMapEntry knownRepr sm s (App $ JustValue knownRepr v))

--
-- | update the jvm class table to include an entry for the specified class
--
-- This will also initalize the superclass (if present and necessary)
--
initializeJVMClass :: J.Class
                       -> JVMGenerator h s t (JVMClass s)
initializeJVMClass c  = do
  ctx <- gets jsContext

  let className  = classNameExpr c

  -- this class has a superclass, that we know something about,
  -- find the JVMClass expression associated with it, creating this
  -- data structure if it hasn't already been created
  let superClassM | Just cn  <- J.superClass c,
                    Just cls <- Map.lookup cn (classTable ctx) = do
                               val <- getJVMClass cls
                               return $ App $ JustValue knownRepr val
                  | otherwise = return $ App $ NothingValue knownRepr 

  superClass <- superClassM
  
  -- find available handles for the methods in the class
  let handles    = [ mhi | m <- J.classMethods c,
                           mhi <- maybeToList $ Map.lookup (J.className c, J.methodKey m)
                                  (methodHandles ctx) ]

  let methTable0 = map (\(JVMHandleInfo m h) ->
                           (methodKeyNameExpr m, App (PackAny (handleType h) (App (HandleLit h))))) handles
                  
  let methTable  = foldr insertMethodTable emptyMethodTable methTable0

  -- construct the data structure
  let str        = App (RollRecursive knownRepr knownRepr
                     $ App $ MkStruct knownRepr
                         (Ctx.empty `Ctx.extend` className
                                   `Ctx.extend` notStarted
                                   `Ctx.extend` superClass
                                   `Ctx.extend` methTable))

  -- update the dynamic class table
  let gv         = dynamicClassTable ctx                   
  sm <- readGlobal gv
  let expr = App $ InsertStringMapEntry knownRepr sm className (App $ JustValue knownRepr str)
  writeGlobal gv expr
  return str

-- Accessors 

getJVMClassName :: JVMClass s -> Expr JVM s StringType
getJVMClassName ct = App (GetStruct (App $ UnrollRecursive knownRepr knownRepr ct) Ctx.i1of4 knownRepr)

getJVMClassInitStatus :: JVMClass s -> JVMInitStatus s
getJVMClassInitStatus ct = App (GetStruct (App $ UnrollRecursive knownRepr knownRepr ct) Ctx.i2of4 knownRepr)

getJVMClassSuper :: JVMClass s -> Expr JVM s (MaybeType JVMClassType)
getJVMClassSuper ct = App (GetStruct (App $ UnrollRecursive knownRepr knownRepr ct) Ctx.i3of4 knownRepr)

getJVMClassMethodTable :: JVMClass s -> JVMMethodTable s
getJVMClassMethodTable ct = App (GetStruct (App $ UnrollRecursive knownRepr knownRepr ct) Ctx.i4of4 knownRepr)

------------------------------------------------------------------------
-- Functions for working with the JVM class table

-- | Access the class table entry of a given class in the dynamic class table
-- If this class table entry has not yet been defined, define it
-- (Note: this function does not call the class initializer on the static variables,
-- that is done separately.)
getJVMClass :: J.Class -> JVMGenerator h s ret (JVMClass s)
getJVMClass c = do
  ctx <- gets jsContext
  let gv = (dynamicClassTable ctx)
  sm <- readGlobal gv
  let cn = classNameExpr c
  let lu = App $ LookupStringMapEntry knownRepr sm cn
  caseMaybe lu knownRepr
    MatchMaybe 
      { onNothing = initializeJVMClass c                     
      , onJust    = return
      }

-- | lookup the data structure associated with a class
getJVMClassByName ::
  J.ClassName -> JVMGenerator h s ret (Expr JVM s JVMClassType)
getJVMClassByName name = do
  lookupClass name >>= getJVMClass

      
-- | Access the initialization status of the class in the dynamic class table
-- If the class table entry for this class has not yet been defined, define it
getInitStatus :: J.Class -> JVMGenerator h s ret (JVMInitStatus s)
getInitStatus c = getJVMClassInitStatus <$> getJVMClass c

-- | Update the initialization status of the class in the dynamic class table
setInitStatus :: J.Class -> JVMInitStatus s -> JVMGenerator h s ret ()
setInitStatus c status = do
  ctx <- gets jsContext
  let gv = dynamicClassTable ctx
  sm <- readGlobal gv
  let name  = classNameExpr c
  let entry = App $ LookupStringMapEntry knownRepr sm name
  writeGlobal gv (App $ InsertStringMapEntry knownRepr sm name entry)

----------------------------------------------------------------------
-- | Static Fields and Methods
--

getStaticFieldValue :: J.FieldId -> JVMGenerator h s ret (JVMValue s)
getStaticFieldValue fieldId = do
      let cls = J.fieldIdClass fieldId
      ctx <- gets jsContext
      initializeClass cls
      case Map.lookup (J.fieldIdClass fieldId, J.fieldIdName fieldId) (staticFields ctx) of
        Just glob -> do
          r <- readGlobal glob
          fromJVMDynamic (J.fieldIdType fieldId) r
        Nothing -> 
          jvmFail $ "getstatic: field " ++ J.fieldIdName fieldId ++ " not found"

-- | Update the value of a static field
setStaticFieldValue :: J.FieldId -> JVMValue s -> JVMGenerator h s ret ()
setStaticFieldValue  fieldId val = do
    ctx <- gets jsContext
    let cName = J.fieldIdClass fieldId 
    case Map.lookup (cName, J.fieldIdName fieldId) (staticFields ctx) of
         Just glob -> do
           writeGlobal glob (valueToExpr val)
         Nothing -> 
           jvmFail $ "putstatic: field " ++ J.unClassName cName
                     ++ "." ++ (J.fieldIdName fieldId) ++ " not found"

-- | Look up a method in the static method table (i.e. methodHandles)
getStaticMethod :: J.ClassName -> J.MethodKey -> JVMGenerator h s ret JVMHandleInfo
getStaticMethod className methodKey = do
   ctx <- gets jsContext
   let mhandle = Map.lookup (className, methodKey) (methodHandles ctx)
   case mhandle of
      Nothing -> jvmFail $ "getStaticMethod: method " ++ show methodKey ++ " in class "
                               ++ show className ++ " not found"
      Just handle -> return handle
      
------------------------------------------------------------------------
-- | Class Initialization
-- 
-- initialize the static fields of a class (if they haven't already been
-- initialized)
-- make sure that the jvm class table entry for the class has been initialized


-- REVISIT: it may make sense for this to be dynamic
skipInit :: J.ClassName -> Bool
skipInit cname = cname `elem` [ "java/lang/Object"
                              , "java/lang/Class"
                              , "java/lang/System"
                              , "java/io/Reader"
                              , "java/io/InputStreamReader"
                              ]                 

skipClinit :: J.ClassName -> Bool
skipClinit cname = cname `elem` []


initializeClass :: forall h s ret . J.ClassName -> JVMGenerator h s ret ()
initializeClass name = unless (skipInit name) $ do 

  c <- lookupClass name
  status <- getInitStatus c
  
  let ifNotStarted = do
        
      -- note that we are starting
      setInitStatus c started

      -- make sure superclass has been initialized
      maybe (return ()) initializeClass (J.superClass c)
      
      -- initialize all of the static fields with default values
      mapM_ (initializeStaticField name) $ J.classFields c

      -- run the static initializer for the class (if present)
      unless (skipClinit name) $ do
        let clinit = (J.MethodKey "<clinit>" [] Nothing)
        case c `J.lookupMethod` clinit  of
          Just _ -> do
            handle <- getStaticMethod name clinit
            callJVMInit handle
          Nothing -> return ()

      -- mark that we have completed
      setInitStatus c initialized

  ifte_ (App $ BVEq knownRepr status notStarted) ifNotStarted (return ())
  -- TODO: if init status is Erroneous createAndThrow "java/lang/NoClassDefFoundError"



-- | Call a JVM static initialer, such as <init>
-- These methods do not take arguments or produce results so they
-- do not work with the stack. As a result we can call these methods
-- in the JVMGenerator monad

callJVMInit :: JVMHandleInfo -> JVMGenerator h s ret ()
callJVMInit (JVMHandleInfo _methodKey handle) =
  do let argTys = handleArgTypes handle
         retTy  = handleReturnType handle
     case (testEquality argTys (knownRepr :: Ctx.Assignment TypeRepr Ctx.EmptyCtx),
           testEquality retTy  (knownRepr :: TypeRepr UnitType)) of
       (Just Refl, Just Refl) -> do
         _ <- call (App (HandleLit handle)) knownRepr
         return ()
       (_,_) -> error "Internal error: can only call functions with no args/result"



-- | Compute the initial value of a field based on its
-- static initializer and/or type
initialFieldValue :: J.ClassName -> J.Field -> JVMValue s
initialFieldValue name f = 
  case J.fieldConstantValue f of
     Just (J.Double v) ->
        (DValue (App (DoubleLit v)))
     Just (J.Float v) ->
        (FValue (App (FloatLit v)))
     Just (J.Integer v) ->
        (IValue (App (BVLit knownRepr (toInteger v))))
     Just (J.Long v) ->
        (LValue (App (BVLit knownRepr (toInteger v))))
     Just (J.String v) ->
        RValue  (App (NothingValue knownRepr))
        -- TODO: actually initialize constant strings
     Nothing ->
        defaultValue (J.fieldType f)
     Just tp -> error $ "Unsupported field type" ++ show tp

initializeStaticField :: J.ClassName -> J.Field -> JVMGenerator h s ret ()
initializeStaticField name f = do
  when (J.fieldIsStatic f) $ do
      let fieldId = J.FieldId name (J.fieldName f) (J.fieldType f)
      setStaticFieldValue fieldId (initialFieldValue name f)

      
------------------------------------------------------------------------

-- | Search for a method handle using the dynamic class information
findDynamicMethod :: JVMClass s 
                  -> J.MethodKey
                  -> JVMGenerator h s ret (Expr JVM s AnyType)
findDynamicMethod dcls methodKey = do
  let dmeth = App (TextLit   (fromString (J.methodKeyName methodKey)))
  traceM $ "looking for dynamic method " ++ J.methodKeyName methodKey
  ctx <- gets jsContext
  sm <- readGlobal (dynamicClassTable ctx)

  -- construct a while loop in the output that searches for the
  -- method handle 
  classTypeReg <- newReg dcls
  methodReg    <- newReg $ App $ NothingValue knownRepr

  let loopbody = do
        classType <- readReg classTypeReg
        let className = getJVMClassName classType
        let lu = App (LookupStringMapEntry knownRepr sm className)
        _ <- caseMaybe lu UnitRepr
               MatchMaybe
               { onNothing = return (App EmptyApp)
               , onJust    =  \ct -> do
                   let sm2 = getJVMClassMethodTable ct
                   let lu2 = App (LookupStringMapEntry knownRepr sm2 dmeth)
                   caseMaybe lu2 knownRepr
                     MatchMaybe
                     { onNothing = do
                         let msuper = getJVMClassSuper ct
                         caseMaybe msuper knownRepr
                            MatchMaybe
                            { onNothing = return (App EmptyApp)
                            , onJust    = \ct2 -> assignReg classTypeReg ct2 >> return (App EmptyApp)
                            }
                     , onJust = \ m -> do
                         assignReg methodReg (App $ JustValue knownRepr m)
                         return (App EmptyApp)
                     } 
               }
        return ()
  while (InternalPos, readReg methodReg >>= gen_isNothing)
        (InternalPos, loopbody)

  v <- readReg methodReg
  assertedJustExpr v (App $ TextLit "NoSuchMethodError")  

------------------------------------------------------------------------

-- | Test whether the given class is a subclass of the classname
isSubclass :: JVMClass s 
           -> J.ClassName
           -> JVMGenerator h s ret (Expr JVM s BoolType)
isSubclass dcls cn2 = do            
  ctx <- gets jsContext
  sm <- readGlobal (dynamicClassTable ctx)

  let className = getJVMClassName dcls
  let className2 = App $ TextLit (fromString (J.unClassName cn2))

  ifte (App (BaseIsEq knownRepr className className2))
    (return (App (BoolLit True)))
    $ do
      -- construct a while loop in the output, testing each superclass
        superReg <- newReg (getJVMClassSuper dcls)
        resultReg <- newReg (App $ BoolLit False)
        let loopbody = do
              mclassType <- readReg superReg
              _ <- caseMaybe mclassType UnitRepr
                    MatchMaybe
                    { onNothing = return (App EmptyApp)
                    , onJust    = \(classType :: Expr JVM s JVMClassType) -> do
                        -- superclass is not null
                            let lu2 = App (LookupStringMapEntry knownRepr sm (getJVMClassName classType))
                            caseMaybe lu2 UnitRepr
                                  MatchMaybe
                                    { onNothing = return (App EmptyApp)
                                    , onJust    = \ct -> do
                                         let sclassName = getJVMClassName classType
                                         ifte (App (BaseIsEq knownRepr sclassName className2))
                                           (assignReg superReg (App $ NothingValue knownRepr)
                                              >> assignReg resultReg (App $ BoolLit True )
                                              >> return (App EmptyApp))
                                           (assignReg superReg (getJVMClassSuper ct) >>
                                           return (App EmptyApp))
                                    }
                    }
              return ()
        
        while (InternalPos, readReg superReg >>= gen_isJust)
              (InternalPos, loopbody)

        v <- readReg resultReg
        return v


------------------------------------------------------------------------
