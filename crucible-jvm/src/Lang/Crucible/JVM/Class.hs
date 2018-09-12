{- |

Module           : Lang.Crucible.JVM.Class
Description      : Implements OO features of the JVM
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : sweirich@galois.com
Stability        : provisional

The functions in this module implement the OO features of the JVM, including
working with objects, dynamic class information and arrays.

- construct objects and arrays

- access static and dynamic fields

- invoke static and dynamic methods

- dynamic type tests

- construct the dynamic information related to the class table
  (including the class initialization status)

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

-- SCW: I didn't even know about this extension until my code stopped parsing
-- with Haskell2010. Not sure where I'm using it in this file.
{-# LANGUAGE NondecreasingIndentation #-}

{-# OPTIONS_GHC -haddock #-}

module Lang.Crucible.JVM.Class
   (
     lookupClassGen
   , getAllFields
   , fieldIdString
   -- * Working with `JVMClass` data
   , getJVMClass
   , getJVMClassByName
   , getInitStatus
   , setInitStatus
   -- ** Class initialization
   , initializeClass
   , emptyMethodTable
   , insertMethodTable
   , initializeJVMClass
   -- ** Initialization status
   , notStarted
   , started
   , initialized
   , erroneous
   -- ** Accessors for `JVMClass` in memory structure
   , getJVMClassName
   , getJVMClassInitStatus
   , getJVMClassSuper
   , getJVMClassMethodTable
   , getJVMClassInterfaces
   , setJVMClassInitStatus
   -- * Dynamic type test
   , isSubType
   , getObjectType
   , checkCast
   -- * Objects
   , newInstanceInstr
   , getInstanceFieldValue
   , setInstanceFieldValue
   , getJVMInstanceClass
   -- ** Dynamic dispatch
   , findDynamicMethod
   -- ** Static fields and methods
   , getStaticFieldValue
   , setStaticFieldValue
   , getStaticMethod
   -- * Strings
   , refFromString
   -- * Arrays
   , newarrayExpr
   , newarrayFromVec
   , newMultiArray 
   , arrayIdx
   , arrayUpdate
   , arrayLength
   )
   where

import Data.Maybe (maybeToList, mapMaybe)
import Control.Monad.State.Strict
-- import Control.Lens hiding (op, (:>))
import           Data.Map(Map)
import qualified Data.Map.Strict as Map
import           Data.Set(Set)
import qualified Data.Set as Set
import           Data.Vector (Vector)
import qualified Data.Vector as V
import           Data.String (fromString)


-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr as NR

-- jvm-parser
import qualified Language.JVM.Parser as J

-- crucible
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types

-- crucible-jvm
import           Lang.Crucible.JVM.Types
import           Lang.Crucible.JVM.Generator

-- what4
import           What4.ProgramLoc (Position(InternalPos))


import           GHC.Stack


-- | lookup the information that the generator has about a class
-- (i.e. methods, fields, superclass)

lookupClassGen :: (HasCallStack) => J.ClassName -> JVMGenerator h s ret J.Class
lookupClassGen cName = do
  ctx <- gets jsContext
  case Map.lookup cName (classTable ctx) of
    Just cls -> return cls
    Nothing  -> error $ "no information about class " ++ J.unClassName cName



---------------------------------------------------------------------------------
--
-- * Runtime representation of class information (i.e. JVMClass)
--

-- | initialization status values
notStarted, started, initialized, erroneous :: JVMInitStatus f 
notStarted   = App $ BVLit knownRepr 0
started      = App $ BVLit knownRepr 1
initialized  = App $ BVLit knownRepr 2
erroneous    = App $ BVLit knownRepr 3


-- | Expression for the class name
classNameExpr :: J.ClassName -> JVMString s
classNameExpr cn = App $ TextLit $ fromString (J.unClassName cn)

-- | Expression for method key
-- Includes the parameter types to resolve overloading
-- TODO: This is an approximation of what the JVM actually does 
methodKeyExpr :: J.MethodKey -> JVMString s
methodKeyExpr c = App $ TextLit $ fromString (J.methodKeyName c ++ params) where
  params = concat (map show (J.methodKeyParameterTypes c))


-- | Method table
type JVMMethodTable s = Expr JVM s JVMMethodTableType

-- | initial table
emptyMethodTable :: JVMMethodTable s
emptyMethodTable = App (EmptyStringMap knownRepr)

-- | add a function handle to the method table
-- The function's type must be existentially quantified
insertMethodTable :: (JVMString s, Expr JVM s AnyType) -> JVMMethodTable s -> JVMMethodTable s
insertMethodTable (s, v) sm = App (InsertStringMapEntry knownRepr sm s (App $ JustValue knownRepr v))

--
-- | update the jvm class table to include an entry for the specified class
--
-- This will also initalize the superclass (if present and necessary)
--
initializeJVMClass :: J.Class -> JVMGenerator h s t (JVMClass s)
initializeJVMClass c  = do
  ctx <- gets jsContext

  let className :: JVMString s
      className  = classNameExpr (J.className c)

  -- if this class has a superclass that we know something about,
  -- find the JVMClass associated with it (creating if necessary)
  let superClassM | Just cn  <- J.superClass c,
                    Just cls <- Map.lookup cn (classTable ctx) = do
                               val <- getJVMClass cls
                               return $ App $ JustValue knownRepr val
                  | otherwise = return $ App $ NothingValue knownRepr 

  jsc <- superClassM
  
  -- find available handles for the methods in the class
  let handles    = [ mhi | m <- J.classMethods c,
                           mhi <- maybeToList $ Map.lookup (J.className c, J.methodKey m)
                                  (methodHandles ctx) ]

  let methTable0 = map (\(JVMHandleInfo m h) ->
                           (methodKeyExpr m, App (PackAny (handleType h) (App (HandleLit h))))) handles
                  
  let methTable  = foldr insertMethodTable emptyMethodTable methTable0

  -- find all interfaces that this class implements
  let ifaces    = interfacesImplemented ctx c
  let ifaceExpr = App (VectorLit knownRepr
                        (V.fromList (map (classNameExpr . J.className) ifaces)))
  
  -- construct the data structure
  let str        = App (RollRecursive knownRepr knownRepr
                     $ App $ MkStruct knownRepr
                         (Ctx.empty `Ctx.extend` className
                                   `Ctx.extend` notStarted
                                   `Ctx.extend` jsc
                                   `Ctx.extend` methTable
                                   `Ctx.extend` ifaceExpr))

  -- update the dynamic class table
  let gv         = dynamicClassTable ctx                   
  sm <- readGlobal gv
  let expr = App $ InsertStringMapEntry knownRepr sm className (App $ JustValue knownRepr str)
  writeGlobal gv expr
  return str

-- | Find *all* interfaces that the class implements (not just those listed explicitly, but
-- all super interfaces, and all interfaces implemented by super classes).
interfacesImplemented :: JVMContext -> J.Class -> [J.Class]
interfacesImplemented ctx cn = toClassList (go (Set.singleton (J.className cn))) where
  
  toClassList :: Set J.ClassName -> [J.Class]
  toClassList s = mapMaybe (\cn0 -> Map.lookup cn0 (classTable ctx)) (Set.toList s)
  
  next :: J.ClassName -> Set J.ClassName
  next cn0 =
    Set.fromList (superclass cn0 ++ interfaces cn0)

  superclass cn0 
    | Just cls <- Map.lookup cn0 (classTable ctx)
    , Just sc  <- J.superClass cls
    = [sc]
    | otherwise
    = []

  interfaces cn0 
    | Just cls <- Map.lookup cn0 (classTable ctx)
    = J.classInterfaces cls
    | otherwise
    = []
    
     
  go :: Set J.ClassName -> Set J.ClassName
  go curr =
    let n  = Set.unions (map next (Set.toList curr))
        nn = Set.union curr n
    in
      if curr == nn then curr
      else go nn
    

-- * Accessors for `JVMClass` in memory structure

struct :: JVMClass s -> Expr JVM s JVMClassImpl
struct ct = App $ UnrollRecursive knownRepr knownRepr ct

getJVMClassName :: JVMClass s -> Expr JVM s StringType
getJVMClassName ct = App (GetStruct (struct ct) Ctx.i1of5 knownRepr)

getJVMClassInitStatus :: JVMClass s -> JVMInitStatus s
getJVMClassInitStatus ct = App (GetStruct (struct ct) Ctx.i2of5 knownRepr)

getJVMClassSuper :: JVMClass s -> Expr JVM s (MaybeType JVMClassType)
getJVMClassSuper ct = App (GetStruct (struct ct) Ctx.i3of5 knownRepr)

getJVMClassMethodTable :: JVMClass s -> JVMMethodTable s
getJVMClassMethodTable ct = App (GetStruct (struct ct) Ctx.i4of5 knownRepr)

getJVMClassInterfaces :: JVMClass s -> Expr JVM s (VectorType StringType)
getJVMClassInterfaces ct = App (GetStruct (struct ct) Ctx.i5of5 knownRepr)

-- | Update

setJVMClassInitStatus :: JVMClass s -> JVMInitStatus s -> JVMClass s
setJVMClassInitStatus ct status = App (RollRecursive knownRepr knownRepr 
                                       (App (SetStruct knownRepr (struct ct) Ctx.i2of5 status)))
                                    
------------------------------------------------------------------------
-- * Functions for working with the JVM class table

-- | Access the class table entry of a given class in the dynamic class table
-- If this class table entry has not yet been defined, define it
-- (Note: this function does not call the class initializer on the static variables,
-- that is done separately.)
getJVMClass :: J.Class -> JVMGenerator h s ret (JVMClass s)
getJVMClass c = do
  ctx <- gets jsContext
  let gv = (dynamicClassTable ctx)
  sm <- readGlobal gv
  let cn = classNameExpr (J.className c)
  let lu = App $ LookupStringMapEntry knownRepr sm cn
  caseMaybe lu knownRepr
    MatchMaybe 
      { onNothing = initializeJVMClass c                     
      , onJust    = return
      }

-- | lookup the data structure associated with a class
getJVMClassByName ::
  (HasCallStack) => J.ClassName -> JVMGenerator h s ret (Expr JVM s JVMClassType)
getJVMClassByName name = do
  lookupClassGen name >>= getJVMClass

      
-- | Access the initialization status of the class in the dynamic class table
-- If the class table entry for this class has not yet been defined, define it
getInitStatus :: J.Class -> JVMGenerator h s ret (JVMInitStatus s)
getInitStatus c = getJVMClassInitStatus <$> getJVMClass c

-- | Update the initialization status of the class in the dynamic class table
setInitStatus :: J.Class -> JVMInitStatus s -> JVMGenerator h s ret ()
setInitStatus c status = do
  entry <- getJVMClass c
  ctx <- gets jsContext
  let gv = dynamicClassTable ctx
  sm <- readGlobal gv
  let name  = classNameExpr (J.className c)
  let entry' = setJVMClassInitStatus entry status
  writeGlobal gv (App $ InsertStringMapEntry knownRepr sm name (App $ JustValue knownRepr entry'))

----------------------------------------------------------------------

-- * Static Fields and Methods

-- | Read the global variable corresponding to the given static field
getStaticFieldValue :: J.FieldId -> JVMGenerator h s ret (JVMValue s)
getStaticFieldValue fieldId = do
      let cls = J.fieldIdClass fieldId
      ctx <- gets jsContext
      initializeClass cls
      case Map.lookup (J.fieldIdClass fieldId, fieldId) (staticFields ctx) of
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
    case Map.lookup (cName, fieldId) (staticFields ctx) of
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
      Just handle@(JVMHandleInfo _ h) -> do
        debug 3 $ "invoking static method with return type " ++ show (handleReturnType h)
        return handle
      
------------------------------------------------------------------------
-- * Class Initialization
-- 


-- REVISIT: it may make sense for this to be dynamic
skipInit :: J.ClassName -> Bool
skipInit cname = cname `elem` []                 


specialClinit :: Map J.ClassName (JVMGenerator h s ret ())
specialClinit = Map.fromList [
   ("java/lang/Object", debug 2 "special java/lang/Object/<clinit>")
  ,("java/lang/String", debug 2 "special java/lang/String/<clinit>")
  ,("java/io/ObjectStreamField", debug 2 "special java/lang/ObjectStreamField/<clinit>")
--  ,("java/lang/StringBuffer", debug 2 "special java/lang/StringBuffer/<clinit>")
  ,("java/lang/System", do
       -- initialize System.out to be a PrintStream object
       -- note: we do not call PrintStream/<init> because this class
       -- is completely synthetic
       debug 2 $  "Initializing System.out static field"
       let fieldId = J.FieldId (J.mkClassName "java/lang/System")
                               "out"
                               (J.ClassType "java/io/PrintStream")
       printStreamCls <- getJVMClassByName (J.mkClassName "java/io/PrintStream")                               
       val <- newInstanceInstr printStreamCls []
       rawRef <- newRef val
       setStaticFieldValue fieldId (RValue (App (JustValue knownRepr rawRef)))
       debug 2 $ "Finished initializing System.out"
       return ())
  ]
  

-- | initialize the static fields of a class (if they haven't already been
-- initialized)
-- make sure that the jvm class table entry for the class has been initialized
initializeClass :: forall h s ret . HasCallStack => J.ClassName -> JVMGenerator h s ret ()
initializeClass name = unless (skipInit name) $ do

  debug 2 $ "initializeClass " ++ J.unClassName name ++ "  (start)"

  c <- lookupClassGen name
  status <- getInitStatus c
  
  let ifNotStarted = do
        
      -- note that we are starting
      setInitStatus c started
  
      -- make sure superclass has been initialized
      maybe (return ()) initializeClass (J.superClass c)
      
      -- initialize all of the static fields with default values
      mapM_ (initializeStaticField name) $ J.classFields c

      -- run the static initializer for the class (if present)
      _ <- case (Map.lookup name specialClinit) of
            Just special -> special
            Nothing -> let clinit = (J.MethodKey "<clinit>" [] Nothing) in
                       case c `J.lookupMethod` clinit  of
                         Just _ -> do
                           handle <- getStaticMethod name clinit
                           callJVMInit handle
                         Nothing -> return ()

      -- mark that we have completed
      setInitStatus c initialized
      debug 2 $ "initializeClass " ++ J.unClassName name ++ "  (finish)"

  ifte_ (App $ BVEq knownRepr status notStarted) ifNotStarted (return ())
  -- TODO: if init status is Erroneous createAndThrow "java/lang/NoClassDefFoundError"



-- | Call a JVM static initialer, such as <init>
-- These methods do not take arguments or produce results so they
-- do not work with the stack. As a result we can call these methods
-- in the JVMGenerator monad.
callJVMInit :: JVMHandleInfo -> JVMGenerator h s ret ()
callJVMInit (JVMHandleInfo _methodKey handle) =
  do let argTys = handleArgTypes handle
         retTy  = handleReturnType handle
     case (testEquality argTys (knownRepr :: Ctx.Assignment TypeRepr (Ctx.EmptyCtx Ctx.::> UnitType)),
           testEquality retTy  (knownRepr :: TypeRepr UnitType)) of
       (Just Refl, Just Refl) -> do
         _ <- call (App (HandleLit handle)) (Ctx.Empty Ctx.:> App EmptyApp)
         return ()
       (_,_) -> error "Internal error: can only call functions with no args/result"


-- | Compute the initial value of a field based on its
-- static initializer and/or type
initialFieldValue :: J.Field -> JVMGenerator h s ret (JVMValue s)
initialFieldValue f = 
  case J.fieldConstantValue f of
     Just (J.Double v) ->
        return (DValue (App (DoubleLit v)))
     Just (J.Float v) ->
        return (FValue (App (FloatLit v)))
     Just (J.Integer v) ->
        return (IValue (App (BVLit knownRepr (toInteger v))))
     Just (J.Long v) ->
        return (LValue (App (BVLit knownRepr (toInteger v))))
     Just (J.String v) ->
        RValue <$> refFromString v
     Nothing ->
        return $ defaultValue (J.fieldType f)
     Just tp -> error $ "Unsupported field type" ++ show tp

initializeStaticField :: J.ClassName -> J.Field -> JVMGenerator h s ret ()
initializeStaticField name f = do
  when (J.fieldIsStatic f) $ do
      let fieldId = J.FieldId name (J.fieldName f) (J.fieldType f)
      setStaticFieldValue fieldId =<< initialFieldValue f

      
------------------------------------------------------------------------

-- | Search for a method handle using the dynamic class information
findDynamicMethod :: JVMClass s 
                  -> J.MethodKey
                  -> JVMGenerator h s ret (Expr JVM s AnyType)
findDynamicMethod dcls methodKey = do
  let dmeth = methodKeyExpr methodKey
  ctx <- gets jsContext
  sm  <- readGlobal (dynamicClassTable ctx)

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
-- * Dynamic type testing

-- | Create a runtime value for an array type rep, given the element type
makeArrayTypeRep :: JVMTypeRep s -> JVMTypeRep s
makeArrayTypeRep ety = App $ RollRecursive knownRepr knownRepr (App $ InjectVariant knownRepr Ctx.i1of3 ety)

-- | Create a runtime value for a class type rep, given the class rep
makeClassTypeRep :: JVMClass s -> JVMTypeRep s
makeClassTypeRep cls = 
  App (RollRecursive knownRepr knownRepr (App $ InjectVariant knownRepr Ctx.i2of3 cls))


-- | This function will initialize the class, if it hasn't been already
makeClassTypeRepByName :: J.ClassName -> JVMGenerator h s ret (JVMTypeRep s)
makeClassTypeRepByName cn = do
  cls <- getJVMClassByName cn
  return $ makeClassTypeRep cls


primIndex :: J.Type -> Maybe (JVMInt s)
primIndex ty =
  case ty of
    J.BooleanType -> return 0
    J.ByteType    -> return 1
    J.CharType    -> return 2
    J.DoubleType  -> return 3
    J.FloatType   -> return 4
    J.IntType     -> return 5
    J.LongType    -> return 6
    J.ShortType   -> return 7
    _             -> Nothing

-- | Given a JVM type, generate a runtime value for its representation.
makeJVMTypeRep :: J.Type -> JVMGenerator h s ret (JVMTypeRep s)
makeJVMTypeRep ty =
  case ty of 
    J.ArrayType ety -> makeArrayTypeRep <$> makeJVMTypeRep ety
    J.ClassType cn  -> makeClassTypeRepByName cn
    _ -> case primIndex ty of
           Just x ->
              return $ App $ RollRecursive knownRepr knownRepr (App $ InjectVariant knownRepr Ctx.i3of3 x) 
           Nothing ->
              jvmFail $ "BUG: impossible case"
              


-- | Generate code that accesses the runtime type rep of an object
getObjectType :: JVMObject s -> JVMGenerator h s ret (JVMTypeRep s)
getObjectType obj =
  let unr = App $ UnrollRecursive knownRepr knownRepr obj in
  caseMaybe (App $ ProjectVariant knownRepr Ctx.i1of2 unr) knownRepr
  MatchMaybe
  { 
    onJust = \inst -> do
      -- this is an instance object, access its class reference
      let cls = App (GetStruct inst Ctx.i2of2 knownRepr)
      -- return a new class type based on that
      return $ makeClassTypeRep cls
      
  , onNothing = do
      -- must be an array object
      let marr = App $ ProjectVariant knownRepr Ctx.i2of2 unr
      arr <- assertedJustExpr marr "must be instance or array"
      return $ App $ GetStruct arr Ctx.i3of3 knownRepr
  }      
  

-- | Generated a checkedcast instruction by reading the dynamic
-- type of the reference and comparing it against the provided
-- type
checkCast :: JVMRef s -> J.Type -> JVMGenerator h s ret ()
checkCast objectRef ty = 
  caseMaybe_ objectRef 
  MatchMaybe
  { onNothing = return ()
  , onJust  = \rawRef -> do
      obj <- readRef rawRef
      tyr <- getObjectType obj
      b   <- isSubType tyr ty
      assertExpr b $ fromString ("java/lang/ClassCastException (" ++ show ty ++ ")" )
  }

-- Classes and interfaces that are supertypes of array types
-- https://docs.oracle.com/javase/specs/jls/se8/html/jls-4.html#jls-4.10.3
arraySuperTypes :: [J.ClassName]
arraySuperTypes = map J.mkClassName ["java/lang/Object", "java/lang/Cloneable", "java/io/Serializable"]

-- | Test whether the dynamic class is a subtype of the given class name or interface name
-- NEED TO MAKE THIS A WHILE LOOP
-- NO: type tyT should decrease on each recursive call
isSubType :: JVMTypeRep s -> J.Type -> JVMGenerator h s ret (Expr JVM s BoolType)
isSubType tyS tyT = do
  debug 3 $ "isSubtype called with " ++ show tyT
  let unr = App $ UnrollRecursive knownRepr knownRepr tyS 
  caseMaybe (App $ ProjectVariant knownRepr Ctx.i1of3 unr) knownRepr
    MatchMaybe
    { onJust    = \sc -> do  -- S is an array type
      -- addPrintStmt (App $ TextLit (fromString ("isSubtype (array): " ++ show tyT ++ "\n")))        
      case tyT of
        (J.ClassType name) ->
          return (App $ BoolLit (name `elem` arraySuperTypes))
        (J.ArrayType tc)   -> do
          -- contravariant arrays, sigh
          isSubType sc tc
        _ -> return (App $ BoolLit False) 
    , onNothing = caseMaybe (App $ ProjectVariant knownRepr Ctx.i2of3 unr) knownRepr
      MatchMaybe
      { onJust  = \scls -> do -- S is an object type
        --addPrintStmt (App $ TextLit (fromString ("isSubtype (class): " ++ show tyT ++ "\n")))          
        case tyT of
          (J.ClassType name) -> do
              b1 <- scls `implements` name
              b2 <- scls `isSubclass` name
              return $ App $ Or b1 b2
          _ -> return (App $ BoolLit False)

      , onNothing = do
        -- primitive type
        -- addPrintStmt (App $ TextLit (fromString ("isSubtype (prim): " ++ show tyT ++ "\n")))          
        val <- assertedJustExpr (App $ ProjectVariant knownRepr Ctx.i3of3 unr) "isSubType: impossible"
        case primIndex tyT of
          Just x  -> return (App $ BVEq knownRepr val x)
          Nothing -> return (App $ BoolLit False)
      }
    }


-- | Test whether the given class implements the given interface name
-- by comparing it against all of the interfaces stored in the JVMClass
-- NOTE: for this implementation to be correct, the class must store the
-- transitive closure of *all* interfaces that it implements
implements :: JVMClass s -> J.ClassName -> JVMGenerator h s ret (Expr JVM s BoolType)
implements dcls interface = do
  let vec = getJVMClassInterfaces dcls
  let str = App $ TextLit (fromString (J.unClassName interface))
  ansReg <- newReg (App $ BoolLit False)
  forEach_ vec (\cn ->
                   ifte_ (App $ BaseIsEq knownRepr str cn)
                         (assignReg ansReg (App $ BoolLit True))
                         (return ()))
  readReg ansReg
  

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
      -- construct a while loop in the output, testing each superclass &
      -- interface type for equality
        superReg <- newReg (getJVMClassSuper dcls)
        resultReg <- newReg (App $ BoolLit False)
        let loopbody = do
              mclassType <- readReg superReg
              caseMaybe_ mclassType 
                    MatchMaybe
                    { onNothing = return ()
                    , onJust    = \(classType :: JVMClass s) -> do
                        -- superclass is not null
                            let lu2 = App (LookupStringMapEntry knownRepr sm (getJVMClassName classType))
                            caseMaybe_ lu2 
                                  MatchMaybe
                                    { onNothing = return ()
                                    , onJust    = \ct -> do
                                         let sclassName = getJVMClassName classType
                                         ifte_ (App (BaseIsEq knownRepr sclassName className2))
                                           (assignReg superReg (App $ NothingValue knownRepr)
                                              >> assignReg resultReg (App $ BoolLit True))
                                              
                                           (assignReg superReg (getJVMClassSuper ct))
                                          
                                    }
                    }
              return ()
        
        while (InternalPos, readReg superReg >>= gen_isJust)
              (InternalPos, loopbody)

        v <- readReg resultReg
        return v




------------------------------------------------------------------------

-- * Working with JVM objects  (class instances)

mkFieldId :: J.Class -> J.Field -> J.FieldId
mkFieldId c f = J.FieldId (J.className c) (J.fieldName f) (J.fieldType f)

getAllFields :: J.Class -> JVMGenerator h s ret [J.FieldId]
getAllFields cls = do
  case J.superClass cls of
    Nothing  -> return (map (mkFieldId cls) (J.classFields cls))
    Just sup -> do
      supCls <- lookupClassGen sup
      supFlds <- getAllFields supCls
      return (supFlds ++ (map (mkFieldId cls) (J.classFields cls)))
  
-- | dynamic text name for a field
fieldIdString :: J.FieldId -> String
fieldIdString f = J.unClassName (J.fieldIdClass f) ++ "." ++ J.fieldIdName f

-- | Construct a new JVM object instance, given the class data structure
-- and the list of fields. The fields will be initialized with the
-- default values, according to their types.
newInstanceInstr ::
  JVMClass s 
  -- ^ class data structure
  ->  [J.FieldId]
  -- ^ Fields
  ->  JVMGenerator h s ret (JVMObject s) 
newInstanceInstr cls fieldIds = do
    objFields <- mapM createField fieldIds
    let strMap = foldr addField (App (EmptyStringMap knownRepr)) objFields
    let ctx    = Ctx.empty `Ctx.extend` strMap `Ctx.extend` cls
    let inst   = App (MkStruct knownRepr ctx)
    let uobj   = injectVariant Ctx.i1of2 inst
    return $ App (RollRecursive knownRepr knownRepr uobj)
  where
    createField fieldId = do
      let str  = App (TextLit (fromString (fieldIdString fieldId)))
      let expr = valueToExpr (defaultValue (J.fieldIdType fieldId))
      let val  = App $ JustValue knownRepr expr
      return (str, val)
    addField (f,i) fs = 
      App (InsertStringMapEntry knownRepr fs f i)

-- | Access the field component of a JVM object (must be a class instance, not an array)
getInstanceFieldValue :: JVMObject s -> J.FieldId -> JVMGenerator h s ret (JVMValue s)
getInstanceFieldValue obj fieldId = do
  let uobj = App (UnrollRecursive knownRepr knownRepr obj)             
  inst <- projectVariant Ctx.i1of2 uobj
  let fields = App (GetStruct inst Ctx.i1of2 knownRepr)
  let str    = fieldIdString fieldId
  let key    = App (TextLit (fromString str))
  let mval   = App (LookupStringMapEntry knownRepr fields key)
  dyn <- assertedJustExpr mval (fromString ("getfield: field " ++ str ++ " not found"))
  fromJVMDynamic (J.fieldIdType fieldId) dyn

-- | Update a field of a JVM object (must be a class instance, not an array)
setInstanceFieldValue :: JVMObject s -> J.FieldId -> JVMValue s -> JVMGenerator h s ret (JVMObject s)
setInstanceFieldValue obj fieldId val = do
  let uobj   = App (UnrollRecursive knownRepr knownRepr obj)
  inst <- projectVariant Ctx.i1of2 uobj
  let fields = App (GetStruct inst Ctx.i1of2 knownRepr)
  let dyn  = valueToExpr val
  let str = fieldIdString fieldId
  let key = App (TextLit (fromString str))
  let mdyn = App (JustValue knownRepr dyn)
  let fields' = App (InsertStringMapEntry knownRepr fields key mdyn)
  let inst'  = App (SetStruct knownRepr inst Ctx.i1of2 fields')
  let uobj' = App (InjectVariant knownRepr Ctx.i1of2 inst')
  return $ App (RollRecursive knownRepr knownRepr uobj')

-- | Access the runtime class information for the class that instantiated this instance
getJVMInstanceClass :: JVMObject s -> JVMGenerator h s ret (JVMClass s)
getJVMInstanceClass obj = do
  let uobj = App (UnrollRecursive knownRepr knownRepr obj)
  inst <- projectVariant Ctx.i1of2 uobj
  return $ App (GetStruct inst Ctx.i2of2 knownRepr)


------------------------------------------------------------------------------
--
-- * String Creation

charLit :: Char -> Expr JVM s JVMValueType
charLit c = App (InjectVariant knownRepr tagI (App (BVLit w32 (toInteger (fromEnum c)))))

-- | Constructor for statically known string objects
-- 
refFromString ::  HasCallStack => String -> JVMGenerator h s ret (JVMRef s)
refFromString s =  do
  
  -- create the string object
  let name = "java/lang/String"
  initializeClass name
  clsObj <-  getJVMClassByName name
  cls    <-  lookupClassGen name
  fids   <-  getAllFields cls 
  obj    <-  newInstanceInstr clsObj fids

  -- create an array of characters
  -- TODO: Check this with unicode characters
  let chars = map charLit s
  let vec   = V.fromList chars
  arr   <- newarrayFromVec (J.ClassType (J.mkClassName "java/lang/String")) vec
  arrRef <- newRef arr

  -- It'd be preferable to use createInstance here, but the amount of
  -- infrastructure needed to create strings via the Java runtime is significant
  -- (thread local variables, character encodings, builtin unsafe operations,
  -- etc.), so we cheat and just forcibly set the (private) instance fields.
  -- We'll want want to REVISIT this in the future.
  obj1 <- setInstanceFieldValue
    obj
    (J.FieldId "java/lang/String" "value" J.charArrayTy)
    (RValue (App (JustValue knownRepr arrRef)))
    
  obj2 <- setInstanceFieldValue
    obj1
    (J.FieldId "java/lang/String" "hash" J.IntType)
    -- TODO: hash is always 0, should be symbolic
    (IValue (App (BVLit w32 0)))

  rawRef <-  newRef obj2
  let ref = App (JustValue knownRepr rawRef)

  return ref


------------------------------------------------------------------------------
-- * Arrays

-- | Construct a new array object, with copies of the initial value
newarrayExpr ::
  JVMInt s 
  -- ^ array size, must be nonnegative
  -> Expr JVM s JVMValueType
  -- ^ Initial value for all array elements
  -> J.Type
  -- ^ type of array (not of elements)
  -> JVMGenerator h s ret (JVMObject s)
newarrayExpr count val jty = do
  debug 4 $ "new array of type " ++ show jty
  let vec = App (VectorReplicate knownRepr (App (BvToNat w32 count)) val)
  ty  <- makeJVMTypeRep jty
  let ctx = Ctx.empty `Ctx.extend` count `Ctx.extend` vec `Ctx.extend` ty
  let arr = App (MkStruct knownRepr ctx)
  let uobj = injectVariant Ctx.i2of2 arr
  return $ App (RollRecursive knownRepr knownRepr uobj)

newMultiArray ::
  J.Type
  -- ^ type of the array to create
  -> [JVMInt s]
  -- ^ list of dimension of the array (must be nonempty)
  -- each int must be nonnegative
  -> JVMGenerator h s ret (JVMObject s)
newMultiArray arrType counts = do
    loop arrType counts
  where
    loop :: J.Type -> [JVMInt s] -> JVMGenerator h s ret (JVMObject s)
    loop _ [] = jvmFail "newMultiArray: need at least one dimension"
    loop (J.ArrayType elemType) [count] =
        newarrayExpr count (valueToExpr $ defaultValue elemType) arrType
    loop (J.ArrayType elemType) (count:rest) = do
        let nul = valueToExpr $ RValue $ App $ NothingValue knownRepr
        arr0 <- newarrayExpr count nul arrType
        arrRef <- newRef arr0
        iterate_ count $ \i -> do
          arr   <- readRef arrRef 
          inner <- loop elemType rest
          rawRef <- newRef inner
          let val = injectVariant tagR (App $ JustValue knownRepr rawRef)
          narr  <- arrayUpdate arr i val
          writeRef arrRef narr
        readRef arrRef
    loop ty (_:_) = jvmFail $ "newMultiArray: wrong number of dims " ++ show ty      


-- | Construct a new array given a vector of initial values
-- (This function is used for static array initializers.)
newarrayFromVec ::
  J.Type
  -- ^ Type of array
  -> Vector (Expr JVM s JVMValueType)
  -- ^ Initial values for all array elements
  -> JVMGenerator h s ret (JVMObject s)
newarrayFromVec aty vec = do
  let count = App $ BVLit w32 (toInteger (V.length vec))
  ty <- makeJVMTypeRep aty
  let ctx   = Ctx.empty `Ctx.extend` count `Ctx.extend` (App $ VectorLit knownRepr vec) `Ctx.extend` ty
  let arr   = App (MkStruct knownRepr ctx)
  let uobj  = injectVariant Ctx.i2of2 arr
  return $
    App $ RollRecursive knownRepr knownRepr uobj


-- | Index into an array object
arrayIdx :: JVMObject s
  -- ^ the array
  -> JVMInt s
  -- ^ index into the array
  -> JVMGenerator h s ret (Expr JVM s JVMValueType)
arrayIdx obj idx = do
     let uobj = App (UnrollRecursive knownRepr knownRepr obj)
     let marr = App (ProjectVariant knownRepr Ctx.i2of2 uobj)
     arr <- assertedJustExpr marr "array index: not a valid array"
     let vec = App (GetStruct arr Ctx.i2of3 knownRepr)
     -- TODO: assert 0 <= idx < length arr
     let val = App (VectorGetEntry knownRepr vec (App (BvToNat w32 idx)))
     return val

-- | Update an array object
arrayUpdate :: JVMObject s                          -- ^ the array
            -> JVMInt s                             -- ^ index
            -> Expr JVM s JVMValueType              -- ^ new value
            -> JVMGenerator h s ret (JVMObject s)
arrayUpdate obj idx val = do
  let uobj = App (UnrollRecursive knownRepr knownRepr obj)
  let marr = App (ProjectVariant knownRepr Ctx.i2of2 uobj)
  arr <- assertedJustExpr marr "array update: not a valid array"
  let vec = App (GetStruct arr Ctx.i2of3 knownRepr)
     -- TODO: assert 0 <= idx < length arr
  let vec' = App (VectorSetEntry knownRepr vec (App (BvToNat w32 idx)) val)
  let arr' = App (SetStruct knownRepr arr Ctx.i2of3 vec')
  let uobj' = App (InjectVariant knownRepr Ctx.i2of2 arr')
  let obj' = App (RollRecursive knownRepr knownRepr uobj')
  return obj'
 
-- | Access length of the array object
arrayLength :: JVMObject s -> JVMGenerator h s ret (JVMInt s)
arrayLength obj = do
  let uobj = App (UnrollRecursive knownRepr knownRepr obj)
  let marr = App (ProjectVariant knownRepr Ctx.i2of2 uobj)
  arr <- assertedJustExpr marr "array length: not a valid array"
  let len = App (GetStruct arr Ctx.i1of3 knownRepr)
  return len


------------------------------------------------------------------------

