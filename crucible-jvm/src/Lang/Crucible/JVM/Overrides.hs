{- |
Module           : Lang.Crucible.JVM.Overrides
Description      : Java method overrides
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : sweirich@galois.com
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
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Lang.Crucible.JVM.Overrides where

-- base
import Numeric(fromRat)
import Data.Maybe (isJust, fromJust)
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
import Data.Text (Text,unpack,pack)
import Data.Word
import Data.Char (ord, chr)

import Control.Applicative ((<|>))
import System.IO

-- jvm-parser
import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

-- bv-sized
import qualified Data.BitVector.Sized as BV

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr as NR

-- crucible
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Backend
import           Lang.Crucible.Panic

import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState   as C
import qualified Lang.Crucible.Simulator.OverrideSim   as C
import qualified Lang.Crucible.Simulator.RegValue      as C
import qualified Lang.Crucible.Simulator.RegMap        as C

import qualified Lang.Crucible.Analysis.Postdom        as C
import qualified Lang.Crucible.Utils.MuxTree           as C

-- what4
import           What4.ProgramLoc (Position(InternalPos))
import           What4.Interface (IsExprBuilder)
import           What4.FunctionName (FunctionName(..))
import qualified What4.Interface                       as W4
import qualified What4.InterpretedFloatingPoint        as W4
import qualified What4.Partial                         as W4

import           What4.Utils.MonadST (liftST)
import           What4.Utils.StringLiteral

-- crucible-jvm
import           Lang.Crucible.JVM.Types
import           Lang.Crucible.JVM.Context
import           Lang.Crucible.JVM.ClassRefs

import Debug.Trace

-----------------------------------------------------------------------------

-- | Given the name of a class and the field name, define the name of the global variable.
globalVarName :: J.ClassName -> String -> Text
globalVarName cn fn = fromString (J.unClassName cn ++ "." ++ fn)

-- | Given the name of a class and a method, define the standard name.
methodHandleName :: J.ClassName -> J.MethodKey -> FunctionName
methodHandleName cn mn = fromString (J.unClassName cn ++ "." ++ J.methodKeyName mn)


-- | Add a reference to the object type if the method is nonstatic.
allParameterTypes :: J.ClassName -> Bool -> J.MethodKey -> [J.Type]
allParameterTypes className isStatic m
  | isStatic  = J.methodKeyParameterTypes m
  | otherwise = J.ClassType className : J.methodKeyParameterTypes m

addThis :: Bool -> [Some TypeRepr] -> [Some TypeRepr]
addThis isStatic args =
  (if isStatic then [] else [Some refRepr]) ++ args


-- | Translate the types of the method.
jvmToFunHandleRepr ::
  Bool -> J.MethodKey ->
  (forall args ret. CtxRepr args -> TypeRepr ret -> a)
  -> a
jvmToFunHandleRepr isStatic meth k =
   let args  = Ctx.fromList (addThis isStatic (map javaTypeToRepr (J.methodKeyParameterTypes meth)))
       ret   = maybe (Some C.UnitRepr) javaTypeToRepr (J.methodKeyReturnType meth)
   in case (args, ret) of
     (Some argsRepr, Some retRepr) -> k argsRepr retRepr

--------------------------------------------------------------------------------

-- Most of this part is adapted from crucible-llvm Lang.Crucible.LLVM.Intrinsics
data JVMOverride p sym = forall args ret.
  JVMOverride
  { jvmOverride_className      :: J.ClassName
  , jvmOverride_methodKey      :: J.MethodKey
  , jvmOverride_methodIsStatic :: Bool
  , jvmOverride_args           :: CtxRepr args
  , jvmOverride_ret            :: TypeRepr ret
  , jvmOverride_def            :: forall rtp args' ret'.
         sym ->
         Ctx.Assignment (C.RegEntry sym) args ->
         C.OverrideSim p sym JVM rtp args' ret' (C.RegValue sym ret)
  }

newtype ArgTransformer p sym args args' =
  ArgTransformer { applyArgTransformer :: (forall rtp l a.
    Ctx.Assignment (C.RegEntry sym) args ->
    C.OverrideSim p sym JVM rtp l a (Ctx.Assignment (C.RegEntry sym) args')) }

newtype ValTransformer p sym tp tp' =
  ValTransformer { applyValTransformer :: (forall rtp l a.
    C.RegValue sym tp ->
    C.OverrideSim p sym JVM rtp l a (C.RegValue sym tp')) }


transformJVMArgs :: forall m p sym args args'.
  (HasCallStack, IsSymInterface sym, Monad m) =>
  sym ->
  CtxRepr args' ->
  CtxRepr args ->
  FunctionName ->
  m (ArgTransformer p sym args args')
transformJVMArgs _ Ctx.Empty Ctx.Empty _ =
  return (ArgTransformer (\_ -> return Ctx.Empty))

transformJVMArgs sym (rest' Ctx.:> tp') (rest Ctx.:> tp) fnm = do
  return (ArgTransformer
           (\(xs Ctx.:> x) ->
              do (ValTransformer f)  <- transformJVMRet sym tp tp'
                 (ArgTransformer fs) <- transformJVMArgs sym rest' rest fnm
                 xs' <- fs xs
                 x'  <- C.RegEntry tp' <$> f (C.regValue x)
                 pure (xs' Ctx.:> x')))
transformJVMArgs _ derived override fnm =
  panic "Intrinsics.transformJVMArgs"
    [ "transformJVMArgs: argument shape mismatch!", show fnm, showJVMArgs derived, showJVMArgs override ]

transformJVMRet ::
  (HasCallStack, IsSymInterface sym, Monad m) =>
  sym ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  m (ValTransformer p sym ret ret')
-- maybe do some work here?
transformJVMRet _sym ret ret'
  | Just Refl <- testEquality ret ret'
  = return (ValTransformer return)
transformJVMRet _sym ret ret'
  = panic "Intrinsics.transformJVMRet"
      [ "Cannot transform types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

-- | Do some pipe-fitting to match a Crucible override function into the shape
--   expected by the JVM calling convention.
build_jvm_override ::
  (HasCallStack, IsSymInterface sym) =>
  sym ->
  FunctionName ->
  CtxRepr args ->
  TypeRepr ret ->
  CtxRepr args' ->
  TypeRepr ret' ->
  (forall rtp' l' a'. Ctx.Assignment (C.RegEntry sym) args ->
   C.OverrideSim p sym JVM rtp' l' a' (C.RegValue sym ret)) ->
  C.OverrideSim p sym JVM rtp l a (C.Override p sym JVM args' ret')
build_jvm_override sym fnm args ret args' ret' llvmOverride =
  do fargs <- transformJVMArgs sym args args' fnm
     fret  <- transformJVMRet  sym ret  ret'
     return $ C.mkOverride' fnm ret' $
            do C.RegMap xs <- C.getOverrideArgs
               applyValTransformer fret =<< llvmOverride =<< applyArgTransformer fargs xs

register_jvm_override :: forall p sym l a rtp
                       . (IsSymInterface sym)
                      => JVMOverride p sym
                      -> StateT JVMContext (C.OverrideSim p sym JVM rtp l a) ()
register_jvm_override (JVMOverride { jvmOverride_className=cn
                                     , jvmOverride_methodKey=mk
                                     , jvmOverride_methodIsStatic=isStatic
                                     , jvmOverride_args=overrideArgs
                                     , jvmOverride_ret=overrideRet
                                     , jvmOverride_def=def }) = do
  jvmctx <- get

  let fnm = methodHandleName cn mk

  sym <- lift $ C.getSymInterface


  jvmToFunHandleRepr isStatic mk  $ \derivedArgs derivedRet -> do
    o <- lift $ build_jvm_override sym fnm overrideArgs overrideRet derivedArgs derivedRet (def sym)
    -- traceM $ "installing override for " ++ show fnm
    case Map.lookup (cn,mk) (methodHandles jvmctx) of
      Just (JVMHandleInfo _mkey h) -> do
        case testEquality (handleArgTypes h) derivedArgs of
           Nothing ->
             panic "Intrinsics.register_jvm_override"
               [ "Argument type mismatch when registering override."
               , "*** Override name: " ++ show fnm
               ]
           Just Refl ->
             case testEquality (handleReturnType h) derivedRet of
               Nothing ->
                 panic "Intrinsics.register_jvm_override"
                   [ "return type mismatch when registering override"
                   , "*** Override name: " ++ show fnm
                   ]
               Just Refl -> lift $ C.bindFnHandle h (C.UseOverride o)
      Nothing ->
        do
           ctx <- lift $ use C.stateContext
           let ha = C.simHandleAllocator ctx
           h <- lift $ liftIO $ mkHandle' ha fnm derivedArgs derivedRet
           lift $ C.bindFnHandle h (C.UseOverride o)
           put (jvmctx { methodHandles = Map.insert (cn,mk) (JVMHandleInfo mk h) (methodHandles jvmctx) })

--------------------------------------------------------------------------------

-- | This is an example of a nop override.
-- Explicitly calling the garbage collector does nothing during symbolic
-- execution.
gc_override ::(IsSymInterface sym) => JVMOverride p sym
gc_override =
  let isStatic = False
      mk       = J.makeMethodKey "gc" "()V" in
  jvmToFunHandleRepr isStatic mk $ \ _argsRepr _retRepr ->
    JVMOverride { jvmOverride_className="java/lang/System"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=UnitRepr
                , jvmOverride_def=
                  \_sym _args -> return ()
                }


--------------------------------------------------------------------------------
-- ** Concrete values
--
-- Concrete values: if the result of static simulation is a unique, concrete value
-- figure out what it is.
-- Essentially, this is a generalization of the `W4.asInteger`, `W4.asBV`
-- etc. operations.
--


-- Haskell representation of JVM symbolic values
-- Note: static simulation should never say that something is, say,
-- both a CFloat and a CDouble --- the type system should rule that
-- out.

data CValue =
    CDouble Double
  | CFloat  Float
  | CInt Int
  | CLong Integer
  | CRef (Maybe CObject)
  deriving Show

data CObject =
    CInstance (Map Text (Maybe CValue), CClass)
  | CArray (Vector (Maybe CValue))
  deriving Show

data CInitStatus = CNotStarted | CStarted | CInitialized | CErroneous
  deriving Show

-- | We don't store any of the static information about the class
-- (methods, interfaces, etc) because we can figure that out just
-- from the class name.
data CClass =
  MkClass { cclassName   :: Text
          , cinitStatus  :: CInitStatus
          }
  deriving Show

------------------------------------------------------------------
--
-- | Convert a concrete value to text.
--
class ToText a where
  totext  :: a -> Text
  totext x = totexts x ""

  totexts :: a -> Text -> Text

instance ToText CValue where
  totexts (CDouble d)     f = fromString (show d) <> f
  totexts (CFloat  d)     f = fromString (show d) <> f
  totexts (CInt    i)     f = fromString (show i) <> f
  totexts (CLong   l)     f = fromString (show l) <> f
  totexts (CRef Nothing)  f = "null" <> f
  totexts (CRef (Just o)) f = totexts o f


toCharVec :: Vector (Maybe CValue) -> Maybe (Vector Char)
toCharVec vec = traverse (\jv -> case jv of
                                   (Just (CInt x)) -> Just (chr x)
                                   _               -> Nothing) vec

--
-- | We don't try to call the toString method for objects.
--   Maybe we should??
instance ToText CObject where
  totexts (CInstance (fields, cls)) f
    | cclassName cls == "java/lang/String"
    , Just (Just (CRef (Just (CArray vec)))) <- Map.lookup "java/lang/String.value" fields
    , Just chars <- toCharVec vec
    = pack (V.toList chars) <> f
  totexts (CInstance (fields, cls)) f
    | cclassName cls == "java/lang/StringBuffer"
    , Just (Just (CRef (Just (CArray vec)))) <-
        Map.lookup "java/lang/AbstractStringBuilder.value" fields
    , Just (Just (CInt count)) <- Map.lookup "java/lang/AbstractStringBuilder.count" fields
    , Just chars <- toCharVec (V.take count vec)
    = pack (V.toList chars) <> f

  totexts (CInstance (fields, cls)) f
    -- do not text out non-String objects.
    -- TODO: what about primitives such as java.lang.Integer?
    = pack ("<instance of ") <> cclassName cls <> (pack ">") <> f
  totexts (CArray vec) f
    = pack ("<array>") <> f

instance ToText (Maybe CObject) where
  totexts (Just cobj) f = totexts cobj f
  totexts Nothing     f = "null" <> f

------------------------------------------------------------------



-- | Convert a register value with a crucible type to a Haskell
--   version, if it is indeed a concrete value
class Concretize (a :: CrucibleType) where

  type Concrete a
  concretize
    :: IsSymInterface sym
    => C.RegValue' sym a
    -> C.OverrideSim p sym JVM rtp args ret (Maybe (Concrete a))




instance Concretize JVMValueType where
  type Concrete JVMValueType = CValue
  concretize (C.RV v) =
    variantCase v
    (Ctx.Empty
      `Ctx.extend` Dispatch (\x -> return ((CFloat . fromRational) <$> floatAsRational x))
      `Ctx.extend` Dispatch (\x -> return ((CDouble . fromRational) <$> floatAsRational x))
      `Ctx.extend` Dispatch (\x -> return ((CInt . fromInteger) <$> BV.asSigned knownRepr <$> W4.asBV x))
      `Ctx.extend` Dispatch (\x -> return ((CLong . fromInteger) <$> BV.asSigned knownRepr <$> W4.asBV x))
      `Ctx.extend` Dispatch (\x -> do mb <- concretize @JVMRefType (C.RV x)
                                      return (CRef <$> mb)))

instance Concretize JVMRefType where
  type Concrete JVMRefType = Maybe CObject
  concretize (C.RV v) = do
    foldr (\a _b -> case (C.viewMuxTree a) of
                      [(ref,_pred)] ->
                        do obj  <- C.readRef ref
                           co   <- concretize @JVMObjectType (C.RV obj)
                           return (Just co)
                      _ -> return Nothing)
            (return (Just Nothing)) v


instance Concretize JVMArrayType where
  type Concrete JVMArrayType = Vector (Maybe CValue)
  concretize (C.RV x) = do
    let (C.RV vec) = x Ctx.! Ctx.i2of3
    vm <- V.mapM (concretize @JVMValueType . C.RV) vec
    return (Just vm)


instance Concretize JVMInstanceType where
  type Concrete JVMInstanceType = (Map Text (Maybe CValue), CClass)
  concretize (C.RV x) = do
    let (C.RV sm)  = x Ctx.! Ctx.i1of2
    let cls' = x Ctx.! Ctx.i2of2
    (sm1 :: Map Text (Maybe CValue)) <-
      traverse (\mv -> foldr (\a b -> (concretize @JVMValueType . C.RV) a) (return Nothing) mv) sm
    (cc  :: Maybe CClass) <- concretize @JVMClassType cls'
    return ((sm1,) <$> cc)


instance Concretize JVMInitStatusType where
  type Concrete JVMInitStatusType = CInitStatus
  concretize (C.RV x) = do
    return $ case BV.asUnsigned <$> W4.asBV x of
      Just 0 -> Just CNotStarted
      Just 1 -> Just CStarted
      Just 2 -> Just CInitialized
      Just 3 -> Just CErroneous
      _ -> Nothing

instance Concretize JVMClassType where
  type Concrete JVMClassType = CClass
  concretize (C.RV x) = do
    let (C.RV sn)  = (C.unroll x) Ctx.! Ctx.i1of5
    let imp        = (C.unroll x) Ctx.! Ctx.i2of5
    imp' <- concretize @JVMInitStatusType imp
    return (MkClass <$> (fromUnicodeLit <$> W4.asString sn) <*> imp')


instance Concretize JVMObjectType where
  type Concrete JVMObjectType = CObject
  concretize (C.RV v) =
    variantCase (C.unroll v)
       (Ctx.Empty `Ctx.extend` Dispatch (\x -> do mv <- concretize @JVMInstanceType (C.RV x)
                                                  return (CInstance <$> mv))
                  `Ctx.extend` Dispatch (\x -> do mv <- concretize @JVMArrayType (C.RV x)
                                                  return (CArray <$> mv)))

-----------------------------------------------------------------------------
data Dispatch m sym b a = Dispatch { apply :: (C.RegValue sym a -> m (Maybe b)) }

--maybeCase f (x :: Part _) = foldr (\ a b -> f a) (return Nothing) x

-- Apply the dispatch to the first defined branch, falling through
-- if none are defined
variantCase :: forall b sym ctx m. Monad m =>
               Ctx.Assignment (C.VariantBranch sym) ctx ->
               Ctx.Assignment (Dispatch m sym b) ctx ->
               m (Maybe b)
variantCase variant cases =
  case Ctx.viewAssign variant of
    Ctx.AssignEmpty -> return $ Nothing
    Ctx.AssignExtend variant' (part::C.VariantBranch sym tp) ->
      let (cases', (fd::Dispatch m sym b tp)) = Ctx.decompose cases in
      foldr (\(a::C.RegValue sym tp) (mb :: m (Maybe b)) -> do
               x1 <- apply fd a
               x2 <- mb
               return (x1 <|> x2))
            (variantCase variant' cases')
            (C.unVB part)



-----------------------------------------------------------------------------

--
-- | Print out an integer represented value (if it is concrete)
-- Needs access to the original Java type
showInt :: (W4.IsExpr e, 1 <= w) => J.Type -> e (BaseBVType w) -> String
showInt jty e = case BV.asSigned (W4.bvWidth e) <$> W4.asBV e of
              Just i  -> case jty of
                J.IntType -> show i
                J.CharType -> [chr (fromInteger i)]
                J.BooleanType -> if i == 0 then "false"
                                 else if i == 1 then "true"
                                 else fail "invalid boolean"
                J.LongType -> show i
                J.ShortType -> show i
                J.ByteType -> show i    --- TODO: are java bytes printed differently
                _ -> fail "showInt: Not an int-like type"
              Nothing -> show $ W4.printSymExpr e

showFloat :: W4.IsExpr e => e tp -> String
showFloat e = case floatAsRational e of
  Just rat -> show (fromRational rat :: Double)
  Nothing -> show $ W4.printSymExpr e

floatAsRational :: W4.IsExpr e => e tp -> Maybe Rational
floatAsRational e
  | Just Refl <- testEquality (W4.exprType e) W4.BaseRealRepr =
    W4.asRational e
  | otherwise =
    Nothing

--
-- | Print out an object value (if it is concrete)
-- For now: only String objects
--
showRef
  :: IsSymInterface sym
  => W4.PartExpr (W4.SymExpr sym BaseBoolType) (C.MuxTree sym (RefCell JVMObjectType))
  -> C.OverrideSim p sym JVM rtp args ret String
showRef pe = do
    cr <- concretize @JVMRefType (C.RV pe)
    case cr of
      Just cv -> return $ unpack (totext cv)
      Nothing -> return $ "<not a concrete reference>"


-- | Convert a register value to a string
-- Won't necessarily look like a standard types
showReg
  :: forall sym arg p rtp args ret
   . IsSymInterface sym
  => J.Type
  -> TypeRepr arg
  -> C.RegValue sym arg
  -> C.OverrideSim p sym JVM rtp args ret String
showReg jty repr arg
  | Just Refl <- testEquality repr doubleRepr
  = return $ showFloat arg

  | Just Refl <- testEquality repr floatRepr
  = return $ showFloat arg

  | Just Refl <- testEquality repr intRepr
  = return $ showInt jty arg

  | Just Refl <- testEquality repr longRepr
  = return $ showInt jty arg

  | Just Refl <- testEquality repr refRepr
  = showRef arg

  | otherwise
  = error "Internal error: invalid regval type"

printlnMthd
  :: forall sym arg p
   . IsSymInterface sym
  => String
  -> TypeRepr arg
  -> JVMOverride p sym
printlnMthd =
  let showNewline = True in printStream "println" showNewline

printMthd
  :: forall sym arg p
   . IsSymInterface sym
  => String
  -> TypeRepr arg
  -> JVMOverride p sym
printMthd = let showNewline = False in printStream "print" showNewline

printStreamUnit :: forall sym p. (IsSymInterface sym) => String -> Bool -> JVMOverride p sym
printStreamUnit name showNewline =
  let mk = J.makeMethodKey name "()V" in
  JVMOverride { jvmOverride_className="java/io/PrintStream"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=True
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=UnitRepr
                , jvmOverride_def=
                  \_sym args -> do
                    h   <- C.printHandle <$> C.getContext
                    when showNewline (liftIO $ hPutStrLn h "")
                    liftIO $ hFlush h
                }

-- Should we print to the print handle in the simulation context?
-- or just to stdout
printStream
  :: forall sym arg p
   . IsSymInterface sym
  => String {- ^ Actual name of the method that we are invoking -}
  -> Bool   {- ^ should we include a newline at the end -}
  -> String {- ^ java descriptor of argument -}
  -> TypeRepr arg {- ^ expected type of the method -}
  -> JVMOverride p sym
printStream name showNewline descr t =
  let isStatic = False in
  let mk = J.makeMethodKey name descr in
  let argsRepr' = Ctx.Empty `Ctx.extend` refRepr `Ctx.extend` t in
  jvmToFunHandleRepr isStatic mk $ \ argsRepr retRepr ->
    if (testEquality argsRepr argsRepr'  == Nothing)
       then error $ "descriptor does not match type\n " ++ showJVMArgs argsRepr
            ++ "\n vs.\n " ++ showJVMArgs argsRepr'
    else if (testEquality retRepr UnitRepr == Nothing)
       then error "descriptor does not have void return type"
    else JVMOverride { jvmOverride_className="java/io/PrintStream"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr `Ctx.extend` t
                , jvmOverride_ret=UnitRepr
                , jvmOverride_def=
                  \_sym args -> do
                    let reg = C.regValue (Ctx.last args)
                    str <- showReg @sym (head (J.methodKeyParameterTypes mk)) t reg
                    h   <- C.printHandle <$> C.getContext
                    liftIO $ (if showNewline then hPutStrLn else hPutStr) h str
                    liftIO $ hFlush h
                }

flush_override :: (IsSymInterface sym) => JVMOverride p sym
flush_override =
  let isStatic = False in
  let mk = J.makeMethodKey "flush" "()V" in
  JVMOverride   { jvmOverride_className="java/io/BufferedOutputStream"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=UnitRepr
                , jvmOverride_def=
                  \_sym _args -> do
                    h <- C.printHandle <$> C.getContext
                    liftIO $ hFlush h
                }

-- java.lang.Throwable.fillInStackTrace  (i.e. just returns this)
-- REVISIT: We may want to correctly populate the Throwable instance,
-- instead of this just being a pass-through.
fillInStackTrace_override :: (IsSymInterface sym) => JVMOverride p sym
fillInStackTrace_override =
  let isStatic = False in
  let mk = J.makeMethodKey "fillInStackTrace" "()Ljava/lang/Throwable;" in
  JVMOverride   { jvmOverride_className="java/io/BufferedOutputStream"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=refRepr
                , jvmOverride_def=
                  \_sym args -> do
                    let reg = C.regValue (Ctx.last args)
                    return reg
                }

-- OMG This is difficult to define
isArray_override :: forall p sym. (IsSymInterface sym) => JVMOverride p sym
isArray_override =
  let isStatic = False in
  let mk = J.makeMethodKey "isArray" "()Z" in
  JVMOverride   { jvmOverride_className="java/lang/Class"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=intRepr
                , jvmOverride_def=
                  \sym args -> do
                    let reg :: W4.PartExpr (W4.Pred sym) (C.MuxTree sym (RefCell JVMObjectType))
                        reg = C.regValue (Ctx.last args)
                    bvFalse <- liftIO $ return $ W4.bvLit sym knownRepr (BV.zero knownRepr)
{-
                    let k :: RefCell JVMObjectType -> IO (W4.SymBV sym 32)
                        k = undefined
                    let h :: W4.Pred sym -> (W4.SymBV sym 32) -> (W4.SymBV sym 32) -> IO (W4.SymBV sym 32)
                        h = undefined
                    let g :: (C.MuxTree sym (RefCell JVMObjectType)) -> IO (W4.SymBV sym 32)
                                                                     -> IO (W4.SymBV sym 32)
                        g mux curr = undefined
-}
                    liftIO $ foldr undefined bvFalse reg
                }




stdOverrides :: IsSymInterface sym => [JVMOverride p sym]
stdOverrides =
   [  -- printlnMthd "()V"   UnitRepr  -- TODO: methods that take no arguments?
      -- printStreamUnit "println" True
      printlnMthd "(Z)V"  intRepr
    , printlnMthd "(C)V"  intRepr  -- TODO: special case for single char, i.e. binary output
    , printlnMthd "([C)V" refRepr  -- TODO: array of chars
    , printlnMthd "(D)V"  doubleRepr
    , printlnMthd "(F)V"  floatRepr
    , printlnMthd "(I)V"  intRepr
    , printlnMthd "(J)V"  longRepr
    , printlnMthd "(Ljava/lang/Object;)V" refRepr -- TODO: object toString
    , printlnMthd "(Ljava/lang/String;)V" refRepr -- TODO: String objects

    -- , printMthd "()V"   UnitRepr
    -- , printStreamUnit "print" False
    , printMthd "(Z)V"  intRepr
    , printMthd "(C)V"  intRepr  -- TODO: special case for single char, i.e. binary output
    , printMthd "([C)V" refRepr  -- TODO: array of chars
    , printMthd "(D)V"  doubleRepr
    , printMthd "(F)V"  floatRepr
    , printMthd "(I)V"  intRepr
    , printMthd "(J)V"  longRepr
    , printMthd "(Ljava/lang/Object;)V" refRepr -- TODO: object toString
    , printMthd "(Ljava/lang/String;)V" refRepr -- TODO: String objects

    , flush_override
--    , gc_override
    , fillInStackTrace_override
    ]

{-
callPutChar
  :: (IsSymInterface sym)
  => sym
  -> C.RegEntry sym (BVType 32)
  -> C.OverrideSim p sym JVM r args ret (C.RegValue sym (BVType 32))
callPutChar _sym
 (regValue -> ch) = do
    h <- printHandle <$> getContext
    let chval = maybe '?' (toEnum . fromInteger) (asUnsignedBV ch)
    liftIO $ hPutChar h chval
    return ch
-}

{-
callPrintStream
  :: (IsSymInterface sym)
  => sym
  -> C.RegEntry sym (JVMValue s)
  -> C.OverrideSim p sym JVM r args ret (RegValue sym (BVType 32))
callPrintStream sym
  (regValue -> strPtr) = do
      ((str, n), mem') <- liftIO $ runStateT (executeDirectives (printfOps sym valist) ds) mem
      h <- printHandle <$> getContext
      liftIO $ hPutStr h str
      liftIO $ bvLit sym knownNat (toInteger n)

{-
  ( "java/io/PrintStream"
                    ,
                    , MethodBody knownRepr (knownRepr :: TypeRepr UnitType) $
                      -- ReaderT (SimState p sym ext r f a) IO (ExecState p sym ext r)
                      do state <- ask
                         let simctx  = _stateContext state  -- (undefined :: C.SimContext p sym JVM)
                         let tree    = _stateTree state
                         printStream True (t == "(C)V")
                         let globals = C.emptyGlobals
                         let val = (undefined :: _)
                         return $ C.ResultState (C.FinishedResult simctx (C.TotalRes (C.GlobalPair val globals)))
                    --  \_ args -> printStream True (t == "(C)V") args
                    )
-}

printStream :: Bool -> Bool -> [JVMValue s] -> ReaderT (C.SimState p sym ext r f a) IO ()
printStream nl _ []       = liftIO $ (if nl then putStrLn else putStr) "" >> hFlush stdout
printStream nl binary [x] = do
    let putStr' s = liftIO $ (if nl then putStrLn else putStr) s >> hFlush stdout
    case x of
      IValue (asInt sbe -> Just v)
        | binary    -> putStr' [chr $ fromEnum v]
        | otherwise -> putStr' $ show v
      v@IValue{} -> putStr' . render $ ppValue sbe v

      LValue (asLong sbe -> Just v) -> putStr' $ show v
      v@LValue{} -> putStr' . render $ ppValue sbe v
      FValue f -> putStr' (show f)
      DValue d -> putStr' (show d)
      RValue r -> do
        ms <- lookupStringRef r
        case ms of
          Just str  -> putStr' str
          Nothing   -> do
            let key = makeMethodKey "toString" "()Ljava/lang/String;"
            msref <- execInstanceMethod "java/lang/Object" key r []
            case msref of
              Just sref -> putStr' =<< drefString (unRValue sref)
              _ -> err "toString terminated abnormally"
      _ -> abort $ "Unable to display values of type other than "
                 ++ "int, long, and reference to constant string"
printStream _ _ _ = abort $ "Unable to print more than one argument"
-}

{-

data MethodBody p sym = forall (args :: Ctx CrucibleType) (ret :: CrucibleType).
  MethodBody
    (CtxRepr args)
    (TypeRepr ret)
    (forall r. C.ExecCont p sym JVM r (C.OverrideLang ret) (Just args))


overrideInstanceMethod :: HandleAllocator s -> J.ClassName -> J.MethodKey -> MethodBody p sym ->
   ST s (C.FnBinding p sym JVM)
overrideInstanceMethod halloc cn mk (MethodBody argsRepr retRepr code) = do
   let funName = fromString (J.unClassName cn ++ "." ++ J.methodKeyName mk)
   handle <- mkHandle' halloc funName argsRepr retRepr
   let override = C.Override funName code
   return $ C.FnBinding handle (C.UseOverride override)

overrideStaticMethod = undefined


-- | Register all predefined overrides for builtin native implementations.
stdOverrides :: HandleAllocator s -> ST s (C.FunctionBindings p sym JVM)
stdOverrides halloc = do
  mapM_ (\(cn, key, impl) -> overrideInstanceMethod halloc cn key impl)
    [ printlnMthd "()V"
    , printlnMthd "(Z)V"
    , printlnMthd "(C)V"
    , printlnMthd "([C)V"
    , printlnMthd "(D)V"
    , printlnMthd "(F)V"
    , printlnMthd "(I)V"
    , printlnMthd "(J)V"
    , printlnMthd "(Ljava/lang/Object;)V"
    , printlnMthd "(Ljava/lang/String;)V"
    , printMthd   "(Z)V"
    , printMthd   "(C)V"
    , printMthd   "([C)V"
    , printMthd   "(D)V"
    , printMthd   "(F)V"
    , printMthd   "(I)V"
    , printMthd   "(J)V"
    , printMthd   "(Ljava/lang/Object;)V"
    , printMthd   "(Ljava/lang/String;)V"
    , appendIntegralMthd "(I)Ljava/lang/StringBuilder;"
    , appendIntegralMthd "(J)Ljava/lang/StringBuilder;"
    -- java.io.BufferedOutputStream.flush
    , ( "java/io/BufferedOutputStream"
      , J.makeMethodKey "flush" "()V"
      , \_ _ -> liftIO $ hFlush stdout
      )
    -- java.lang.Runtime.gc
    , ( "java/lang/Runtime"
      , J.makeMethodKey "gc" "()V"
      -- Should we implement a garbage collector? ;)
      , \_ _ -> return ()
      )
    -- java.lang.Throwable.fillInStackTrace
    -- REVISIT: We may want to correctly populate the Throwable instance,
    -- instead of this just being a pass-through.
    , ( "java/lang/Throwable"
      , J.makeMethodKey "fillInStackTrace" "()Ljava/lang/Throwable;"
      , \this _ -> pushValue (RValue this)
      )
    -- java.lang.Class.isArray
    , ( "java/lang/Class"
      , J.makeMethodKey "isArray" "()Z"
      , \this _ -> pushValue =<< classNameIsArray =<< getClassName this
      )
    -- java.lang.Class.isPrimitive
    , ( "java/lang/Class"
      , J.makeMethodKey "isPrimitive" "()Z"
      , \this _ -> pushValue =<< classNameIsPrimitive =<< getClassName this
      )
    -- java.lang.Class.getComponentType
    , ( "java/lang/Class"
      , J.makeMethodKey "getComponentType" "()Ljava/lang/Class;"
      , \this _ -> do
          nm <- getClassName this
          pushValue =<< RValue
                        <$> if classNameIsArray' nm
                            then getJVMClassByName (mkClassName (tail nm)) -- BH: why tail?
                            else return NullRef
      )
    -- java.lang.class.getClassLoader -- REVISIT: This implementation makes it so
    -- that custom class loaders are not supported.
    , ( "java/lang/Class"
      , J.makeMethodKey "getClassLoader" "()Ljava/lang/ClassLoader;"
      , \_ _ -> pushValue (RValue NullRef)
      )
    -- java.lang.String.intern -- FIXME (must reconcile reference w/ strings map)
    , ( "java/lang/String"
      , J.makeMethodKey "intern" "()Ljava/lang/String;"
      , \this _ -> pushValue =<< RValue <$> (refFromString =<< drefString this)
      )
    ]

  --------------------------------------------------------------------------------
  -- Static method overrides

  mapM_ (\(cn, key, impl) -> overrideStaticMethod cn key impl)
    [ -- Java.lang.System.arraycopy
      let arrayCopyKey =
            J.makeMethodKey "arraycopy"
              "(Ljava/lang/Object;ILjava/lang/Object;II)V"
      in
        ( "java/lang/System"
        , arrayCopyKey
        , \opds -> do
            let nativeClass = "com/galois/core/NativeImplementations"
            pushStaticMethodCall nativeClass arrayCopyKey opds Nothing
        )
      -- java.lang.System.exit(int status)
    , fillArrayMethod "([ZZ)V"
    , fillArrayMethod "([ZIIZ)V"
    , fillArrayMethod "([BB)V"
    , fillArrayMethod "([BIIB)V"
    , fillArrayMethod "([CC)V"
    , fillArrayMethod "([CIIC)V"
    , fillArrayMethod "([DD)V"
    , fillArrayMethod "([DIID)V"
    , fillArrayMethod "([FF)V"
    , fillArrayMethod "([FIIF)V"
    , fillArrayMethod "([II)V"
    , fillArrayMethod "([IIII)V"
    , fillArrayMethod "([JJ)V"
    , fillArrayMethod "([JIIJ)V"
    , fillArrayMethod "([SS)V"
    , fillArrayMethod "([SIIS)V"
    , fillArrayMethod "([Ljava/lang/Object;Ljava/lang/Object;)V"
    , fillArrayMethod "([Ljava/lang/Object;IILjava/lang/Object;)V"
    , ( "java/lang/System"
      , J.makeMethodKey "exit" "(I)V"
      , \[IValue status] -> do
          sbe <- use backend
          let codeStr = case asInt sbe status of
                          Nothing -> "unknown exit code"
                          Just code -> "exit code " ++ show code
          errorPath . FailRsn
            $ "java.lang.System.exit(int status) called with " ++ codeStr
      )
      -- java.lang.Float.floatToRawIntBits: override for invocation by
      -- java.lang.Math's static initializer
    , ( "java/lang/Float"
      , J.makeMethodKey "floatToRawIntBits" "(F)I"
      , \args -> case args of
                   [FValue flt] -> do
                     when (flt /= (-0.0 :: Float)) $
                       abort "floatToRawIntBits: overridden for -0.0f only"
                     pushValue =<< IValue <$>
                       App $ LitInt (fromIntegral (0x80000000 :: Word32))
                   _ -> abort "floatToRawIntBits: called with incorrect arguments"
      )
      -- java.lang.Double.doubleToRawLongBits: override for invocation by
      -- java.lang.Math's static initializer
    , ( "java/lang/Double"
      , J.makeMethodKey "doubleToRawLongBits" "(D)J"
      , \args -> case args of
                   [DValue dbl] -> do
                     when (dbl /= (-0.0 :: Double)) $
                       abort "doubltToRawLongBits: overriden -0.0d only"
                     pushValue =<< withSBE (\sbe -> LValue <$>
                                             termLong sbe (fromIntegral (0x8000000000000000 :: Word64)))
                   _ -> abort "floatToRawIntBits: called with incorrect arguments"
      )
      -- Set up any necessary state for the native methods of various
      -- classes. At the moment, nothing is necessary.
    , ( "java/lang/Class"
      , J.makeMethodKey "registerNatives" "()V"
      , \_ -> return ()
      )
    , ( "java/lang/ClassLoader"
      , J.makeMethodKey "registerNatives" "()V"
      , \_ -> return ()
      )
    , ( "java/lang/Thread"
      , J.makeMethodKey "registerNatives" "()V"
      , \_ -> return ()
      )
    , ( "java/lang/Class"
      , J.makeMethodKey "desiredAssertionStatus0" "(Ljava/lang/Class;)Z"
      , \_ -> pushValue =<< withSBE (\sbe -> IValue <$> termInt sbe 1)
      )
    , ( "java/lang/Class"
      , J.makeMethodKey "getPrimitiveClass" "(Ljava/lang/String;)Ljava/lang/Class;"
      , \args -> error "TODO: look at simulator code"
      )
    , ( "java/io/FileInputStream", J.makeMethodKey "initIDs" "()V", \ _ -> return () )
    , ( "java/io/FileOutputStream", J.makeMethodKey "initIDs" "()V", \ _ -> return () )
    , ( "java/io/RandomAccessFile", J.makeMethodKey "initIDs" "()V", \ _ -> return () )
    , ( "java/io/ObjectStreamClass", J.makeMethodKey "initNative" "()V", \ _ -> return () )
    , ( "java/security/AccessController"
      , J.makeMethodKey "doPrivileged" "(Ljava/security/PrivilegedAction;)Ljava/lang/Object;"
      , \args -> error "TODO: look at static simulator code"
      )
    , ( "java/lang/System", J.makeMethodKey "nanoTime" "()J", \ _ -> do
          dbugM "warning: long java.lang.System.nanoTime() always returns 0 during symbolic execution"
          pushValue =<< withSBE (\sbe -> LValue <$> termLong sbe 0)
      )
    , ( "java/lang/System", J.makeMethodKey "currentTimeMillis" "()J", \ _ -> do
          whenVerbosity (>=2)
          pushValue =<< withSBE (\sbe -> LValue <$> termLong sbe 0)
      )
    , ( "java/lang/System", J.makeMethodKey "identityHashCode" "(Ljava/lang/Object;)I", \ _ -> do
          dbugM "warning: int java.lang.System.identityHashCode(Object) always returns 0 during symbolic executin"
          pushValue =<< withSBE (\sbe -> IValue <$> termInt sbe 0)
      )

    -- Here we override the "valueOf" methods that are used for autoboxing primitive types.
    -- We do this because these methods are defined to use a lookup table cache; if we attempt
    -- to autobox a symbolic value, this results in indexing a reference array by a symbolic
    -- value, which is not allowed.  Instead, we override these methods to just directly call
    -- the appropriate class constructor.

    , ( "java/lang/Boolean", J.makeMethodKey "valueOf" "(Z)Ljava/lang/Boolean;", \([IValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Boolean" (Just [(BooleanType, IValue x)])
      )
    , ( "java/lang/Byte", J.makeMethodKey "valueOf" "(B)Ljava/lang/Byte;", \([IValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Byte" (Just [(ByteType, IValue x)])
      )
    , ( "java/lang/Short", J.makeMethodKey "valueOf" "(S)Ljava/lang/Short;", \([IValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Short" (Just [(ShortType, IValue x)])
      )
    , ( "java/lang/Integer", J.makeMethodKey "valueOf" "(I)Ljava/lang/Integer;", \([IValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Integer" (Just [(IntType, IValue x)])
      )
    , ( "java/lang/Long", J.makeMethodKey "valueOf" "(J)Ljava/lang/Long;", \([LValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Long" (Just [(LongType, LValue x)])
      )
    ]
  where
    printlnMthd t = ( "java/io/PrintStream"
                    , J.makeMethodKey "println" t
                    , MethodBody knownRepr (knownRepr :: TypeRepr UnitType) $
                      -- ReaderT (SimState p sym ext r f a) IO (ExecState p sym ext r)
                      do state <- ask
                         let simctx  = _stateContext state  -- (undefined :: C.SimContext p sym JVM)
                         let tree    = _stateTree state
                         printStream True (t == "(C)V")
                         let globals = C.emptyGlobals
                         let val = (undefined :: _)
                         return $ C.ResultState (C.FinishedResult simctx (C.TotalRes (C.GlobalPair val globals)))
                    --  \_ args -> printStream True (t == "(C)V") args
                    )
    printMthd t   = ( "java/io/PrintStream"
                    , J.makeMethodKey "print" t
                    , \_ args -> printStream False (t == "(C)V") args
                    )
    fillArrayMethod t =
      ( "java/util/Arrays"
      , J.makeMethodKey "fill" t
      , \args ->
          case args of
            [RValue ref, val] -> fillArray ref Nothing val
            [RValue ref, beg, end, val] -> fillArray ref (Just (beg, end)) val
            _ -> abort "Arrays.fill called with invalid args"
      )

    -- | Allows the user to append pretty-printed renditions of symbolic
    -- ints/longs as strings; however, we should REVISIT this.  Concatenation of
    -- the typical form form ("x = " + x) where x is symbolic is currently very
    -- inefficient since the concrete string representation of x is still
    -- executed through many array operations in the {Abstract,}StringBuilder
    -- implementations and so forth.  This leads to the odd situation where:
    --
    -- System.out.print("x = ");
    -- System.out.println(x);
    --
    -- is vastly more efficient than the equivalent concatenating version.
    appendIntegralMthd t =
      let cn = "java/lang/StringBuilder"
      in
        ( cn
        , makeMethodKey "append" t
        , \this [st] -> do
            let redir = makeMethodKey "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;"
                warn  = dbugM $
                  "Warning: string concatenation of symbolic variables is "
                    ++ "very inefficient in this release. \n  Consider using "
                    ++ "'System.out.print(\"x = \"); System.out.println(x);'"
                    ++ "\n  instead of 'System.out.println(\"x = \" + x); "
                    ++ "also see Symbolic.Debug.trace()."
            sbe <- use backend
            case st of
              IValue (asInt sbe -> Just{}) -> return ()
              LValue (asLong sbe -> Just{}) -> return ()
              _ -> warn
            sr        <- refFromString . render . ppValue sbe $ st
            void $ execInstanceMethod cn redir this [RValue sr]
        )

--}
