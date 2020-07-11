{- |

Module           : Lang.Crucible.JVM.ClassRefs
Description      : Determine class names referred to by JVM abstract syntax
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : sweirich@galois.com
Stability        : provisional

-}

module Lang.Crucible.JVM.ClassRefs where

import Data.List ( isPrefixOf )
import GHC.Stack (HasCallStack)

import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J
import Data.Set (Set)
import qualified Data.Set as Set

-- | Calculate the set of class names referred to in a particular
-- piece of JVM abstract syntax.
class ClassRefs a where
  classRefs :: HasCallStack => a -> Set J.ClassName


instance ClassRefs a => ClassRefs (Maybe a) where
  classRefs = maybe mempty classRefs

instance ClassRefs a => ClassRefs [a] where
  classRefs = foldMap classRefs

--
instance ClassRefs J.ClassName where
  classRefs cn =
    if "[" `isPrefixOf` J.unClassName cn then
      error $ "INVALID classname " ++ show cn
    else
      Set.singleton cn

instance ClassRefs J.Type where
  classRefs ty =
    case ty of
      J.ClassType cn  -> classRefs cn
      J.ArrayType arr -> classRefs arr
      _               -> mempty

instance ClassRefs J.ConstantPoolValue where
  classRefs val =
    case val of
      J.String  _s  -> Set.singleton (J.mkClassName "java/lang/String")
-- These classnames are actually class descriptors (such as [Ljava.lang.Object;)
-- and unparsed. We drop them for now
--    J.ClassRef cn -> classRefs cn
      _             -> mempty

instance ClassRefs J.Field where
  classRefs field =
    classRefs (J.fieldType field) <>
    classRefs (J.fieldConstantValue field)

instance ClassRefs J.Method where
  classRefs meth =
    classRefs (J.methodParameterTypes meth) <>
    classRefs (J.methodReturnType meth)     <>
    classRefs (J.methodBody meth)

instance ClassRefs J.MethodBody where
  classRefs (J.Code _ _ cfg _ _ _ _) = classRefs cfg
  classRefs _ = Set.empty

instance ClassRefs J.CFG where
  classRefs cfg = classRefs (J.allBBs cfg)

instance ClassRefs J.BasicBlock where
  classRefs bb =
    classRefs (map snd (J.bbInsts bb))

instance ClassRefs J.FieldId where
  classRefs fieldId = classRefs (J.fieldIdClass fieldId)

instance ClassRefs J.MethodKey where
  classRefs methodKey =
     classRefs (J.methodKeyParameterTypes methodKey) <>
     classRefs (J.methodKeyReturnType     methodKey)

instance ClassRefs J.Instruction where
  classRefs inst =
    case inst of
    J.Checkcast  ty -> classRefs ty
    J.Getfield  fieldId -> classRefs fieldId
    J.Getstatic fieldId -> classRefs fieldId
    J.Instanceof ty -> classRefs ty
    J.Invokeinterface cn mk -> classRefs cn <> classRefs mk
    J.Invokespecial   ty mk -> classRefs ty <> classRefs mk
    J.Invokestatic    cn mk -> classRefs cn <> classRefs mk
    J.Invokevirtual   ty mk -> classRefs ty <> classRefs mk
    J.Ldc cpv -> classRefs cpv
    J.Multianewarray ty _word8 -> classRefs ty
    J.New cn -> classRefs cn
    J.Newarray ty -> classRefs ty
    J.Putfield  fieldId -> classRefs fieldId
    J.Putstatic fieldId -> classRefs fieldId
    _ -> mempty


instance ClassRefs J.Class where
  classRefs cls =
    classRefs (J.superClass cls)  <>
    classRefs (J.classFields cls) <>
    classRefs (J.classMethods cls)
