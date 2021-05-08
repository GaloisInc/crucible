{- |
Module           : Lang.Crucible.JVM.Context
Description      : JVM context with information about methods and fields
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : huffman@galois.com, sweirich@galois.com
Stability        : provisional
-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -haddock #-}

module Lang.Crucible.JVM.Context where

-- base
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- jvm-parser
import qualified Language.JVM.Parser as J

-- crucible
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types

-- crucible-jvm
import           Lang.Crucible.JVM.Types

----------------------------------------------------------------------
-- * JVMContext


type StaticFieldTable = Map J.FieldId (GlobalVar JVMValueType, GlobalVar BoolType)
type MethodHandleTable = Map (J.ClassName, J.MethodKey) JVMHandleInfo

data JVMHandleInfo where
  JVMHandleInfo :: J.MethodKey -> FnHandle init ret -> JVMHandleInfo

-- | Contains information about crucible function handles and global variables
-- that is statically known during the class translation.
data JVMContext = JVMContext
  { methodHandles :: Map (J.ClassName, J.MethodKey) JVMHandleInfo
      -- ^ Map from static and dynamic methods to Crucible function handles.
  , staticFields :: Map J.FieldId (GlobalVar JVMValueType, GlobalVar BoolType)
      -- ^ Map from static field names to Crucible global variables.
      -- Each static field is paired with a permission bit for writability.
      -- We know about these fields at translation time so we can allocate
      -- global variables to store them.
  , classTable :: Map J.ClassName J.Class
      -- ^ Map from class names to their declarations.
      -- This contains all of the information about class declarations at
      -- translation time.
  , dynamicClassTable :: GlobalVar JVMClassTableType
      -- ^ A global variable storing information about the class that can be
      -- used at runtime: includes initialization status, superclass (if any),
      -- and a map from method names to their handles for dynamic dispatch.
  }

-- | Left-biased merge of two contexts.
-- NOTE: There should only ever be one dynamic class table global variable.
instance Semigroup JVMContext where
  c1 <> c2 =
    JVMContext
    { methodHandles     = Map.union (methodHandles   c1) (methodHandles   c2)
    , staticFields      = Map.union (staticFields c1) (staticFields c2)
    , classTable        = Map.union (classTable  c1) (classTable  c2)
    , dynamicClassTable = dynamicClassTable c1
    }

