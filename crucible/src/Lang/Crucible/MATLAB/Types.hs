{-
Module           : Lang.Crucible.MATLAB.Types
Copyright        : (c) Galois, Inc 2015-2016
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines basic types specific to MATLAB.
-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.MATLAB.Types
 ( MatlabFunctionHandleType
 , MatlabMethodHandleType
 , MatlabClassIdentType
 , MatlabMethodNameType
 , MatlabPropNameType
 , MatlabPropertiesType

 , MatlabFunctionBaseArgs
 , MatlabMethodBaseArgs
 , MatlabFunctionReturnType
 , MatlabFunctionFullArgs
 , MatlabClosureHandle
 , MatlabFunctionHandle
 , MatlabMethodHandle
 , MatlabHandleFields
 , MatlabHandle
 ) where

import           Control.Monad.Identity
import qualified Data.Parameterized.Context as Ctx
import           Data.Text (Text)

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types


-- | Crucible type for Matlab function handles
--
-- Arguments: are the values passed, the number of expected return values,
-- and the number of inputs.
type MatlabFunctionHandleType
   = FunctionHandleType MatlabFunctionBaseArgs MatlabFunctionReturnType

-- | Crucible type for method handles
--
-- Arguments are: the values passed, the number of expected return values,
-- and the self object.
type MatlabMethodHandleType
   = FunctionHandleType MatlabMethodBaseArgs MatlabFunctionReturnType

-- | A type for Matlab class and property names
type MatlabClassIdentType = StringType
type MatlabPropNameType   = StringType
type MatlabMethodNameType = StringType

-- | Type for lists of property identifiers
type MatlabPropertiesType = VectorType StringType

------------------------------------------------------------------------
-- Matlab argument types

-- | A type context for arguments to a matlab function
--   that do not include any captured free variables.
type MatlabFunctionBaseArgs
   = EmptyCtx
   ::> VectorType MatlabValueType  -- Arguments to function
   ::> NatType                     -- Number of outputs expected
   ::> IdentValueMapType           -- Identifiers in calling context (used by exist)
   ::> NatType                     -- Number of arguments in calling frame (used by nargin)

-- | A type context for arguments to a matlab method. Methods are treated
--   as a special case because of the 'object goes first' calling convention.
type MatlabMethodBaseArgs
  = MatlabFunctionBaseArgs
  ::> MatlabObjectType

-- | The type of return values from matlab functions.  Functions may
--   have multiple return values, and may be selectively omitted by returning `Nothing`
type MatlabFunctionReturnType
   = VectorType (MaybeType MatlabValueType)

-- | A type context for the "full" arguments of a function.  These include
--   any free variables inside lambdas that become captured into closures when
--   anonymous functions are lifted out of the function bodies in which they occur.
type MatlabFunctionFullArgs
   = MatlabFunctionBaseArgs
   ::> VectorType (MaybeType MatlabValueType) -- Captured arguments

-- | A CFG handle to a matlab function.  The function signature includes the formal
--   arguments to the top-level named function as well as any captured free variables
--   in anonymous functions.
type MatlabClosureHandle = FnHandle MatlabFunctionFullArgs MatlabFunctionReturnType

-- | A CFG handle to a top-level matlab function.  The function signature includes
--   only the formal arguments to the top-level named function.
type MatlabFunctionHandle = FnHandle MatlabFunctionBaseArgs MatlabFunctionReturnType

-- | Similar to 'MatlabFunctionHandle' but with slightly different base args
-- to allow for the object to play a special role as the first argument to the
-- method.
type MatlabMethodHandle = FnHandle MatlabMethodBaseArgs MatlabFunctionReturnType

-- | Data pertaining to a top-level matlab function.  These include
--   the handle to the function itself, the name of the first return value,
--   and the number of arguments the function expects.
type MatlabHandleFields
   = EmptyCtx
   ::> MatlabFunctionHandle
   ::> Text
   ::> Int

type MatlabHandle = Ctx.Assignment Identity MatlabHandleFields
