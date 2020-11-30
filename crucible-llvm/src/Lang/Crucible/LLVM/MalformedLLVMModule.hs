module Lang.Crucible.LLVM.MalformedLLVMModule where

import qualified Control.Exception as X
import           Data.Void

import           Prettyprinter

------------------------------------------------------------------------
-- MalformedLLVMModule

-- | This datatype represents an exception that occurs when an LLVM module
--   is broken in some way; for example, if the types of expressions do
--   not match up in some way.  The first argument is a short description
--   of the error, and the remaining arguments are any additional details
--   describing the error.
data MalformedLLVMModule
  = MalformedLLVMModule (Doc Void) [Doc Void]

instance X.Exception MalformedLLVMModule

instance Show MalformedLLVMModule where
  show = show . renderMalformedLLVMModule

-- Throw a @MalformedLLVMModule@ exception
malformedLLVMModule :: Doc Void -> [Doc Void] -> a
malformedLLVMModule short details = X.throw (MalformedLLVMModule short details)

-- Render a @MalformedLLVMModule@ exception as a pretty printer document
renderMalformedLLVMModule :: MalformedLLVMModule -> Doc Void
renderMalformedLLVMModule (MalformedLLVMModule short details) =
  vcat [short, indent 2 (vcat details)]
