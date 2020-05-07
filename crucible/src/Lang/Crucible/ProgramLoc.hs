-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.ProgramLoc
-- Description      : Datatype for handling program locations
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module primarily defines the `Position` datatype for
-- handling program location data.  A program location may refer
-- either to a source file location (file name, line and column number),
-- a binary file location (file name and byte offset) or be a dummy
-- "internal" location assigned to generated program fragments.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Lang.Crucible.ProgramLoc
  ( Position(..)
  , sourcePos
  , startOfFile
  , ppNoFileName
  , Posd(..)
  , ProgramLoc
  , mkProgramLoc
  , initializationLoc
  , plFunction
  , plSourceLoc
    -- * Objects with a program location associated.
  , HasProgramLoc(..)
  ) where

import           Control.Lens
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import           Numeric (showHex)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lang.Crucible.FunctionName

------------------------------------------------------------------------
-- Position

data Position
     -- | A source position containing filename, line, and column.
   = SourcePos !Text !Int !Int
     -- | A binary position containing a filename and address in memory.
   | BinaryPos !Text !Word64
     -- | Some unstructured position information that doesn't fit into the other categories.
   | OtherPos !Text
     -- | Generated internally by the simulator, or otherwise unknown.
   | InternalPos
  deriving (Eq, Ord)

instance Show Position where
  show p = show (PP.pretty p)

sourcePos :: FilePath -> Int -> Int -> Position
sourcePos p l c = SourcePos (Text.pack p) l c

startOfFile :: FilePath -> Position
startOfFile path = sourcePos path 1 0

instance PP.Pretty Position where
  pretty (SourcePos path l c) =
    PP.text (Text.unpack path)
      PP.<> PP.colon PP.<> PP.int l
      PP.<> PP.colon PP.<> PP.int c
  pretty (BinaryPos path addr) =
    PP.text (Text.unpack path) PP.<> PP.colon PP.<>
      PP.text "0x" PP.<> PP.text (showHex addr "")
  pretty (OtherPos txt) = PP.text (Text.unpack txt)
  pretty InternalPos = PP.text "internal"

ppNoFileName :: Position -> PP.Doc
ppNoFileName (SourcePos _ l c) =
  PP.int l PP.<> PP.colon PP.<> PP.int c
ppNoFileName (BinaryPos _ addr) =
  PP.text (showHex addr "")
ppNoFileName (OtherPos msg) =
  PP.text (Text.unpack msg)
ppNoFileName InternalPos = PP.text "internal"

------------------------------------------------------------------------
-- Posd

-- | A value with a source position associated.
data Posd v = Posd { pos :: !Position
                   , pos_val :: !v
                   }
  deriving (Functor, Foldable, Traversable, Show, Eq)

------------------------------------------------------------------------
-- ProgramLoc

-- | A very small type that contains a function and PC identifier.
data ProgramLoc
   = ProgramLoc { plFunction :: {-# UNPACK #-} !FunctionName
                , plSourceLoc :: !Position
                }
 deriving (Show, Eq, Ord)


instance PP.Pretty ProgramLoc where
  pretty = PP.pretty . plSourceLoc


-- | Location for initialization code
initializationLoc :: ProgramLoc
initializationLoc = ProgramLoc startFunctionName (startOfFile "")

-- | Make a program loc
mkProgramLoc :: FunctionName
             -> Position
             -> ProgramLoc
mkProgramLoc = ProgramLoc

------------------------------------------------------------------------
-- HasProgramLoc

class HasProgramLoc v where
  programLoc :: Lens' v ProgramLoc
