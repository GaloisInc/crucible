module Crux.Version where

import Data.Version (showVersion)
import qualified Paths_crux (version)

version :: String
version = showVersion Paths_crux.version


