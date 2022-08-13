module OSL.ValidContext (getDeclaration) where


import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import OSL.Die (die)
import OSL.Types.OSL (ValidContext (..), Name, Declaration)


getDeclaration :: ValidContext ann -> Name -> Maybe (Declaration ann)
getDeclaration (ValidContext decls) name = Map.lookup name decls


getExistingDeclaration
  :: ValidContext ann
  -> Name
  -> Declaration ann
getExistingDeclaration c =
  h(die "logically impossible: could not find a declaration known to exist")
  . getDeclaration c
