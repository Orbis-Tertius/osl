module OSL.ValidContext (getDeclaration) where


import qualified Data.Map as Map

import OSL.Types.OSL (ValidContext (..), Name, Declaration)


getDeclaration :: ValidContext ann -> Name -> Maybe (Declaration ann)
getDeclaration (ValidContext decls) name = Map.lookup name decls
