{-# LANGUAGE OverloadedStrings #-}


module OSL.ValidContext
  ( getDeclaration
  , getExistingDeclaration
  , addDeclaration
  ) where


import qualified Data.Map as Map

import OSL.Die (die)
import OSL.Types.OSL (ValidContext (..), Name, Declaration)


getDeclaration :: ValidContext ann -> Name -> Maybe (Declaration ann)
getDeclaration (ValidContext decls) name = Map.lookup name decls


getExistingDeclaration
  :: ValidContext ann
  -> Name
  -> Declaration ann
getExistingDeclaration c =
  (die "logically impossible: could not find a declaration known to exist")
  . getDeclaration c


addDeclaration
  :: Name
  -> Declaration ann
  -> ValidContext ann
  -> ValidContext ann 
addDeclaration name decl (ValidContext c) =
  ValidContext (Map.insert name decl c)
