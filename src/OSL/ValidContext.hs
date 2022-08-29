{-# LANGUAGE OverloadedStrings #-}


module OSL.ValidContext
  ( getDeclaration
  , getExistingDeclaration
  , addDeclaration
  ) where


import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (pack)

import OSL.Die (die)
import OSL.Types.OSL (ValidContext (..), Name, Declaration)


getDeclaration :: ValidContext ann -> Name -> Maybe (Declaration ann)
getDeclaration (ValidContext decls) name = Map.lookup name decls


getExistingDeclaration
  :: ValidContext ann
  -> Name
  -> Declaration ann
getExistingDeclaration c name =
  fromMaybe
  (die $ "logically impossible: could not find a declaration known to exist: " <> pack (show name))
  (getDeclaration c name)


addDeclaration
  :: Name
  -> Declaration ann
  -> ValidContext ann
  -> ValidContext ann 
addDeclaration name decl (ValidContext c) =
  ValidContext (Map.insert name decl c)
