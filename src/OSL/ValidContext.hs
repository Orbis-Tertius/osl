{-# LANGUAGE OverloadedStrings #-}

module OSL.ValidContext
  ( getDeclaration,
    getExistingDeclaration,
    addDeclaration,
  )
where

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (pack)
import Die (die)
import OSL.Types.OSL (Declaration, Name, ValidContext (..))

getDeclaration :: ValidContext t ann -> Name -> Maybe (Declaration ann)
getDeclaration (ValidContext decls) name = Map.lookup name decls

getExistingDeclaration ::
  ValidContext t ann ->
  Name ->
  Declaration ann
getExistingDeclaration c name =
  fromMaybe
    (die $ "logically impossible: could not find a declaration known to exist: " <> pack (show name))
    (getDeclaration c name)

addDeclaration ::
  Name ->
  Declaration ann ->
  ValidContext t ann ->
  ValidContext t ann
addDeclaration name decl (ValidContext c) =
  ValidContext (Map.insert name decl c)
