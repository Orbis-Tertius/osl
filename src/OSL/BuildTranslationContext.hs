{-# LANGUAGE OverloadedStrings #-}


module OSL.BuildTranslationContext
  ( buildTranslationContext
  , getFreeS11Name
  ) where


import Control.Monad (forM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans.State.Strict (StateT, execStateT)
import Data.Functor.Identity (runIdentity)
import qualified Data.Map as Map

import OSL.Die (die)
import OSL.Type (typeAnnotation)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Declaration (..), Type (..), ValidContext (..))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.TranslationContext (TranslationContext (..))
import OSL.ValidContext (getExistingDeclaration)


-- builds a translation context providing mappings
-- for all of the free variables in the given context.
buildTranslationContext
  :: ValidContext ann
  -> Either (ErrorMessage ann) TranslationContext
buildTranslationContext c =
  let freeVariables = getFreeVariables c
  in runIdentity $
     runExceptT
       (execStateT
         (forM_
           freeVariables
           (addFreeVariableMapping c))
         (TranslationContext mempty))


addFreeVariableMapping
  :: Monad m
  => ValidContext ann
  -> OSL.Name
  -> StateT TranslationContext (ExceptT (ErrorMessage ann) m) ()
addFreeVariableMapping c freeVariable = do
  let decl = getExistingDeclaration c freeVariable
  case decl of
    FreeVariable t ->
      case t of
        Prop _ -> lift . ExceptT . pure . Left
          $ ErrorMessage (typeAnnotation t)
            "free Prop variable"
        N _ -> todo -- ScalarMapping <$> getFreeS11Name t
        _ -> todo
    _ -> die "logically impossible: free variable is not a free variable"


getFreeVariables :: ValidContext ann -> [OSL.Name]
getFreeVariables (ValidContext decls) =
  Map.keys (Map.filter isFree decls)
  where
    isFree (FreeVariable _) = True
    isFree _ = False


getFreeS11Name :: TranslationContext -> S11.Name
getFreeS11Name = todo


todo :: a
todo = todo
