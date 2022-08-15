{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}


module OSL.BuildTranslationContext
  ( buildTranslationContext
  , addFreeVariableMapping
  , addToTranslationContext
  , getFreeVariables
  , getBoundS11NamesInContext
  , getBoundS11NamesInMapping
  , getFreeS11Name
  ) where


import Control.Lens ((^.))
import Control.Monad (forM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans.State.Strict (StateT, execStateT, modify, get)
import Data.Functor.Identity (runIdentity)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import OSL.Die (die)
import OSL.Type (typeAnnotation)
import OSL.Types.Arity (Arity (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Declaration (..), Type (..), ValidContext (..))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.TranslationContext (TranslationContext (..), Mapping (..), LeftMapping (..), RightMapping (..), ChoiceMapping (..), LengthMapping (..), ValuesMapping (..), KeysMapping (..), KeyIndicatorMapping (..))
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
        N _ -> addToTranslationContext
               freeVariable
               =<< (ScalarMapping <$> getFreeS11NameM (Arity 0))
        _ -> todo
    _ -> die "logically impossible: free variable is not a free variable"


addToTranslationContext
  :: Monad m
  => OSL.Name
  -> Mapping
  -> StateT TranslationContext m ()
addToTranslationContext name mapping =
  modify
    ( TranslationContext
    . Map.insert name mapping
    . unTranslationContext )


getFreeVariables :: ValidContext ann -> [OSL.Name]
getFreeVariables (ValidContext decls) =
  Map.keys (Map.filter isFree decls)
  where
    isFree (FreeVariable _) = True
    isFree _ = False


getBoundS11NamesInContext :: Arity -> TranslationContext -> Set S11.Name
getBoundS11NamesInContext arity (TranslationContext ctx) =
  Map.foldl' Set.union Set.empty
    $ getBoundS11NamesInMapping arity <$> ctx


getBoundS11NamesInMapping :: Arity -> Mapping -> Set S11.Name
getBoundS11NamesInMapping arity =
  \case
    ScalarMapping name -> f name
    ProductMapping (LeftMapping a) (RightMapping b) ->
      rec a `Set.union` rec b
    CoproductMapping (ChoiceMapping a)
        (LeftMapping b) (RightMapping c) ->
      f a `Set.union` (rec b `Set.union` rec c)
    ListMapping (LengthMapping a) (ValuesMapping b) ->
      f a `Set.union` rec b
    MapMapping (LengthMapping a) (KeysMapping b)
        (KeyIndicatorMapping c) (ValuesMapping d) ->
      f a `Set.union` (rec b `Set.union` (f c `Set.union` rec d))
  where
    f :: S11.Name -> Set S11.Name
    f name =
      if name ^. #arity == arity
      then Set.singleton name
      else Set.empty

    rec = getBoundS11NamesInMapping arity


getFreeS11Name :: Arity -> TranslationContext -> S11.Name
getFreeS11Name arity ctx =
  fromMaybe (S11.Name arity (DeBruijnIndex 0))
    . fmap (S11.Name arity . (+1) . (^. #deBruijnIndex))
    $ Set.lookupMax (getBoundS11NamesInContext arity ctx)


getFreeS11NameM
  :: Monad m
  => Arity
  -> StateT TranslationContext m S11.Name
getFreeS11NameM arity =
  getFreeS11Name arity <$> get


todo :: a
todo = todo
