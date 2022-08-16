{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}


module OSL.BuildTranslationContext
  ( buildTranslationContext
  , addFreeVariableMapping
  , addMapping
  , addFreeVariableDeclaration
  , getFreeVariables
  , getBoundS11NamesInContext
  , getBoundS11NamesInMapping
  , getFreeS11Name
  , getFreeS11NameM
  , addGensym
  , getFreeOSLName
  ) where


import Control.Lens ((^.), (%~))
import Control.Monad (forM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT, except, throwE)
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
import OSL.Types.OSL (Declaration (..), Type (..), ValidContext (..), Name (Sym, GenSym))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.TranslationContext (TranslationContext (..), Mapping (..), LeftMapping (..), RightMapping (..), ChoiceMapping (..), LengthMapping (..), ValuesMapping (..), KeysMapping (..), KeyIndicatorMapping (..))
import OSL.ValidContext (getExistingDeclaration, addDeclaration)


-- builds a translation context providing mappings
-- for all of the free variables in the given context.
buildTranslationContext
  :: ValidContext ann
  -> Either (ErrorMessage ann) (TranslationContext ann)
buildTranslationContext c =
  let freeVariables = getFreeVariables c
  in runIdentity $
     runExceptT
       (execStateT
         (forM_ freeVariables addFreeVariableMapping)
         (TranslationContext c mempty))


addFreeVariableMapping
  :: Monad m
  => OSL.Name
  -> StateT (TranslationContext ann)
       (ExceptT (ErrorMessage ann) m) Mapping
addFreeVariableMapping freeVariable = do
  TranslationContext c _ <- get
  let decl = getExistingDeclaration c freeVariable
  case decl of
    FreeVariable t ->
      case t of
        Prop _ -> lift . ExceptT . pure . Left
          $ ErrorMessage (typeAnnotation t)
            "free Prop variable"
        N _ -> mapScalar
        Z _ -> mapScalar
        Fin _ _ -> mapScalar
        Product _ a b -> do
          aSym <- addGensym a
          bSym <- addGensym b
          aMap <- addFreeVariableMapping aSym
          bMap <- addFreeVariableMapping bSym
          let mapping = ProductMapping
                        (LeftMapping aMap)
                        (RightMapping bMap)
          addMapping freeVariable mapping
          return mapping
        Coproduct _ a b -> do
          iSym <- getFreeS11NameM (Arity 0)
          aSym <- addGensym a
          bSym <- addGensym b
          aMap <- addFreeVariableMapping aSym
          bMap <- addFreeVariableMapping bSym
          let mapping = CoproductMapping
                        (ChoiceMapping iSym)
                        (LeftMapping aMap)
                        (RightMapping bMap)
          addMapping freeVariable mapping
          return mapping
        F _ a b -> do
          aSym <- addGensym a
          bSym <- addGensym b
          aMap <- addFreeVariableMapping aSym
          bMap <- addFreeVariableMapping bSym
          aDim <- lift . except $
                  getFiniteDimMappingArity
                  (typeAnnotation a) 
                  aMap
          return (mapAritiesInMapping (+ (Arity 1)) bMap)
        NamedType ann aName -> do
          a <- getTypeDeclaration ann aName
          aSym <- addGensym a
          aMap <- addFreeVariableMapping aSym
          return aMap
    _ -> die "logically impossible: free variable is not a free variable"
  where
    mapScalar = do
      mapping <- ScalarMapping <$> getFreeS11NameM (Arity 0)
      addMapping freeVariable mapping
      return mapping


addMapping
  :: Monad m
  => OSL.Name
  -> Mapping
  -> StateT (TranslationContext ann) m ()
addMapping name mapping =
  modify ( #mappings %~ Map.insert name mapping )


addFreeVariableDeclaration
  :: Monad m
  => OSL.Name
  -> Type ann
  -> StateT (TranslationContext ann) m ()
addFreeVariableDeclaration name t =
  modify ( #context %~ addDeclaration name (FreeVariable t) )


getFreeVariables :: ValidContext ann -> [OSL.Name]
getFreeVariables (ValidContext decls) =
  Map.keys (Map.filter isFree decls)
  where
    isFree (FreeVariable _) = True
    isFree _ = False


getBoundS11NamesInContext
  :: Arity
  -> TranslationContext ann
  -> Set S11.Name
getBoundS11NamesInContext arity (TranslationContext _ ctx) =
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


getFreeS11Name
  :: Arity
  -> TranslationContext ann
  -> S11.Name
getFreeS11Name arity ctx =
  fromMaybe (S11.Name arity (DeBruijnIndex 0))
    . fmap (S11.Name arity . (+1) . (^. #deBruijnIndex))
    $ Set.lookupMax (getBoundS11NamesInContext arity ctx)


getFreeS11NameM
  :: Monad m
  => Arity
  -> StateT (TranslationContext ann) m S11.Name
getFreeS11NameM arity =
  getFreeS11Name arity <$> get


addGensym
  :: Monad m
  => Type ann
  -> StateT (TranslationContext ann) m OSL.Name
addGensym t = do
  name <- getFreeOSLName <$> get
  addFreeVariableDeclaration name t
  return name


getFreeOSLName
  :: TranslationContext ann
  -> OSL.Name
getFreeOSLName (TranslationContext (ValidContext c) _) =
  case fst <$> Map.lookupMax c of
    Nothing -> GenSym 0
    Just (Sym _) -> GenSym 0
    Just (GenSym i) -> GenSym (i+1)


mapAritiesInMapping
  :: (Arity -> Arity)
  -> Mapping
  -> Mapping
mapAritiesInMapping = todo


getFiniteDimMappingArity
  :: ann
  -> Mapping
  -> Either (ErrorMessage ann) Arity
getFiniteDimMappingArity ann =
  \case
    ScalarMapping _ -> return (Arity 1)
    ProductMapping (LeftMapping a) (RightMapping b) ->
      (+) <$> rec a <*> rec b
    CoproductMapping _ (LeftMapping a) (RightMapping b) ->
      (Arity 1 +) <$> ((+) <$> rec a <*> rec b)
    _ -> Left (ErrorMessage ann "expected a finite-dimensional type")
  where
    rec = getFiniteDimMappingArity ann


getTypeDeclaration
  :: Monad m
  => ann
  -> OSL.Name
  -> StateT (TranslationContext ann)
       (ExceptT (ErrorMessage ann) m)
       (Type ann)
getTypeDeclaration ann name = do
  TranslationContext (ValidContext c) _ <- get
  case Map.lookup name c of
    Just (Data a) -> return a
    -- these errors should be logically impossible:
    Just _ -> lift . throwE $ ErrorMessage ann "expected the name of a type"
    Nothing -> lift . throwE $ ErrorMessage ann "undefined name"


todo :: a
todo = todo
