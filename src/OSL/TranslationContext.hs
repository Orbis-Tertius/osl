{-# LANGUAGE DataKinds #-}

module OSL.TranslationContext
  ( toLocalTranslationContext,
    mergeMappings,
    mergeMapping,
    mergeMapping3,
    mappingIndices,
    highestIndicesInMappings,
    linearizeMapping,
  )
where

import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import OSL.Sigma11 (incrementDeBruijnIndices, termIndices, unionIndices)
import OSL.Types.Arity (Arity)
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.OSL (ContextType (Global, Local), Name, ValidContext (..))
import OSL.Types.Sigma11 (Term)
import OSL.Types.TranslationContext (Mapping (..), TranslationContext (..))

toLocalTranslationContext ::
  TranslationContext 'Global ann ->
  TranslationContext 'Local ann
toLocalTranslationContext (TranslationContext (ValidContext decls) mappings) =
  TranslationContext (ValidContext decls) mappings

-- Merges the two given mappings, moving the
-- de Bruijn indices in the right hand mapping
-- out of the way.
mergeMappings ::
  Map Name (Mapping ann Term) ->
  Map Name (Mapping ann Term) ->
  Map Name (Mapping ann Term)
mergeMappings as bs =
  let aMaxes = highestIndicesInMappings as
      f =
        foldl'
          (.)
          id
          [ fmap (incrementDeBruijnIndices arity (m + 1))
            | (arity, DeBruijnIndex m) <- Map.toList aMaxes
          ]
   in Map.union as (f <$> bs)

mergeMapping ::
  (Mapping ann Term -> Mapping ann Term -> Mapping ann Term) ->
  Mapping ann Term ->
  Mapping ann Term ->
  Mapping ann Term
mergeMapping f a b =
  let aMaxes = highestIndicesInMapping a
      g =
        foldl'
          (.)
          id
          [ fmap (incrementDeBruijnIndices arity (m + 1))
            | (arity, DeBruijnIndex m) <- Map.toList aMaxes
          ]
   in f (g a) b

mergeMapping3 ::
  (Mapping ann Term -> Mapping ann Term -> Mapping ann Term -> Mapping ann Term) ->
  Mapping ann Term ->
  Mapping ann Term ->
  Mapping ann Term ->
  Mapping ann Term
mergeMapping3 f a b c =
  let aMaxes = highestIndicesInMapping a
      g =
        foldl'
          (.)
          id
          [ fmap (incrementDeBruijnIndices arity (m + 1))
            | (arity, DeBruijnIndex m) <- Map.toList aMaxes
          ]
      b' = g b
      bMaxes = highestIndicesInMapping b'
      h =
        foldl'
          (.)
          id
          [ fmap (incrementDeBruijnIndices arity (m + 1))
            | (arity, DeBruijnIndex m) <- Map.toList bMaxes
          ]
   in f (h a) b' c

mappingIndices ::
  Mapping ann Term ->
  Map Arity (Set DeBruijnIndex)
mappingIndices =
  foldl' unionIndices mempty . fmap termIndices

-- Gets the highest de Bruijn index of each arity.
highestIndicesInMappings ::
  Map Name (Mapping ann Term) ->
  Map Arity DeBruijnIndex
highestIndicesInMappings =
  foldl' (Map.unionWith max) mempty . fmap highestIndicesInMapping

highestIndicesInMapping ::
  Mapping ann Term ->
  Map Arity DeBruijnIndex
highestIndicesInMapping =
  Map.mapMaybe id . fmap Set.lookupMax . mappingIndices

linearizeMapping :: Mapping ann a -> [a]
linearizeMapping = foldl' (flip (:)) []
