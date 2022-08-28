{-# LANGUAGE LambdaCase #-}


module OSL.TranslationContext
  ( mappingDimensions
  , mergeMappings
  , mappingIndices
  , highestIndicesInMappings
  ) where


import Control.Functor.Compactable (compact)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import OSL.Sigma11 (termIndices, unionIndices, incrementDeBruijnIndices)
import OSL.Types.Arity (Arity)
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.OSL (Name)
import OSL.Types.Sigma11 (Term)
import OSL.Types.TranslationContext (Mapping (..), MappingDimensions (..), LeftMapping (..), RightMapping (..), ValuesMapping (..))


mappingDimensions :: Mapping a -> MappingDimensions
mappingDimensions =
  \case
    ScalarMapping _ -> one
    ProductMapping (LeftMapping a) (RightMapping b) ->
      rec a <> rec b
    CoproductMapping _ (LeftMapping a) (RightMapping b) ->
      one <> rec a <> rec b
    FunctionCoproductMapping _ _ -> InfiniteDimensions
    MaybeMapping _ (ValuesMapping a) ->
      one <> rec a
    ListMapping _ _ -> InfiniteDimensions
    MapMapping _ _ _ _ -> InfiniteDimensions
  where
    one = FiniteDimensions 1
    rec = mappingDimensions


-- Merges the two given mappings, moving the
-- de Bruijn indices in the right hand mapping
-- out of the way.
mergeMappings
  :: Map Name (Mapping Term)
  -> Map Name (Mapping Term)
  -> Map Name (Mapping Term)
mergeMappings as bs =
  let aMaxes = highestIndicesInMappings as
      f = foldl (.) id
          [ incrementDeBruijnIndices arity (m+1)
          | (arity, DeBruijnIndex m) <- Map.toList aMaxes ]
  in Map.union as (f <$> bs)


mappingIndices
  :: Mapping Term
  -> Map Arity (Set DeBruijnIndex)
mappingIndices =
  foldl' unionIndices mempty . fmap termIndices


-- Gets the highest de Bruijn index of each arity.
highestIndicesInMappings
  :: Map Name (Mapping Term)
  -> Map Arity DeBruijnIndex
highestIndicesInMappings =
  foldl' (Map.unionWith max) mempty
    . fmap (compact . fmap Set.lookupMax . mappingIndices)
