{-# LANGUAGE LambdaCase #-}


module OSL.TranslationContext
  ( mappingDimensions
  , mergeMappings
  ) where


import Data.Map (Map)

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
mergeMappings = todo


todo :: a
todo = todo
