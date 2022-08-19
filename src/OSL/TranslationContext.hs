{-# LANGUAGE LambdaCase #-}


module OSL.TranslationContext
  ( mappingDimensions
  ) where


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
