{-# LANGUAGE LambdaCase #-}

module OSL.Bound (boundAnnotation) where

import OSL.Types.OSL (Bound (..))

boundAnnotation :: Bound ann -> ann
boundAnnotation =
  \case
    ScalarBound ann _ -> ann
    FieldMaxBound ann -> ann
    ProductBound ann _ _ -> ann
    CoproductBound ann _ _ -> ann
    FunctionBound ann _ _ -> ann
    ListBound ann _ -> ann
    MaybeBound ann _ -> ann
    MapBound ann _ _ -> ann
    ToBound ann _ _ -> ann
