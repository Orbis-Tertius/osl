module OSL.Type
  ( typeAnnotation,
    typeCardinality,
  )
where

import OSL.Types.OSL (Cardinality (..), Declaration (Data), Type (..), ValidContext)
import OSL.ValidContext (getDeclaration)

typeAnnotation :: Type ann -> ann
typeAnnotation t =
  case t of
    Prop ann -> ann
    F ann _ _ _ -> ann
    P ann _ _ _ -> ann
    N ann -> ann
    Z ann -> ann
    Fp ann -> ann
    Fin ann _ -> ann
    Product ann _ _ -> ann
    Coproduct ann _ _ -> ann
    NamedType ann _ -> ann
    Maybe ann _ -> ann
    List ann _ _ -> ann
    Map ann _ _ _ -> ann

typeCardinality :: ValidContext t ann -> Type ann -> Maybe Cardinality
typeCardinality ctx t =
  case t of
    Prop _ -> Nothing
    F _ n _ _ -> n
    P _ n _ _ -> n
    N _ -> Just 1
    Z _ -> Just 1
    Fp _ -> Just 1
    Fin _ _ -> Just 1
    Product {} -> Just 1
    Coproduct {} -> Just 1
    NamedType _ name ->
      case getDeclaration ctx name of
        Just (Data t') -> typeCardinality ctx t'
        _ -> Nothing
    Maybe _ _ -> Just 1
    List _ n _ -> Just n
    Map _ n _ _ -> Just n
