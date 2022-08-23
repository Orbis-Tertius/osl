module OSL.Type (typeAnnotation) where


import OSL.Types.OSL (Type (..))


typeAnnotation :: Type ann -> ann
typeAnnotation t =
  case t of
    Prop ann -> ann
    F ann _ _ _ -> ann
    N ann -> ann
    Z ann -> ann
    Fin ann _ -> ann
    Product ann _ _ -> ann
    Coproduct ann _ _ -> ann
    NamedType ann _ -> ann
    Maybe ann _ -> ann
    List ann _ _ -> ann
    Map ann _ _ _ -> ann
