module OSL.Spec.Gen
  ( genType,
    genValueOfType
  ) where

import Test.QuickCheck (Gen, oneof, choose)
import OSL.Types.OSL (Type (Prop, F, P, N, Z, Fp, Fin, Product, Coproduct, NamedType, Maybe, List, Map),
  Cardinality (Cardinality), Name)
import OSL.Types.Value (Value)

genType :: Gen ann -> Gen Name -> Gen (Type ann)
genType ann name =
  oneof
  [ Prop <$> ann,
    F <$> ann <*> genMaybe genCardinality
      <*> rec <*> rec,
    P <$> ann <*> genMaybe genCardinality
      <*> rec <*> rec,
    N <$> ann,
    Z <$> ann,
    Fp <$> ann,
    Fin <$> ann <*> choose (0,1000),
    Product <$> ann <*> rec <*> rec,
    Coproduct <$> ann <*> rec <*> rec,
    NamedType <$> ann <*> name,
    Maybe <$> ann <*> rec,
    List <$> ann <*> genCardinality <*> rec,
    Map <$> ann <*> genCardinality <*> rec <*> rec
  ]
  where
    rec = genType ann name

genMaybe :: Gen a -> Gen (Maybe a)
genMaybe g =
  oneof
  [ pure Nothing,
    Just <$> g
  ]

genCardinality :: Gen Cardinality
genCardinality =
  Cardinality <$> choose (0, 1000)

genValueOfType :: Gen Value
genValueOfType = todo

todo :: a
todo = todo
