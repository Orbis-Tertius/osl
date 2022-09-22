{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}


module OSL.Types.TranslationContext
  ( TranslationContext (TranslationContext)
  , Mapping (..)
  , LeftMapping (..)
  , RightMapping (..)
  , ChoiceMapping (..)
  , LengthMapping (..)
  , ValuesMapping (..)
  , KeysMapping (..)
  , KeyIndicatorMapping (..)
  , MappingDimensions (..)
  ) where


import Data.Generics.Labels ()
import Data.Map (Map)
import GHC.Generics (Generic)

import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11


data TranslationContext (t :: OSL.ContextType) ann =
  TranslationContext
  { context :: OSL.ValidContext t ann
  , mappings :: Map OSL.Name (Mapping ann S11.Term)
  }
  deriving (Show, Generic)


data Mapping ann a =
    ScalarMapping a
  | ProductMapping
    (LeftMapping ann a)
    (RightMapping ann a)
  | CoproductMapping
    (ChoiceMapping ann a)
    (LeftMapping ann a)
    (RightMapping ann a)
  | FunctionCoproductMapping
    (LeftMapping ann a)
    (RightMapping ann a)
  | MaybeMapping
    (ChoiceMapping ann a)
    (ValuesMapping ann a)
  | ListMapping
    (LengthMapping ann a)
    (ValuesMapping ann a)
  | MapMapping
    (LengthMapping ann a)
    (KeysMapping ann a)
    (KeyIndicatorMapping ann a)
    (ValuesMapping ann a)
  | LambdaMapping
    (TranslationContext 'OSL.Global ann)
    (TranslationContext 'OSL.Local ann)
    OSL.Name
    (OSL.Type ann)
    (OSL.Term ann)
  | PropMapping S11.Formula
  | PredicateMapping S11.PredicateName
  deriving Show


instance Functor (Mapping ann) where
  fmap f =
    \case
      ScalarMapping a -> ScalarMapping (f a)
      ProductMapping (LeftMapping a) (RightMapping b) ->
        ProductMapping
        (LeftMapping (f <$> a))
        (RightMapping (f <$> b))
      CoproductMapping (ChoiceMapping a)
          (LeftMapping b) (RightMapping c) ->
        CoproductMapping
        (ChoiceMapping (f <$> a))
        (LeftMapping (f <$> b))
        (RightMapping (f <$> c))
      FunctionCoproductMapping (LeftMapping a) (RightMapping b) ->
        FunctionCoproductMapping
        (LeftMapping (f <$> a))
        (RightMapping (f <$> b))
      MaybeMapping (ChoiceMapping a) (ValuesMapping b) ->
        MaybeMapping
        (ChoiceMapping (f <$> a))
        (ValuesMapping (f <$> b))
      ListMapping (LengthMapping a) (ValuesMapping b) ->
        ListMapping
        (LengthMapping (f <$> a))
        (ValuesMapping (f <$> b))
      MapMapping (LengthMapping a) (KeysMapping b)
          (KeyIndicatorMapping c) (ValuesMapping d) ->
        MapMapping
        (LengthMapping (f <$> a))
        (KeysMapping (f <$> b))
        (KeyIndicatorMapping (f <$> c))
        (ValuesMapping (f <$> d))
      LambdaMapping gc lc v vT t ->
        -- TODO: should fmap descend into gc and/or lc?
        LambdaMapping gc lc v vT t
      PropMapping p -> PropMapping p
      PredicateMapping p -> PredicateMapping p


instance Foldable (Mapping ann) where
  foldMap f =
    \case
      ScalarMapping x -> f x
      ProductMapping (LeftMapping x) (RightMapping y) ->
        foldMap f x <> foldMap f y
      CoproductMapping (ChoiceMapping x) (LeftMapping y) (RightMapping z) ->
        foldMap f x <> foldMap f y <> foldMap f z
      FunctionCoproductMapping (LeftMapping x) (RightMapping y) ->
        foldMap f x <> foldMap f y
      MaybeMapping (ChoiceMapping x) (ValuesMapping y) ->
        foldMap f x <> foldMap f y
      ListMapping (LengthMapping x) (ValuesMapping y) ->
        foldMap f x <> foldMap f y
      MapMapping (LengthMapping w)
                 (KeysMapping x)
                 (KeyIndicatorMapping y)
                 (ValuesMapping z) ->
        foldMap f w <> foldMap f x
          <> foldMap f y <> foldMap f z
      LambdaMapping _ _ _ _ _ -> mempty
      PropMapping _ -> mempty
      PredicateMapping _ -> mempty


newtype LeftMapping ann a
  = LeftMapping { unLeftMapping :: Mapping ann a }
  deriving Show


newtype RightMapping ann a =
  RightMapping { unRightMapping :: Mapping ann a }
  deriving Show


newtype ChoiceMapping ann a
  = ChoiceMapping { unChoiceMapping :: Mapping ann a }
  deriving Show


newtype LengthMapping ann a =
  LengthMapping { unLengthMapping :: Mapping ann a }
  deriving Show


newtype ValuesMapping ann a
  = ValuesMapping { unValuesMapping :: Mapping ann a }
  deriving Show


newtype KeysMapping ann a
  = KeysMapping { unKeysMapping :: Mapping ann a }
  deriving Show


newtype KeyIndicatorMapping ann a
  = KeyIndicatorMapping
    { unKeyIndicatorMapping :: Mapping ann a }
  deriving Show


data MappingDimensions
  = FiniteDimensions Int
  | InfiniteDimensions
  deriving Show

instance Semigroup MappingDimensions where
  (FiniteDimensions x) <> (FiniteDimensions y) = FiniteDimensions (x + y)
  _ <> InfiniteDimensions = InfiniteDimensions
  InfiniteDimensions <> _ = InfiniteDimensions

instance Monoid MappingDimensions where
  mempty = FiniteDimensions 0
