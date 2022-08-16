{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}


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
  ) where


import Data.Generics.Labels ()
import Data.Map (Map)
import GHC.Generics (Generic)

import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11


data TranslationContext ann =
  TranslationContext
  { context :: OSL.ValidContext ann
  , mappings :: Map OSL.Name (Mapping S11.Name)
  }
  deriving Generic


data Mapping a =
    ScalarMapping a
  | ProductMapping
    (LeftMapping a)
    (RightMapping a)
  | CoproductMapping
    (ChoiceMapping a)
    (LeftMapping a)
    (RightMapping a)
  | MaybeMapping
    (ChoiceMapping a)
    (ValuesMapping a)
  | ListMapping
    (LengthMapping a)
    (ValuesMapping a)
  | MapMapping
    (LengthMapping a)
    (KeysMapping a)
    (KeyIndicatorMapping a)
    (ValuesMapping a)


instance Functor Mapping where
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
        (ChoiceMapping (f a))
        (LeftMapping (f <$> b))
        (RightMapping (f <$> c))
      MaybeMapping (ChoiceMapping a) (ValuesMapping b) ->
        MaybeMapping
        (ChoiceMapping (f a))
        (ValuesMapping (f <$> b))
      ListMapping (LengthMapping a) (ValuesMapping b) ->
        ListMapping
        (LengthMapping (f a))
        (ValuesMapping (f <$> b))
      MapMapping (LengthMapping a) (KeysMapping b)
          (KeyIndicatorMapping c) (ValuesMapping d) ->
        MapMapping
        (LengthMapping (f a))
        (KeysMapping (f <$> b))
        (KeyIndicatorMapping (f c))
        (ValuesMapping (f <$> d))


newtype LeftMapping a
  = LeftMapping { unLeftMapping :: Mapping a }


newtype RightMapping a =
  RightMapping { unRightMapping :: Mapping a }


newtype ChoiceMapping a
  = ChoiceMapping { unChoiceMapping :: a }


newtype LengthMapping a =
  LengthMapping { unLengthMapping :: a }


newtype ValuesMapping a
  = ValuesMapping { unValuesMapping :: Mapping a }


newtype KeysMapping a
  = KeysMapping { unKeysMapping :: Mapping a }


newtype KeyIndicatorMapping a
  = KeyIndicatorMapping
    { unKeyIndicatorMapping :: a }
