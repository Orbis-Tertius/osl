{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module OSL.FromHaskell
  ( ToOSLType (toOSLType),
    AddToOSLContext (addToOSLContext),
    addToOSLContextM,
    productType,
    coproductType,
    mkRecordToOSL
  ) where

import Control.Lens ((^.))
import Control.Monad.State (State, state)
import Data.Fixed (Fixed (..), HasResolution (resolution))
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Text (pack)
import Data.Time (Day (..))
import Data.Typeable (Typeable, tyConName, typeRepTyCon, typeRep, typeRepArgs)
import Die (die)
import GHC.TypeLits (KnownNat)
import Language.Haskell.TH (Dec, Q, lookupTypeName, reify, Info (TyConI), Dec (DataD), Con (NormalC, RecC), Exp (VarE, ListE), newName, Pat (VarP), Type (ConT))
import qualified OSL.Types.OSL as OSL

class ToOSLType a where
  toOSLType :: Proxy a -> OSL.ValidContext 'OSL.Global () -> OSL.Type ()

-- Unit types
instance ToOSLType () where
  toOSLType _ _ = OSL.Fin () 1

-- Products
instance ( ToOSLType a, ToOSLType b, Typeable a, Typeable b )
           => ToOSLType (a, b) where
  toOSLType (Proxy :: Proxy (a, b)) c =
    OSL.Product ()
      (ntoOSLType (Proxy :: Proxy a) c)
      (ntoOSLType (Proxy :: Proxy b) c)

ntoOSLType ::
  ( ToOSLType a, Typeable a ) =>
  Proxy a ->
  OSL.ValidContext 'OSL.Global () ->
  OSL.Type ()
ntoOSLType pxy c =
  case typeRepArgs rep of
    [] ->
      case Map.lookup sym (c ^. #unValidContext) of
        Just (OSL.Data _) -> OSL.NamedType () sym
        _ -> toOSLType pxy c
    _ -> toOSLType pxy c
  where
    sym = OSL.Sym (pack (tyConName (typeRepTyCon rep)))
    rep = typeRep pxy

-- Coproducts
instance ( ToOSLType a, ToOSLType b, Typeable a, Typeable b )
           => ToOSLType (Either a b) where
  toOSLType (Proxy :: Proxy (Either a b)) c =
    OSL.Coproduct ()
      (ntoOSLType (Proxy :: Proxy a) c)
      (ntoOSLType (Proxy :: Proxy b) c)

-- Functions
instance ( ToOSLType a, ToOSLType b, Typeable a, Typeable b ) => ToOSLType (a -> b) where
  toOSLType (Proxy :: Proxy (a -> b)) c =
    OSL.F () Nothing (ntoOSLType (Proxy @a) c) (ntoOSLType (Proxy @b) c)

-- Maybe
instance ( ToOSLType a, Typeable a ) => ToOSLType (Maybe a) where
  toOSLType (Proxy :: Proxy (Maybe a)) c =
    OSL.Maybe () (ntoOSLType (Proxy @a) c)

-- Map
instance ( ToOSLType a, ToOSLType b, Typeable a, Typeable b ) => ToOSLType (Map a b) where
  toOSLType (Proxy :: Proxy (Map a b)) c =
    OSL.Map () 1 (ntoOSLType (Proxy @a) c) (ntoOSLType (Proxy @b) c)

-- List
instance ( ToOSLType a, Typeable a ) => ToOSLType [a] where
  toOSLType (Proxy :: Proxy [a]) c =
    OSL.List () 1 (ntoOSLType (Proxy @a) c)

-- Scalar types
instance ToOSLType Integer where
  toOSLType _ _ = OSL.Z ()

instance ToOSLType Int where
  toOSLType _ _ = OSL.Z ()

instance HasResolution n => ToOSLType (Fixed n) where
  toOSLType (Proxy :: Proxy (Fixed n)) _ =
    OSL.Fin () (resolution (Proxy @n))

instance KnownNat n => ToOSLType (Fixed n) where
  toOSLType (Proxy :: Proxy (Fixed n)) _ =
    OSL.Fin () (resolution (Proxy @n))

class AddToOSLContext a where
  addToOSLContext ::
    Proxy a ->
    OSL.ValidContext 'OSL.Global () ->
    OSL.ValidContext 'OSL.Global ()

-- newtypes
instance
  ( ToOSLType t, Typeable t ) =>
    AddToOSLContext t where
  addToOSLContext pxy c =
    c <> OSL.ValidContext
           (Map.singleton
              (OSL.Sym (pack (tyConName (typeRepTyCon (typeRep pxy)))))
              (OSL.Data (ntoOSLType pxy c)))

addToOSLContextM ::
  AddToOSLContext a =>
  Proxy a ->
  State (OSL.ValidContext 'OSL.Global ()) ()
addToOSLContextM p = state (((),) . addToOSLContext p)

deriving instance ToOSLType Day

productType :: [OSL.Type ()] -> OSL.Type ()
productType [] = OSL.Fin () 1
productType (t:ts) = foldl' (OSL.Product ()) t ts

coproductType :: [OSL.Type ()] -> OSL.Type ()
coproductType [] = OSL.Fin () 0
coproductType (t:ts) = foldl' (OSL.Coproduct ()) t ts

mkRecordToOSL :: String -> Q [Dec]
mkRecordToOSL nameStr = do
  name <-
    fromMaybe
      (die $ "mkRecordToOSL: expected the name of a type: " <> nameTxt)
      <$> lookupTypeName nameStr
  info <- reify name
  c <- newName "c"
  case info of
    TyConI (DataD _cxt _name _binders _kind ctors _deriving) ->
      [d|
         instance ToOSLType $(pure (ConT name)) where
           toOSLType _ $(pure (VarP c)) =
             coproductType $(ctorsToCoproductExp ctors c)
       |]
    _ -> die $ "mkRecordToOSL: expected an algebraic data type: " <> nameTxt
  where
    nameTxt = pack nameStr

    ctorsToCoproductExp ctors c =
      ListE <$> sequence
        [ [|
            productType $(ctorToProductExp c ctor)
           |]
          | ctor <- ctors
        ]

    ctorToProductExp c =
      \case
        NormalC _ ts ->
          ListE <$>
            sequence
              [ [| toOSLType (Proxy :: Proxy $(pure t)) $(pure (VarE c)) |]
                | (_, t) <- ts
              ]
        RecC _ ts ->
          ListE <$>
            sequence
              [ [| toOSLType (Proxy :: Proxy $(pure t)) $(pure (VarE c)) |]
                | (_, _, t) <- ts
              ]
        ctor -> die $ "mkRecordToOSL: expected a normal constructor: " <> pack (show ctor)
