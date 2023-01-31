{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module OSL.FromHaskell
  ( ToOSLType (toOSLType),
    AddToOSLContext (addToOSLContext),
    Newtype,
    addToOSLContextM,
    productType,
    coproductType,
    mkDataToOSL,
    mkDataToAddOSL,
  )
where

import Control.Lens ((^.), _3)
import Control.Monad.State (State, state)
import Data.Fixed (Fixed (..), HasResolution (resolution))
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Text (pack)
import Data.Time (Day (..))
import Data.Typeable (Typeable, tyConName, typeRep, typeRepArgs, typeRepTyCon)
import Die (die)
import GHC.TypeLits (KnownNat)
import Language.Haskell.TH (Con (NormalC, RecC), Dec (DataD), Exp (ListE, LitE, VarE), Info (TyConI), Lit (StringL), Pat (VarP), Q, Type (AppT, ConT, TupleT), lookupTypeName, nameBase, newName, reify)
import qualified OSL.Types.OSL as OSL

class ToOSLType a where
  toOSLType :: Proxy a -> OSL.ValidContext 'OSL.Global () -> OSL.Type ()

-- Unit types
instance ToOSLType () where
  toOSLType _ _ = OSL.Fin () 1

-- Products
instance
  (ToOSLType a, ToOSLType b, Typeable a, Typeable b) =>
  ToOSLType (a, b)
  where
  toOSLType (Proxy :: Proxy (a, b)) c =
    OSL.Product
      ()
      (ntoOSLType (Proxy :: Proxy a) c)
      (ntoOSLType (Proxy :: Proxy b) c)

ntoOSLType ::
  (ToOSLType a, Typeable a) =>
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
instance
  (ToOSLType a, ToOSLType b, Typeable a, Typeable b) =>
  ToOSLType (Either a b)
  where
  toOSLType (Proxy :: Proxy (Either a b)) c =
    OSL.Coproduct
      ()
      (ntoOSLType (Proxy :: Proxy a) c)
      (ntoOSLType (Proxy :: Proxy b) c)

-- Functions
instance (ToOSLType a, ToOSLType b, Typeable a, Typeable b) => ToOSLType (a -> b) where
  toOSLType (Proxy :: Proxy (a -> b)) c =
    OSL.F () Nothing (ntoOSLType (Proxy @a) c) (ntoOSLType (Proxy @b) c)

-- Maybe
instance (ToOSLType a, Typeable a) => ToOSLType (Maybe a) where
  toOSLType (Proxy :: Proxy (Maybe a)) c =
    OSL.Maybe () (ntoOSLType (Proxy @a) c)

-- Map
instance (ToOSLType a, ToOSLType b, Typeable a, Typeable b) => ToOSLType (Map a b) where
  toOSLType (Proxy :: Proxy (Map a b)) c =
    OSL.Map () 1 (ntoOSLType (Proxy @a) c) (ntoOSLType (Proxy @b) c)

-- List
instance (ToOSLType a, Typeable a) => ToOSLType [a] where
  toOSLType (Proxy :: Proxy [a]) c =
    OSL.List () 1 (ntoOSLType (Proxy @a) c)

-- Scalar types
instance ToOSLType Integer where
  toOSLType _ _ = OSL.Z ()

instance ToOSLType Int where
  toOSLType _ _ = OSL.Z ()

instance ToOSLType Char where
  toOSLType _ _ = OSL.N ()

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
data Newtype a

instance
  (ToOSLType t, Typeable t) =>
  AddToOSLContext (Newtype t)
  where
  addToOSLContext (Proxy :: Proxy (Newtype t)) c =
    c
      <> OSL.ValidContext
        ( Map.singleton
            (OSL.Sym (pack (tyConName (typeRepTyCon (typeRep (Proxy :: Proxy t))))))
            (OSL.Data (ntoOSLType (Proxy :: Proxy t) c))
        )

addToOSLContextM ::
  AddToOSLContext a =>
  Proxy a ->
  State (OSL.ValidContext 'OSL.Global ()) ()
addToOSLContextM p = state (((),) . addToOSLContext p)

deriving instance ToOSLType Day

productType :: [OSL.Type ()] -> OSL.Type ()
productType [] = OSL.Fin () 1
productType (t : ts) = foldl' (OSL.Product ()) t ts

coproductType :: [OSL.Type ()] -> OSL.Type ()
coproductType [] = OSL.Fin () 0
coproductType (t : ts) = foldl' (OSL.Coproduct ()) t ts

mkDataToOSL :: String -> Q [Dec]
mkDataToOSL nameStr = do
  name <-
    fromMaybe
      (die $ "mkDataToOSL: expected the name of a type: " <> nameTxt)
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
    _ -> die $ "mkDataToOSL: expected an algebraic data type: " <> nameTxt
  where
    nameTxt = pack nameStr

    ctorsToCoproductExp ctors c =
      ListE
        <$> sequence
          [ [|
              productType $(ctorToProductExp c ctor)
              |]
            | ctor <- ctors
          ]

    ctorToProductExp c =
      \case
        NormalC _ ts ->
          ListE
            <$> sequence
              [ [|toOSLType (Proxy :: Proxy $(pure t)) $(pure (VarE c))|]
                | (_, t) <- ts
              ]
        RecC _ ts ->
          ListE
            <$> sequence
              [ [|toOSLType (Proxy :: Proxy $(pure t)) $(pure (VarE c))|]
                | (_, _, t) <- ts
              ]
        ctor -> die $ "mkDataToOSL: expected a normal constructor: " <> pack (show ctor)

mkDataToAddOSL :: String -> Q [Dec]
mkDataToAddOSL nameStr = do
  name <-
    fromMaybe
      (die $ "mkDataToAddOSL: expected the name of a type: " <> nameTxt)
      <$> lookupTypeName nameStr
  info <- reify name
  c <- newName "c"
  case info of
    TyConI (DataD _cxt _name _binders _kind ctors _deriving) ->
      [d|
        instance AddToOSLContext $(pure (ConT name)) where
          addToOSLContext _ $(pure (VarP c)) =
            $(pure (VarE c))
              <> OSL.ValidContext
                ( Map.fromList $(ctorsContextEntries ctors c)
                    <> Map.singleton
                      $(pure (LitE (StringL nameStr)))
                      (OSL.Data $(ctorsCoproduct ctors))
                )

        instance ToOSLType $(pure (ConT name)) where
          toOSLType _ _ =
            OSL.NamedType () $(pure (LitE (StringL nameStr)))
        |]
    _ -> die $ "mkDataToAddOSL: expected a simple algebraic data type: " <> nameTxt
  where
    nameTxt = pack nameStr

    ctorsContextEntries ctors c =
      ListE
        <$> sequence
          [ [|
              ( $(pure (LitE (StringL (nameBase cName)))),
                OSL.Data
                  ( toOSLType
                      (Proxy :: Proxy $(pure ctorType))
                      $(pure (VarE c))
                  )
              )
              |]
            | ctor <- ctors,
              let cName = ctorName ctor,
              let ctorArgs =
                    case ctor of
                      NormalC _ ts -> snd <$> ts
                      RecC _ ts -> (^. _3) <$> ts
                      _ ->
                        die $
                          "mkDataToAddOSL: expected a normal constructor: "
                            <> pack (show ctor),
              let ctorType =
                    case ctorArgs of
                      (t : ts) ->
                        foldl'
                          (AppT . AppT (TupleT 2))
                          t
                          ts
                      [] -> TupleT 0
          ]

    ctorsCoproduct ctors =
      [|
        coproductType
          $( ListE
               <$> sequence
                 [ [|OSL.NamedType () $(pure (LitE (StringL (nameBase (ctorName ctor)))))|]
                   | ctor <- ctors
                 ]
           )
        |]

    ctorName =
      \case
        NormalC n _ -> n
        RecC n _ -> n
        ctor -> die $ "mkDataToAddOSL: expected a normal constructor: " <> pack (show ctor)
