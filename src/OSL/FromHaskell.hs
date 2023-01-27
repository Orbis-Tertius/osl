{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module OSL.FromHaskell
  ( ToOSLType (toOSLType),
    ToOSLContext (toOSLContext)
  ) where

import Data.Fixed (Fixed, HasResolution (resolution))
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Rep, U1, (:*:), (:+:), M1, D, C, S, K1, R)
import GHC.TypeNats (KnownNat)
import qualified OSL.Types.OSL as OSL

class ToOSLType a where
  toOSLType :: Proxy a -> OSL.ValidContext 'OSL.Global ann -> OSL.Type ()

class GToOSLType (a :: Type) (ra :: Type -> Type) where
  gtoOSLType :: Proxy a -> Proxy ra -> OSL.ValidContext 'OSL.Global ann -> OSL.Type ()

instance GToOSLType t U1 where
  gtoOSLType _ _ _ = OSL.Fin () 1

instance GToOSLType t a => GToOSLType t (M1 D m a) where
  gtoOSLType (Proxy :: Proxy t) (Proxy :: Proxy (M1 D m a)) c =
    gtoOSLType (Proxy :: Proxy t) (Proxy :: Proxy a) c

instance GToOSLType t a => GToOSLType t (M1 C m a) where
  gtoOSLType (Proxy :: Proxy t) (Proxy :: Proxy (M1 C m a)) c =
    gtoOSLType (Proxy :: Proxy t) (Proxy :: Proxy a) c

instance GToOSLType t a => GToOSLType t (M1 S m a) where
  gtoOSLType (Proxy :: Proxy t) (Proxy :: Proxy (M1 S m a)) c =
    gtoOSLType (Proxy :: Proxy t) (Proxy :: Proxy a) c

instance GToOSLType t (Rep a) => GToOSLType t (K1 R a) where
  gtoOSLType (Proxy :: Proxy t) (Proxy :: Proxy (K1 R a)) c =
    gtoOSLType (Proxy :: Proxy t) (Proxy :: Proxy (Rep a)) c

instance ( GToOSLType a ra, GToOSLType b rb )
           => GToOSLType (a, b) (ra :*: rb) where
  gtoOSLType (Proxy :: Proxy (a, b)) (Proxy :: Proxy (ra :*: rb)) c =
    OSL.Product ()
      (gtoOSLType (Proxy :: Proxy a) (Proxy :: Proxy ra) c)
      (gtoOSLType (Proxy :: Proxy b) (Proxy :: Proxy rb) c)

instance ( GToOSLType a ra, GToOSLType b rb )
           => GToOSLType (Either a b) (ra :+: rb) where
  gtoOSLType (Proxy :: Proxy (Either a b)) (Proxy :: Proxy (ra :+: rb)) c =
    OSL.Coproduct ()
      (gtoOSLType (Proxy :: Proxy a) (Proxy :: Proxy ra) c)
      (gtoOSLType (Proxy :: Proxy b) (Proxy :: Proxy rb) c)

instance GToOSLType Integer a where
  gtoOSLType _ _ _ = OSL.Z ()

instance KnownNat n => GToOSLType (Fixed n) a where
  gtoOSLType (Proxy :: Proxy (Fixed n)) _ _ =
    OSL.Fin () (resolution (Proxy @n))

instance GToOSLType a (Rep a) => ToOSLType a where
  toOSLType (Proxy :: Proxy a) = gtoOSLType (Proxy @a) (Proxy @(Rep a))

class ToOSLContext a where
  toOSLContext ::
    Proxy a ->
    OSL.ValidContext 'OSL.Global ann ->
    OSL.ValidContext 'OSL.Global ann
