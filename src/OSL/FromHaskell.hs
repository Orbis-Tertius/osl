{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module OSL.FromHaskell
  ( ToOSLType (toOSLType),
    ToOSLContext (toOSLContext)
  ) where

import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Rep, U1, (:*:))
import qualified OSL.Types.OSL as OSL

class ToOSLType a where
  toOSLType :: Proxy a -> OSL.ValidContext 'OSL.Global ann -> OSL.Type ()

class GToOSLType (a :: Type -> Type) where
  gtoOSLType :: Proxy a -> OSL.ValidContext 'OSL.Global ann -> OSL.Type ()

instance GToOSLType U1 where
  gtoOSLType _ _ = OSL.Fin () 1

instance ( GToOSLType a, GToOSLType b )
           => GToOSLType (a :*: b) where
  gtoOSLType (Proxy :: Proxy (a :*: b)) c =
    OSL.Product ()
      (gtoOSLType (Proxy :: Proxy a) c)
      (gtoOSLType (Proxy :: Proxy b) c)

instance GToOSLType (Rep a) => ToOSLType a where
  toOSLType (Proxy :: Proxy a) = gtoOSLType (Proxy @(Rep a))

class ToOSLContext a where
  toOSLContext ::
    Proxy a ->
    OSL.ValidContext 'OSL.Global ann ->
    OSL.ValidContext 'OSL.Global ann
