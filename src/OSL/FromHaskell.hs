{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
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

import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Exts (Symbol)
import GHC.Generics (Rep, U1, (:*:), (:+:), M1, D, C, S, K1, R, Meta (MetaData))
import qualified OSL.Types.OSL as OSL

class ToOSLType a where
  toOSLType :: Proxy a -> OSL.ValidContext 'OSL.Global ann -> OSL.Type ()

class GToOSLType (a :: Type -> Type) where
  gtoOSLType :: Proxy a -> OSL.ValidContext 'OSL.Global ann -> OSL.Type ()

instance GToOSLType U1 where
  gtoOSLType _ _ = OSL.Fin () 1

instance GToOSLType a => GToOSLType (M1 D m a) where
  gtoOSLType (Proxy :: Proxy (M1 D m a)) c =
    gtoOSLType (Proxy :: Proxy a) c

instance GToOSLType a => GToOSLType (M1 C m a) where
  gtoOSLType (Proxy :: Proxy (M1 C m a)) c =
    gtoOSLType (Proxy :: Proxy a) c

instance GToOSLType a => GToOSLType (M1 S m a) where
  gtoOSLType (Proxy :: Proxy (M1 S m a)) c =
    gtoOSLType (Proxy :: Proxy a) c

instance ScalarToOSLType a ra sa ma pa nt
           => GToOSLType (M1 S (MetaData sa ma pa nt) ra) where
  gtoOSLType (Proxy :: Proxy (M1 S (MetaData sa ma pa nt))) c =
    scalarToOSLType (Proxy :: Proxy a) c

instance GToOSLType (Rep a) => GToOSLType (K1 R a) where
  gtoOSLType (Proxy :: Proxy (K1 R a)) c =
    gtoOSLType (Proxy :: Proxy (Rep a)) c

instance ( GToOSLType a, GToOSLType b )
           => GToOSLType (a :*: b) where
  gtoOSLType (Proxy :: Proxy (a :*: b)) c =
    OSL.Product ()
      (gtoOSLType (Proxy :: Proxy a) c)
      (gtoOSLType (Proxy :: Proxy b) c)

instance ( GToOSLType a, GToOSLType b )
           => GToOSLType (a :+: b) where
  gtoOSLType (Proxy :: Proxy (a :+: b)) c =
    OSL.Coproduct ()
      (gtoOSLType (Proxy :: Proxy a) c)
      (gtoOSLType (Proxy :: Proxy b) c)

-- To handle scalar types, maybe make a new typeclass for finding
-- their OSL reps?

class ScalarToOSLType
        (a :: Type)
        (ra :: Type -> Type)
        (sa :: Symbol)
        (ma :: Symbol)
        (pa :: Symbol)
        (nt :: Bool)
        | a -> sa, a -> ra, a -> ma, a -> pa, a -> nt where
  scalarToOSLType ::
    Proxy a ->
    OSL.ValidContext 'OSL.Global ann ->
    OSL.Type ()

instance GToOSLType (Rep a) => ToOSLType a where
  toOSLType (Proxy :: Proxy a) = gtoOSLType (Proxy @(Rep a))

class ToOSLContext a where
  toOSLContext ::
    Proxy a ->
    OSL.ValidContext 'OSL.Global ann ->
    OSL.ValidContext 'OSL.Global ann
