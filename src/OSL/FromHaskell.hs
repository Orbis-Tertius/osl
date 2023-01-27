{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module OSL.FromHaskell
  ( ToOSLType (toOSLType),
    ToOSLContext (toOSLContext)
  ) where

import Data.Proxy (Proxy)
import GHC.Generics (Generic, U1 (U1))
import OSL.Types.OSL (ValidContext, ContextType (Global), Type (Fin))

class ToOSLType a where
  toOSLType :: Proxy a -> ValidContext 'Global ann -> Type ann

instance Generic a => ToOSLType a where
  toOSLType _ _ U1 = Fin 1

class ToOSLContext a where
  toOSLContext :: Proxy a -> ValidContext 'Global ann -> ValidContext 'Global ann
