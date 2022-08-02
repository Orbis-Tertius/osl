{-# LANGUAGE DeriveGeneric #-}


module OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage)) where


import Data.Text (Text)
import GHC.Generics (Generic)


data ErrorMessage ann =
  ErrorMessage
  { annotation :: ann
  , message :: Text
  }
  deriving Generic
