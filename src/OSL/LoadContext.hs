{-# LANGUAGE DataKinds #-}

module OSL.LoadContext (loadContext) where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Text (pack)
import OSL.Parse (parseContext)
import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.FileName (FileName (FileName))
import OSL.Types.OSL (ValidContext, ContextType (Global))
import OSL.Tokenize (tokenize)
import OSL.ValidateContext (validateContext)
import Text.Parsec (SourcePos)

loadContext :: MonadIO m => FileName -> m (Either (ErrorMessage SourcePos) (ValidContext 'Global SourcePos))
loadContext (FileName fileName) = do
  source <- pack <$> liftIO (readFile fileName)
  pure $ do
    toks <- tokenize fileName source
    rawCtx <- parseContext fileName toks
    validateContext rawCtx
