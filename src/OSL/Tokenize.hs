module OSL.Tokenize (tokenize) where


import Data.Text (Text)
import Text.Parsec (SourceName, SourcePos)

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.Token (Token)


tokenize :: SourceName -> Text -> Either (ErrorMessage SourcePos) [(Token, SourcePos)]
tokenize = todo


todo :: a
todo = todo
