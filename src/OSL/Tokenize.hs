module OSL.Tokenize (tokenize) where


import Data.Either.Combinators (mapLeft)
import Data.Text (Text, pack)
import Text.Parsec (SourceName, SourcePos)
import Text.Parsec.Prim (parse)
import Text.Parsec.Text (Parser)

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.Token (Token)


tokenize :: SourceName -> Text -> Either (ErrorMessage ()) [(Token, SourcePos)]
tokenize name = mapLeft (ErrorMessage () . pack . show) . parse tokens name


tokens :: Parser [(Token, SourcePos)]
tokens = todo


todo :: a
todo = todo
