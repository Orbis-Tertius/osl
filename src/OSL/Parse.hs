module OSL.Parse (parseContext) where


import Data.Either.Combinators (mapLeft)
import Data.Text (pack)
import Text.Parsec (SourceName, SourcePos, Parsec)
import qualified Text.Parsec.Prim as Prim

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Context (..))
import OSL.Types.Token (Token (..))


parseContext :: SourceName -> [(Token, SourcePos)] -> Either (ErrorMessage ()) (Context SourcePos)
parseContext = parse' context


type Parser = Parsec [(Token, SourcePos)] ()


parse' :: Parser a -> SourceName -> [(Token, SourcePos)] -> Either (ErrorMessage ()) a
parse' p name = mapLeft (ErrorMessage () . pack . show) . Prim.parse p name


context :: Parser (Context SourcePos)
context = todo


todo :: a
todo = todo
