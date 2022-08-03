module OSL.Tokenize (tokenize) where


import Control.Monad (void)
import Data.Either.Combinators (mapLeft)
import Data.Text (Text, pack)
import Text.Parsec (SourceName, SourcePos, getPosition, eof, oneOf, (<|>), try, string, noneOf, anyChar)
import Text.Parsec.Prim (parse, many)
import Text.Parsec.Text (Parser)

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.Token (Token)


tokenize :: SourceName -> Text -> Either (ErrorMessage ()) [(Token, SourcePos)]
tokenize name = mapLeft (ErrorMessage () . pack . show) . parse tokens name


tokens :: Parser [(Token, SourcePos)]
tokens = do
  void (many whitespace)
  ts <- many $ do
         t <- token
         p <- getPosition
         void (many whitespace)
         return (t, p)
  eof
  return ts


whitespace :: Parser ()
whitespace = void (oneOf " \t\r\n") <|> try oneLineComment <|> try multiLineComment


oneLineComment :: Parser ()
oneLineComment = do
  void $ string "--"
  void $ many (noneOf lineEnding)
  void $ oneOf lineEnding
  where
    lineEnding = "\r\n"


multiLineComment :: Parser ()
multiLineComment = do
  void $ string "{-"
  rest

  where
    rest :: Parser ()
    rest = void (try (string "-}")) <|> (void anyChar >> rest)


token :: Parser Token
token = todo


todo :: a
todo = todo
