module OSL.Tokenize (tokenize) where


import Control.Monad (void)
import Data.Either.Combinators (mapLeft)
import Data.Text (Text, pack, cons)
import Text.Parsec (SourceName, SourcePos, getPosition, eof, oneOf, (<|>), try, string, noneOf, anyChar, choice)
import Text.Parsec.Prim (parse, many)
import Text.Parsec.Text (Parser)

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Name (..))
import OSL.Types.Keyword (Keyword)
import OSL.Types.Token (Token)
import qualified OSL.Types.Token as T


tokenize :: SourceName -> Text -> Either (ErrorMessage ()) [(Token, SourcePos)]
tokenize sourceName = mapLeft (ErrorMessage () . pack . show) . parse tokens sourceName


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
token =
  choice
  $
  try
  <$>
  [ T.Keyword <$> keyword
  , T.ThinArrow <$ string "->"
  , T.ThinArrow <$ string "→"
  , T.Colon <$ string ":"
  , T.OpenParen <$ string "("
  , T.CloseParen <$ string ")"
  , T.ConstN <$> constantNatural
  , T.ConstZ <$> constantInteger
  , T.ConstFin <$> constantFinite
  , T.AddNOp <$ string "+N"
  , T.AddNOp <$ string "+ℕ"
  , T.MulNOp <$ string "×ℕ"
  , T.AddZOp <$ string "+Z"
  , T.AddZOp <$ string "+ℤ"
  , T.MulZOp <$ string "*Z"
  , T.MulZOp <$ string "×ℤ"
  , T.ProductOp <$ string "*"
  , T.ProductOp <$ string "×"
  , T.Comma <$ string ","
  , T.CoproductOp <$ string "+"
  , T.CoproductOp <$ string "⊕"
  , T.Equals <$ string "="
  , T.LessOrEquals <$ string "<="
  , T.LessOrEquals <$ string "≤"
  , T.And <$ string "&"
  , T.And <$ string "∧"
  , T.Or <$ string "|"
  , T.Or <$ string "∨"
  , T.Not <$ string "!"
  , T.Not <$ string "¬"
  , T.ForAll <$ string "all"
  , T.ForAll <$ string "∀"
  , T.ForSome <$ string "some"
  , T.ForSome <$ string "∃"
  , T.Lambda <$ string "\\"
  , T.Lambda <$ string "λ"
  , T.ThickArrow <$ string "=>"
  , T.ThickArrow <$ string "⇨"
  , T.Congruent <$ string "~="
  , T.Congruent <$ string "≅"
  , T.DefEquals <$ string ":="
  , T.DefEquals <$ string "≔"
  , T.Semicolon <$ string ";"
  , T.Period <$ string "."
  -- Var must come last in order to deal with ambiguity
  , T.Var <$> name
  ]


keyword :: Parser Keyword
keyword = todo


name :: Parser Name
name = do
  begin <- oneOf (['a'..'z'] <> ['A'..'Z'] <> "_")
  rest  <- many (oneOf (['a'..'z'] <> ['A'..'Z'] <> ['0'..'9'] <> "_"))
  return (Name (cons begin (pack rest)))


constantNatural :: Parser Integer
constantNatural = todo


constantInteger :: Parser Integer
constantInteger = todo


constantFinite :: Parser Integer
constantFinite = todo


todo :: a
todo = todo
