{-# LANGUAGE LambdaCase #-}


module OSL.Tokenize (tokenize) where


import Control.Monad (void)
import Data.Either.Combinators (mapLeft)
import Data.Text (Text, pack, cons)
import Text.Parsec (SourceName, SourcePos, getPosition, eof, oneOf, (<|>), try, string, noneOf, anyChar, choice, char, many1)
import Text.Parsec.Prim (parse, many)
import Text.Parsec.Text (Parser)

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Name (..))
import OSL.Types.Keyword (Keyword)
import qualified OSL.Types.Keyword as K
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
  , constantNatural
  , constantInteger
  , constantFinite
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
keyword =
  choice
  $
  try
  <$>
  [ K.Type <$ string "Type"
  , K.Prop <$ string "Prop"
  , K.N <$ string "ℕ"
  , K.N <$ string "N"
  , K.Z <$ string "ℤ"
  , K.Z <$ string "Z"
  , K.Fin <$ string "Fin"
  , K.Cast <$ string "cast"
  , K.Data <$ string "data"
  , K.To <$ string "to"
  , K.From <$ string "from"
  , K.Def <$ string "def"
  , K.Maybe <$ string "Maybe"
  , K.Maybe' <$ string "maybe"
  , K.Just' <$ string "just"
  , K.Nothing' <$ string "nothing"
  , K.Exists <$ string "exists"
  , K.List <$ string "List"
  , K.Length <$ string "length"
  , K.Nth <$ string "nth"
  , K.Sum <$ string "Σ"
  , K.Sum <$ string "sum"
  , K.Pi1 <$ string "π1"
  , K.Pi1 <$ string "pi1"
  , K.Pi2 <$ string "π2"
  , K.Pi2 <$ string "pi2"
  , K.Iota1 <$ string "ι1"
  , K.Iota2 <$ string "ι2"
  , K.Iota1 <$ string "iota1"
  , K.Iota2 <$ string "iota2"
  , K.Map <$ string "Map"
  , K.Lookup <$ string "lookup"
  , K.Keys <$ string "keys"
  , K.SumMapLength <$ string "sumMapLength"
  , K.SumListLookup <$ string "sumListLookup"
  ]


name :: Parser Name
name = do
  begin <- oneOf (['a'..'z'] <> ['A'..'Z'] <> "_")
  rest  <- many (oneOf (['a'..'z'] <> ['A'..'Z'] <> ['0'..'9'] <> "_"))
  return (Name (cons begin (pack rest)))


constantNatural :: Parser Token
constantNatural = do
  i <- nonNegativeIntegerLiteral
  void $ char 'N' <|> char 'ℕ'
  return (T.ConstN i)


constantInteger :: Parser Token
constantInteger = do
  i <- integerLiteral
  void $ char 'Z' <|> char 'ℤ'
  return (T.ConstZ i)


constantFinite :: Parser Token
constantFinite = do
  void $ string "fin"
  whitespace
  void $ char '('
  i <- integerLiteral
  whitespace
  void $ char ')'
  return (T.ConstFin i)


integerLiteral :: Parser Integer
integerLiteral = negativeIntegerLiteral <|> nonNegativeIntegerLiteral


negativeIntegerLiteral :: Parser Integer
negativeIntegerLiteral = do
  void (char '-')
  negate <$> nonNegativeIntegerLiteral


nonNegativeIntegerLiteral :: Parser Integer
nonNegativeIntegerLiteral =
  digitsToInteger <$> many1 (oneOf ['0'..'9'])


digitToInteger :: Char -> Integer
digitToInteger =
  \case
    '0' -> 0
    '1' -> 1
    '2' -> 2
    '3' -> 3
    '4' -> 4
    '5' -> 5
    '6' -> 6
    '7' -> 7
    '8' -> 8
    '9' -> 9
    _   -> 0


digitsToInteger :: String -> Integer
digitsToInteger = foldl (\a x -> a * 10 + x) 0 . fmap digitToInteger
