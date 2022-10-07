{-# LANGUAGE LambdaCase #-}

module OSL.Tokenize (tokenize) where

import Control.Monad (void)
import Data.Either.Combinators (mapLeft)
import Data.List (foldl')
import Data.Text (Text, cons, pack)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.Keyword (Keyword)
import qualified OSL.Types.Keyword as K
import OSL.Types.OSL (Name (..))
import OSL.Types.Token (Token)
import qualified OSL.Types.Token as T
import Text.Parsec (SourceName, SourcePos, anyChar, char, choice, eof, getPosition, lookAhead, many1, noneOf, oneOf, string, try, (<|>))
import Text.Parsec.Prim (many, parse)
import Text.Parsec.Text (Parser)

tokenize :: SourceName -> Text -> Either (ErrorMessage ()) [(Token, SourcePos)]
tokenize sourceName = mapLeft (ErrorMessage () . pack . show) . parse tokens sourceName

tokens :: Parser [(Token, SourcePos)]
tokens = do
  void (many whitespace)
  ts <- many $ do
    t <- token
    p <- getPosition
    void (many whitespace)
    pure (t, p)
  eof
  pure ts

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
  choice $
    try
      <$> [ T.Keyword
              <$> ( do
                      tok <- keyword
                      _ <- lookAhead (noneOf (['a' .. 'z'] <> ['A' .. 'Z'] <> "_" <> ['0' .. '9'] <> "_\'"))
                      pure tok
                  ),
            T.LeftRightArrow <$ string "<->",
            T.LeftRightArrow <$ string "↔",
            T.ThinArrow <$ string "->",
            T.ThinArrow <$ string "→",
            T.OpenParen <$ string "(",
            T.CloseParen <$ string ")",
            T.OpenBracket <$ string "[",
            T.CloseBracket <$ string "]",
            T.OpenBrace <$ string "{",
            T.CloseBrace <$ string "}",
            constantNatural,
            constantInteger,
            constantFinite,
            constantField,
            -- the T.Const case must come after the other constant
            -- cases to deal with ambiguity
            T.Const <$> nonNegativeIntegerLiteral,
            T.AddNOp <$ string "+N",
            T.AddNOp <$ string "+ℕ",
            T.MulNOp <$ string "*N",
            T.MulNOp <$ string "×ℕ",
            T.AddZOp <$ string "+Z",
            T.AddZOp <$ string "+ℤ",
            T.MulZOp <$ string "*Z",
            T.MulZOp <$ string "×ℤ",
            T.AddFpOp <$ string "+F",
            T.AddFpOp <$ string "+𝔽",
            T.MulFpOp <$ string "*F",
            T.MulFpOp <$ string "×𝔽",
            T.ProductOp <$ string "×",
            T.Comma <$ string ",",
            T.CoproductOp <$ string "⊕",
            T.LessOrEqual <$ string "<=",
            T.LessOrEqual <$ string "≤",
            T.Caret <$ string "^",
            T.Less <$ string "<", -- NOTICE: must come after ascii LessOrEqual case
            T.And <$ string "&",
            T.And <$ string "∧",
            T.Or <$ string "|",
            T.Or <$ string "∨",
            T.Not <$ string "!",
            T.Not <$ string "¬",
            T.ForAll <$ string "all",
            T.ForAll <$ string "∀",
            T.ForSome <$ string "some",
            T.ForSome <$ string "∃",
            T.Lambda <$ string "\\",
            T.Lambda <$ string "λ",
            T.ThickArrow <$ string "=>",
            T.ThickArrow <$ string "⇨",
            T.Congruent <$ string "~=",
            T.Congruent <$ string "≅",
            T.DefEquals <$ string ":=",
            T.DefEquals <$ string "≔",
            T.Semicolon <$ string ";",
            T.Period <$ string ".",
            T.Keyword K.Let <$ string "let",
            -- the following must come after some others in order to deal with ambiguity
            T.ProductOp <$ string "*",
            T.CoproductOp <$ string "+",
            T.Colon <$ string ":",
            T.Equal <$ string "=",
            -- Var must come last in order to deal with ambiguity
            T.Var <$> name
          ]

keyword :: Parser Keyword
keyword =
  choice $
    try
      <$> [ K.Type <$ string "Type",
            K.Prop <$ string "Prop",
            K.N <$ string "ℕ",
            K.N <$ string "N",
            K.Z <$ string "ℤ",
            K.Z <$ string "Z",
            K.Fin <$ string "Fin",
            K.F <$ string "F",
            K.F <$ string "𝔽",
            K.Cast <$ string "cast",
            K.Data <$ string "data",
            K.Inverse <$ string "inverse",
            K.To <$ string "to",
            K.From <$ string "from",
            K.Def <$ string "def",
            K.IsNothing <$ string "isNothing",
            K.Maybe <$ string "Maybe",
            K.Maybe' <$ string "maybe",
            K.Just' <$ string "just",
            K.Nothing' <$ string "nothing",
            K.Exists <$ string "exists",
            K.List <$ string "List",
            K.Length <$ string "length",
            K.Nth <$ string "nth",
            K.Sum <$ string "Σ",
            K.SumMapLength <$ string "sumMapLength",
            K.SumListLookup <$ string "sumListLookup",
            K.Sum <$ string "sum",
            K.Pi1 <$ string "π1",
            K.Pi1 <$ string "pi1",
            K.Pi2 <$ string "π2",
            K.Pi2 <$ string "pi2",
            K.Iota1 <$ string "ι1",
            K.Iota2 <$ string "ι2",
            K.Iota1 <$ string "iota1",
            K.Iota2 <$ string "iota2",
            K.Map <$ string "Map",
            K.Lookup <$ string "lookup",
            K.Keys <$ string "keys"
          ]

name :: Parser Name
name = do
  begin <- oneOf (['a' .. 'z'] <> ['A' .. 'Z'] <> "_")
  rest <- many (oneOf (['a' .. 'z'] <> ['A' .. 'Z'] <> ['0' .. '9'] <> "_\'"))
  pure (Sym (cons begin (pack rest)))

constantNatural :: Parser Token
constantNatural = do
  i <- nonNegativeIntegerLiteral
  void $ char 'N' <|> char 'ℕ'
  pure (T.ConstN i)

constantInteger :: Parser Token
constantInteger = do
  i <- integerLiteral
  void $ char 'Z' <|> char 'ℤ'
  pure (T.ConstZ i)

constantField :: Parser Token
constantField = do
  i <- integerLiteral
  void $ char 'F' <|> char '𝔽'
  pure (T.ConstF i)

constantFinite :: Parser Token
constantFinite = do
  void $ string "fin"
  _ <- many whitespace
  void $ char '('
  _ <- many whitespace
  i <- integerLiteral
  _ <- many whitespace
  void $ char ')'
  pure (T.ConstFin i)

integerLiteral :: Parser Integer
integerLiteral = negativeIntegerLiteral <|> nonNegativeIntegerLiteral

negativeIntegerLiteral :: Parser Integer
negativeIntegerLiteral = do
  void (char '-')
  negate <$> nonNegativeIntegerLiteral

nonNegativeIntegerLiteral :: Parser Integer
nonNegativeIntegerLiteral =
  digitsToInteger <$> many1 (oneOf ['0' .. '9'])

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
    _ -> 0

digitsToInteger :: String -> Integer
digitsToInteger = foldl' (\a x -> a * 10 + x) 0 . fmap digitToInteger
