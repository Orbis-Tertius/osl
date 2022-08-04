{-# LANGUAGE LambdaCase #-}


module OSL.Parse (parseContext) where


import Control.Monad (guard, mzero)
import Data.Either.Combinators (mapLeft)
import Data.Text (Text, pack, unpack)
import Text.Parsec (SourceName, SourcePos, Parsec, many, eof, token, (<|>), try, choice)
import qualified Text.Parsec.Prim as Prim

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Context (..), Name, Declaration (..), Term (..), Type (..))
import qualified OSL.Types.Keyword as K
import OSL.Types.Token (Token (..))
import qualified OSL.Types.Token as T


parseContext :: SourceName -> [(Token, SourcePos)] -> Either (ErrorMessage ()) (Context SourcePos)
parseContext = parse' context


type Parser = Parsec [(Token, SourcePos)] ()


parse' :: Parser a -> SourceName -> [(Token, SourcePos)] -> Either (ErrorMessage ()) a
parse' p n = mapLeft (ErrorMessage () . pack . show) . Prim.parse p n


consume :: ((Token, SourcePos) -> Maybe a) -> Parser a
consume = token (unpack . printToken . fst) snd


consumeExact :: Token -> (SourcePos -> a) -> Parser a
consumeExact tok tm =
  consume (\(t, p) -> guard (t == tok) >> return (tm p))


consumeExact_ :: Token -> Parser ()
consumeExact_ tok = consumeExact tok (const ())


printToken :: Token -> Text
printToken = pack . show


context :: Parser (Context SourcePos)
context = do
  decls <- many declaration
  eof
  return (Context decls)


declaration :: Parser (Name, Declaration SourcePos)
declaration = dataDeclaration <|> defDeclaration <|> freeDeclaration


dataDeclaration :: Parser (Name, Declaration SourcePos)
dataDeclaration = do
  consumeExact_ (T.Keyword K.Data)
  n <- name
  consumeExact_ T.Congruent
  t <- type'
  consumeExact_ T.Period
  return (n, Data t)


defDeclaration :: Parser (Name, Declaration SourcePos)
defDeclaration = do
  consumeExact_ (T.Keyword K.Def)
  n <- name
  consumeExact_ T.Colon
  ty <- type'
  consumeExact_ T.DefEquals
  def <- term
  consumeExact_ T.Period
  return (n, Defined ty def)


freeDeclaration :: Parser (Name, Declaration SourcePos)
freeDeclaration = do
  n <- name
  consumeExact_ T.Colon
  t <- type'
  consumeExact_ T.Period
  return (n, FreeVariable t)


name :: Parser Name
name =
  consume $
    \case
      (T.Var x, _) -> pure x
      _            -> mzero


type' :: Parser (Type SourcePos)
type' =
  choice
  $
  try
  <$>
  [ consumeExact (T.Keyword K.Prop) Prop
  ]


term :: Parser (Term SourcePos)
term = todo


todo :: a
todo = todo
