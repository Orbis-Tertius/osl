{-# LANGUAGE LambdaCase #-}


module OSL.Parse (parseContext) where


import Control.Monad (guard, mzero)
import Data.Either.Combinators (mapLeft)
import Data.Text (Text, pack, unpack)
import Text.Parsec (SourceName, SourcePos, Parsec, many, eof, token, (<|>), try, choice, getPosition, option, many1)
import qualified Text.Parsec.Prim as Prim

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Context (..), Name, Declaration (..), Term (..), Type (..))
import qualified OSL.Types.Keyword as K
import OSL.Types.Token (Token)
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
  t <- type0
  consumeExact_ T.Period
  return (n, Data t)


defDeclaration :: Parser (Name, Declaration SourcePos)
defDeclaration = do
  consumeExact_ (T.Keyword K.Def)
  n <- name
  consumeExact_ T.Colon
  ty <- type0
  consumeExact_ T.DefEquals
  def <- term0
  consumeExact_ T.Period
  return (n, Defined ty def)


freeDeclaration :: Parser (Name, Declaration SourcePos)
freeDeclaration = do
  n <- name
  consumeExact_ T.Colon
  t <- type0
  consumeExact_ T.Period
  return (n, FreeVariable t)


name :: Parser Name
name =
  consume $
    \case
      (T.Var x, _) -> pure x
      _            -> mzero


type0 :: Parser (Type SourcePos)
type0 = do
  p <- getPosition
  t <- type1
  ts <- option Nothing (consumeExact_ T.ThinArrow >> (Just <$> type0))
  case ts of
    Nothing -> return t
    Just t' -> return (F p t t')


type1 :: Parser (Type SourcePos)
type1 = do
  p <- getPosition
  t <- type1
  ts <- option Nothing ((Just. Left <$> productTail) <|> (Just . Right <$> coproductTail))
  case ts of
    Nothing -> return t
    Just (Left ts') -> return (Product p t ts')
    Just (Right ts') -> return (Coproduct p t ts')


productTail :: Parser (Type SourcePos)
productTail = do
  p <- getPosition
  consumeExact_ T.ProductOp
  t <- type2
  ts <- option Nothing (Just <$> productTail)
  case ts of
    Nothing -> return t
    Just ts' -> return (Product p t ts')


coproductTail :: Parser (Type SourcePos)
coproductTail = do
  p <- getPosition
  consumeExact_ T.CoproductOp
  t <- type2
  ts <- option Nothing (Just <$> coproductTail)
  case ts of
    Nothing -> return t
    Just ts' -> return (Coproduct p t ts')


type2 :: Parser (Type SourcePos)
type2 =
  choice
  $
  try
  <$>
  [ consumeExact (T.Keyword K.Prop) Prop
  , consumeExact (T.Keyword K.N) N
  , consumeExact (T.Keyword K.Z) Z
  , NamedType <$> getPosition <*> name
  , parenthesizedType
  , finiteType
  , maybeType
  , listType
  , mapType
  ]


parenthesizedType :: Parser (Type SourcePos)
parenthesizedType = do
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  return t


finiteType :: Parser (Type SourcePos)
finiteType = do
  consumeExact_ (T.Keyword K.Fin)
  consumeExact_ T.OpenParen
  t <- consume $
    \case
      (T.Const i, p) -> return (Fin p i)
      _ -> mzero
  consumeExact_ T.CloseParen
  return t


maybeType :: Parser (Type SourcePos)
maybeType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Maybe)
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  return (Maybe p t)


listType :: Parser (Type SourcePos)
listType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.List)
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  return (List p t)


mapType :: Parser (Type SourcePos)
mapType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Map)
  consumeExact_ T.OpenParen
  t0 <- type0
  consumeExact_ T.Comma
  t1 <- type0
  consumeExact_ T.CloseParen
  return (Map p t0 t1)


term0 :: Parser (Term SourcePos)
term0 =
  choice
  $
  [ quantifier T.ForAll ForAll
  , quantifier T.ForSome ForSome
  , lambda
  , letExpr
  , term1
  ]


quantifier :: Token
  -> (SourcePos
      -> Name
      -> Type (SourcePos)
      -> Term (SourcePos)
      -> Term SourcePos)
  -> Parser (Term SourcePos)
quantifier tok ctor = do
  p <- getPosition
  consumeExact_ tok
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  consumeExact_ T.Comma
  q <- term0
  return (ctor p varName varType q)


lambda :: Parser (Term SourcePos)
lambda = do
  p <- getPosition
  consumeExact_ T.Lambda
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  consumeExact_ T.ThickArrow
  y <- term0
  return (Lambda p varName varType y)


letExpr :: Parser (Term SourcePos)
letExpr = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Let)
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  consumeExact_ T.DefEquals
  def <- term0
  consumeExact_ T.Semicolon
  y <- term0
  return (Let p varName varType def y)


term1 :: Parser (Term SourcePos)
term1 =
  choice
  $
  try
  <$>
  [ binaryOp term2 T.And And
  , binaryOp term2 T.Or Or
  , binaryOp term2 T.ThinArrow Implies
  , term2
  ]


term2 :: Parser (Term SourcePos)
term2 =
  choice
  $
  try
  <$>
  [ binaryOp term3 T.Equal Equal
  , binaryOp term3 T.LessOrEqual LessOrEqual
  , term3
  ]


term3 :: Parser (Term SourcePos)
term3 =
  choice
  $
  try
  <$>
  [ binaryOp term4 T.AddNOp (applyBinaryOp AddN)
  , binaryOp term4 T.MulNOp (applyBinaryOp MulN)
  , binaryOp term4 T.AddZOp (applyBinaryOp AddZ)
  , binaryOp term4 T.MulZOp (applyBinaryOp MulZ)
  , binaryOp term4 T.ProductOp FunctionProduct
  , binaryOp term4 T.CoproductOp FunctionCoproduct
  , term4
  ]


term4 :: Parser (Term SourcePos)
term4 =
  choice
  $
  [ tuple
  , unaryOp T.Not Not
  , constant
  , unaryOp (T.Keyword K.Cast) (applyUnaryOp Cast)
  , todo
  ]


constant :: Parser (Term SourcePos)
constant =
  consume $
    \case
      (T.ConstN i, p) -> return (ConstN p i)
      (T.ConstZ i, p) -> return (ConstZ p i)
      (T.ConstFin i, p) -> return (ConstFin p i)
      _ -> mzero


applyUnaryOp :: (SourcePos -> Term SourcePos)
  -> SourcePos
  -> Term SourcePos
  -> Term SourcePos
applyUnaryOp op p = Apply p (op p)


applyBinaryOp :: (SourcePos -> Term SourcePos)
  -> SourcePos
  -> Term SourcePos
  -> Term SourcePos
  -> Term SourcePos
applyBinaryOp op p x y =
  (Apply p (Apply p (op p) x) y)


binaryOp :: Parser (Term SourcePos)
  -> Token
  -> (SourcePos
      -> Term SourcePos
      -> Term SourcePos
      -> Term SourcePos)
  -> Parser (Term SourcePos)
binaryOp subexpr opTok opCtor = do
  p <- getPosition
  x <- subexpr
  consumeExact_ opTok
  y <- subexpr
  return (opCtor p x y)


unaryOp :: Token
  -> (SourcePos -> Term SourcePos -> Term SourcePos)
  -> Parser (Term SourcePos)
unaryOp opTok opCtor = do
  p <- getPosition
  consumeExact_ opTok
  consumeExact_ T.OpenParen
  x <- term0
  consumeExact_ T.CloseParen
  return (opCtor p x)


tuple :: Parser (Term SourcePos)
tuple = do
  p <- getPosition
  x <- term0
  xs <- many1 term0
  return (foldr (Apply p) (Pair p) (x:xs))


todo :: a
todo = todo
