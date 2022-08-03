module OSL.Types.Token (Token (..)) where


import OSL.Types.Keyword (Keyword (..))
import OSL.Types.OSL (Name (..))


data Token = Var Name | Keyword Keyword | FunctionArrow | Colon
  | OpenParen | CloseParen | ConstN Integer | ConstZ Integer | ConstFin Integer
  | ProductOp | Comma | CoproductOp 
  | Lambda | LambdaArrow | Congruent | DefEquals | Semicolon | Period
