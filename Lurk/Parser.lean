import Megaparsec.Char
import Megaparsec.Common
import Lurk.LDON

def Char.isHexDigit (c : Char) : Bool :=
  c.isDigit || (c.val ≥ 97 && c.val ≤ 102)

def Char.asHexDigitToNat (c : Char) : Nat :=
  if c.isDigit then c.val.toNat - 48
  else 10 + c.val.toNat - 97

namespace Lurk.Parser

open Megaparsec Char Parsec Common

abbrev P := Parsec Char String Unit

def nonHexNumP : P LDON := do
  let str := String.mk (← some' (satisfy Char.isDigit))
  return .num $ .ofNat $ String.toNat! str

def hexNumP : P LDON := do
  discard $ string "0x"
  discard $ many' (satisfy (· == '0'))
  let chars ← some' (satisfy Char.isHexDigit)
  let (n, _) := chars.foldr (init := (0, 1)) fun c (n, p) =>
    (n + p * c.asHexDigitToNat, 16 * p)
  return .num $ .ofNat n

def numP : P LDON :=
  hexNumP <|> nonHexNumP

-- def charP : P LDON := attempt do
--   discard $ single '\''
--   let c ← satisfy fun _ => true
--   discard $ single '\''
--   return .char c

def charP : P LDON := do
  discard $ string "#\\"
  .char <$> anySingle

def strP : P LDON := between '"' '"' $
  .str <$> String.mk <$> many' (satisfy (· != '\"'))

def validSpecialSymChar : Char → Bool
  | '+'
  | '-'
  | '*'
  | '/'
  | '='
  | '<'
  | '>' => true
  | _ => false

def noEscSymP : P LDON := do
  let c ← satisfy fun c => c.isAlpha || validSpecialSymChar c
  let x ← many' (satisfy fun c => c.isAlphanum || validSpecialSymChar c)
  let i : String := ⟨c :: x⟩
  let iU := i.toUpper
  if LDON.reservedSyms.contains iU then
    return .sym iU
  else
    return .sym i

def escSymP : P LDON := between '|' '|' $
  .sym <$> String.mk <$> many' (satisfy (· != '|'))

def symP : P LDON :=
  escSymP <|> noEscSymP

def blanksP : P Unit :=
  discard $ many' $ oneOf [' ', '\n', '\t']

def atomP : P LDON :=
  symP <|> numP <|> charP <|> strP

mutual

partial def quoteP : P LDON := do
  discard $ single '\''
  let x ← astP
  return .mkQuote x

partial def listP : P LDON := between '(' ')' $ do
  blanksP
  let x ← many' astP
  return .consWith x .nil

partial def dottedListP : P LDON := between '(' ')' $ do
  let xs ← some' astP
  discard $ single '.'
  let x ← astP
  return .consWith xs x

partial def astP : P LDON := do
  blanksP
  let x ← atomP <|> (attempt listP) <|> dottedListP <|> quoteP
  blanksP
  return x

end

protected def parse (code : String) : Except String LDON :=
  Except.mapError toString $ parse astP code

end Lurk.Parser
