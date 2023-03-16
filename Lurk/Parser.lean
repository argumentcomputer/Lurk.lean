import Megaparsec.Char
import Megaparsec.Common
import Lurk.LDON

namespace Lurk.Parser

open Megaparsec Char Parsec Common

abbrev P := Parsec Char String Unit

def numP : P LDON := do
  let x ← some' (satisfy Char.isDigit)
  let str := String.mk x
  return .num $ .ofNat $ String.toNat! str

-- def charP : P LDON := attempt do
--   discard $ single '\''
--   let c ← satisfy fun _ => true
--   discard $ single '\''
--   return .char c

def charP : P LDON := do
  discard $ string "#\\"
  .char <$> anySingle

def strP : P LDON := between '"' '"' $
  .str <$> String.mk <$> many' (satisfy fun c => c != '\"')

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
  .sym <$> String.mk <$> many' (satisfy fun c => c != '|')

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
