import Megaparsec.Char
import Megaparsec.Common
import Lurk.Frontend.AST

namespace Lurk.Frontend.Parser

open Megaparsec Char Parsec Common

abbrev P := Parsec Char String Unit

def numP : P AST := do
  let x ← some' (satisfy Char.isDigit)
  let str := String.mk x
  return .num $ String.toNat! str

-- def charP : P AST := attempt do
--   discard $ single '\''
--   let c ← satisfy fun _ => true
--   discard $ single '\''
--   return .char c

def charP : P AST := do
  discard $ string "#\\"
  .char <$> anySingle

def strP : P AST := between '"' '"' $
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

def noEscSymP : P AST := do
  let c ← satisfy fun c => c.isAlpha || validSpecialSymChar c
  let x ← many' (satisfy fun c => c.isAlphanum || validSpecialSymChar c)
  let i : String := ⟨c :: x⟩
  let iU := i.toUpper
  if AST.reservedSyms.contains iU then
    return .sym iU
  else
    return .sym i

def escSymP : P AST := between '|' '|' $
  .sym <$> String.mk <$> many' (satisfy fun c => c != '|')

def symP : P AST :=
  escSymP <|> noEscSymP

def blanksP : P Unit :=
  discard $ many' $ oneOf [' ', '\n', '\t']

def atomP : P AST :=
  symP <|> numP <|> charP <|> strP

mutual

partial def quoteP : P AST := do
  discard $ single '\''
  let x ← astP
  return .mkQuote x

partial def listP : P AST := between '(' ')' $ do
  blanksP
  let x ← many' astP
  return .consWith x .nil

partial def dottedListP : P AST := between '(' ')' $ do
  let xs ← some' astP
  discard $ single '.'
  let x ← astP
  return .consWith xs x

partial def astP : P AST := do
  blanksP
  let x ← atomP <|> (attempt listP) <|> dottedListP <|> quoteP
  blanksP
  return x

end

protected def parse (code : String) : Except String AST :=
  Except.mapError toString $ parse astP code

end Lurk.Frontend.Parser
