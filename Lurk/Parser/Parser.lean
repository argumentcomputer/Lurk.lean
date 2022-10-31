import Megaparsec.String
import Lurk.Syntax2.AST

namespace Lurk.Syntax

open Megaparsec.Parsec Megaparsec.Common
open Lurk.Syntax AST

abbrev P := Parsec Char String Unit

def nilP : P AST := do
  discard $ satisfy fun c => c.toUpper == 'N'
  discard $ satisfy fun c => c.toUpper == 'I'
  discard $ satisfy fun c => c.toUpper == 'L'
  return .nil

def numP : P AST := do
  let x ← some' (satisfy Char.isDigit)
  let str := String.mk x
  return .num $ String.toNat! str

def charP : P AST := do
  discard $ single '\''
  let c ← satisfy fun _ => true
  discard $ single '\''
  return .char c

def strP : P AST := do
  discard $ single '"'
  let x ← many' (satisfy fun c => c != '\"')
  discard $ single '"'
  return .str $ ⟨x⟩

def symP : P AST := do
  let c ← satisfy Char.isAlpha
  let x ← many' (satisfy Char.isAlphanum)
  return .sym $ String.toUpper ⟨c :: x⟩

def atomP : P AST := Megaparsec.attempt $ do
  discard $ many' (satisfy fun c => c == ' ')
  nilP <|> numP <|> charP <|> strP <|> symP

partial def parensP : P AST := Megaparsec.attempt $ do
  discard $ many' (satisfy fun c => c == ' ')
  discard $ single '('
  let x ← many' $ atomP <|> parensP
  discard $ single ')'
  return buildCons x nil

def astP : P AST := atomP <|> parensP

def quoteP : P AST := do
  discard $ single '\''
  discard $ many' (satisfy fun c => c == ' ')
  let x ← astP
  return ~[sym "QUOTE", x]

/-- TODO: dotted cons -/
protected def parse (code : String) : Except String AST :=
  match parse (quoteP <|> astP) code with
  | .right x => return x
  | .left x => throw $ toString x

end Lurk.Syntax
