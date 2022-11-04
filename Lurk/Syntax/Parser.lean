import Megaparsec.String
import Lurk.Syntax.AST

namespace Lurk.Syntax

open Megaparsec Parsec Common Lurk.Syntax AST

abbrev P := Parsec Char String Unit

def numP : P AST := do
  let x ← some' (satisfy Char.isDigit)
  let str := String.mk x
  return .num $ String.toNat! str

def charP : P AST := attempt do
  discard $ single '\''
  let c ← satisfy fun _ => true
  discard $ single '\''
  return .char c

def strP : P AST := do
  discard $ single '"'
  let x ← many' (satisfy fun c => c != '\"')
  discard $ single '"'
  return .str $ ⟨x⟩

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
  return .sym $ String.toUpper ⟨c :: x⟩

def escSymP : P AST := do
  discard $ single '|'
  let x ← many' (satisfy fun c => c != '|')
  discard $ single '|'
  return .sym $ ⟨x⟩

def symP : P AST :=
  escSymP <|> noEscSymP

def blanksP : P Unit := do
  discard $ many' $ satisfy [' ', '\n', '\t'].contains

def atomP : P AST :=
  symP <|> numP <|> charP <|> strP

mutual

partial def quoteP : P AST := do
  discard $ single '\''
  let x ← astP
  return mkQuote x

partial def listP : P AST := do
  discard $ single '('
  blanksP
  let x ← many' astP
  discard $ single ')'
  return consWith x nil

partial def dottedListP : P AST := do
  discard $ single '('
  let xs ← many1' astP
  discard $ single '.'
  let x ← astP
  discard $ single ')'
  return consWith xs x

partial def astP : P AST := do
  blanksP
  let x ← atomP <|> (attempt listP) <|> dottedListP <|> quoteP
  blanksP
  return x

end

protected def parse (code : String) : Except String AST :=
  match parse astP code with
  | .right x => return x
  | .left x => throw $ toString x

end Lurk.Syntax
