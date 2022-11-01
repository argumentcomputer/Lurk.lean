import Megaparsec.String
import Lurk.Syntax.AST

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

def noEscSymP : P AST := do
  let c ← satisfy Char.isAlpha
  let x ← many' (satisfy fun c => c.isAlphanum || c == '-' || c == ':')
  return .sym $ String.toUpper ⟨c :: x⟩

def escSymP : P AST := do
  discard $ single '|'
  let x ← many' (satisfy fun c => c != '|')
  discard $ single '|'
  return .sym $ ⟨x⟩

def symP : P AST := escSymP <|> noEscSymP

def atomP : P AST := Megaparsec.attempt $ do
  discard $ many' (satisfy fun c => c == ' ')
  let a ← nilP <|> numP <|> charP <|> strP <|> symP
  discard $ many' (satisfy fun c => c == ' ')
  return a

mutual 

partial def quoteP : P AST := Megaparsec.attempt $ do
  discard $ many' (satisfy fun c => c == ' ')
  discard $ single '\''
  let x ← astP
  return mkQuote x

partial def listP : P AST := Megaparsec.attempt $ do
  discard $ many' (satisfy fun c => c == ' ')
  discard $ single '('
  let x ← many' astP
  discard $ single ')'
  return consWith x nil

partial def dottedListP : P AST := Megaparsec.attempt $ do
  discard $ many' (satisfy fun c => c == ' ')
  discard $ single '('
  let xs ← many1' astP
  discard $ many' (satisfy fun c => c == ' ')
  discard $ single '.'
  let x ← astP
  discard $ single ')'
  return consWith xs x

partial def astP : P AST := atomP <|> quoteP <|> listP <|> dottedListP

end 

protected def parse (code : String) : Except String AST :=
  match parse astP code with
  | .right x => return x
  | .left x => throw $ toString x

end Lurk.Syntax
