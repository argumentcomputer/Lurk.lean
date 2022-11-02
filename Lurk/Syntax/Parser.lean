import Megaparsec.String
import Lurk.Syntax.AST

namespace Lurk.Syntax

open Megaparsec Parsec Common
open Lurk.Syntax AST

abbrev P := Parsec Char String Unit

def nilP : P AST := attempt do
  discard $ single 'n' <|> single 'N'
  discard $ single 'i' <|> single 'I'
  discard $ single 'l' <|> single 'L'
  return .nil

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

def symP : P AST := escSymP <|> noEscSymP

def atomP : P AST := do
  nilP <|> numP <|> charP <|> strP <|> symP

def blanksP : P Unit := do
  discard $ many' (satisfy fun c => c == ' ')
  discard $ many' (satisfy fun c => c == '\t')
  discard $ many' (satisfy fun c => c == '\n')

mutual 

partial def quoteP : P AST := do
  discard $ single '\''
  blanksP
  let x ← astP
  return mkQuote x

partial def listP : P AST := attempt do
  discard $ single '('
  blanksP
  let x ← many' astP
  discard $ single ')'
  return consWith x nil

partial def dottedListP : P AST := do
  discard $ single '('
  blanksP
  let xs ← many1' astP
  discard $ single '.'
  let x ← astP
  discard $ single ')'
  return consWith xs x

partial def astP : P AST := do
  blanksP
  let x ← atomP <|> quoteP <|> listP <|> dottedListP
  blanksP
  return x

end 

protected def parse (code : String) : Except String AST :=
  match parse astP code with
  | .right x => return x
  | .left x => throw $ toString x

-- #eval discard $ parseTestP astP "(begin
--     (current-env)
--     (g x s)
--     (let (
--         (n1 nil)
--         (n2 (quote (nil)))
--         (n3 (begin)))
--       (current-env))
--     ((+ 1 2) (f x) . (cons 4 2)))"

end Lurk.Syntax
