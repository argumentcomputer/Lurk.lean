import Lurk.Hashing2.Hashing

namespace Lurk.Hashing

open Syntax

abbrev Cache := Std.RBMap ScalarPtr AST compare

abbrev DecodeM := ReaderT ScalarStore $ ExceptT String $ StateM Cache

mutual

partial def decodeAST (ptr : ScalarPtr) : DecodeM AST := do
  match (← read).exprs.find? ptr with
  | none => throw s!"Pointer not found on the store:\n  {ptr}"
  | some expr => match (ptr.tag, expr) with
    | (.nil, _) => return .nil
    | (.num, .num x) => return .num x
    | (.char, .char x) => return .char (Char.ofNat x)
    | (.sym, .sym x) => match ← getOrDecodeAST x with
      | .str s => return .sym s
      | _ => throw s!"Invalid pointer for a symbol: {x}"
    | (.str, .strCons h t) => match (h.tag, ← getOrDecodeAST t) with
      | (.char, .str t) => return .str ⟨Char.ofNat h.val :: t.data⟩
      | _ => throw "Error when decoding string"
    | (.str, .strNil) => return .str ""
    | (.cons, .cons car cdr) => return .cons (← getOrDecodeAST car) (← getOrDecodeAST cdr)
    | _ => throw s!"Pointer tag {ptr.tag} incompatible with expression: {expr}"

partial def getOrDecodeAST (ptr : ScalarPtr) : DecodeM AST := do
  match (← get).find? ptr with
  | some ast => pure ast
  | none =>
    -- todo: Use the reader to detect cycles (infinite loops)
    let ast ← decodeAST ptr
    modifyGet fun stt => (ast, stt.insert ptr ast)

end

def decode (ptr : ScalarPtr) (store : ScalarStore) : Except String AST :=
  (StateT.run (ReaderT.run (decodeAST ptr) store) default).1

end Lurk.Hashing
