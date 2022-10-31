import Lurk.Hashing2.Hashing

namespace Lurk.Hashing

open Syntax

abbrev Cache := Std.RBMap ScalarPtr AST compare

structure Context where
  store : ScalarStore
  visit : Std.RBSet ScalarPtr compare

abbrev DecodeM := ReaderT Context $ ExceptT String $ StateM Cache

def withVisiting (ptr : ScalarPtr) : DecodeM α → DecodeM α :=
  withReader fun ctx => { ctx with visit := ctx.visit.insert ptr }

mutual

partial def decodeAST : ScalarPtr → DecodeM AST
  | ⟨.nil,  _⟩ => return .nil
  | ⟨.num,  x⟩ => return .num x
  | ⟨.char, x⟩ => return .char (Char.ofNat x)
  | ptr => do
    match (← read).store.exprs.find? ptr with
    | none => throw s!"Pointer not found in the store: {ptr}"
    | some expr => match (ptr.tag, expr) with
      | (.sym, .sym x) => match ← getOrDecodeAST x with
        | .str s => return .sym s
        | _ => throw s!"Invalid pointer for a symbol: {x}"
      | (.str, .strCons h t) => match (h.tag, ← getOrDecodeAST t) with
        | (.char, .str t) => return .str ⟨Char.ofNat h.val :: t.data⟩
        | _ => throw "Error when decoding string"
      | (.str, .strNil) => return .str ""
      | (.cons, .cons car cdr) =>
        return .cons (← getOrDecodeAST car) (← getOrDecodeAST cdr)
      | _ => throw s!"Tag {ptr.tag} incompatible with expression {expr}"

partial def getOrDecodeAST (ptr : ScalarPtr) : DecodeM AST := do
  match (← get).find? ptr with
  | some ast => pure ast
  | none =>
    if (← read).visit.contains ptr then throw "Cycle of pointers detected"
    else withVisiting ptr do
      let ast ← decodeAST ptr
      modifyGet fun stt => (ast, stt.insert ptr ast)

end

def decode (ptr : ScalarPtr) (store : ScalarStore) : Except String AST :=
  (StateT.run (ReaderT.run (decodeAST ptr) ⟨store, default⟩) default).1

end Lurk.Hashing
