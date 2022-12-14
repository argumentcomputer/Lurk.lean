import Lurk.Frontend.AST
import Lurk.Scalar.Datatypes

namespace Lurk.Scalar

open Frontend (AST)

structure DecodeContext where
  store : ScalarStore
  visit : Std.RBSet ScalarPtr compare

abbrev DecodeM := ReaderT DecodeContext $ ExceptT String $
  StateM (Std.RBMap ScalarPtr AST compare)

def withVisiting (ptr : ScalarPtr) : DecodeM α → DecodeM α :=
  withReader fun ctx => { ctx with visit := ctx.visit.insert ptr }

partial def decodeAST (ptr : ScalarPtr) : DecodeM AST := do
  match (← get).find? ptr with
  | some ast => pure ast
  | none =>
    if (← read).visit.contains ptr then throw "Cycle of pointers detected"
    else withVisiting ptr do
      let ast ← match ptr with
        | ⟨.nil,  _⟩ => return .nil
        | ⟨.num,  x⟩ => return .num x
        | ⟨.char, x⟩ => return .char (Char.ofNat x)
        | ⟨.str, F.zero⟩ => return .str default
        | ptr => match (← read).store.exprs.find? ptr with
          | none => throw s!"Pointer not found in the store: {ptr}"
          | some none => throw "TODO opaque"
          | some (some expr) => match (ptr.tag, expr) with
            | (.sym, .sym x) => match ← decodeAST x with
              | .str s => return .sym s
              | _ => throw s!"Invalid pointer for a symbol: {x}"
            | (.str, .strCons h t) => match (h.tag, ← decodeAST t) with
              | (.char, .str t) => return .str ⟨Char.ofNat h.val :: t.data⟩
              | _ => throw "Error when decoding string"
            | (.cons, .cons car cdr) => return .cons (← decodeAST car) (← decodeAST cdr)
            | _ => throw s!"Tag {ptr.tag} incompatible with expression {expr}"
      modifyGet fun stt => (ast, stt.insert ptr ast)

def decode (ptr : ScalarPtr) (store : ScalarStore) : Except String AST :=
  (StateT.run (ReaderT.run (decodeAST ptr) ⟨store, default⟩) default).1

end Lurk.Scalar
