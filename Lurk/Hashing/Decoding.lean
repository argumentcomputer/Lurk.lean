import Lurk.Hashing.Hashing

namespace Lurk.Hashing

open Lurk.Syntax

def hashString' (s : String) (state : HashState) : ScalarPtr × HashState :=
  StateT.run (hashString s) state

def knownSymbols := [
  "nil",
  "t",
  "quote",
  "lambda",
  -- "_",
  "let",
  "letrec",
  "begin",
  "hide",
  "cons",
  "strcons",
  "car",
  "cdr",
  "commit",
  -- "num",
  "comm",
  -- "char",
  -- "open",
  -- "secret",
  "atom",
  "emit",
  "+",
  "-",
  "*",
  "/",
  "=",
  "<",
  ">",
  "<=",
  ">=",
  "eq",
  "current-env",
  "if"
  -- "terminal",
  -- "dummy",
  -- "outermost",
  -- "error"
]

structure DecodeContext where
  store : ScalarStore
  memo  : Std.RBMap ScalarPtr String compare

abbrev DecodeM := ReaderT DecodeContext $ ExceptT String Id

partial def decodeExpr (ptr : ScalarPtr) : DecodeM Expr := do
  let ctx ← read
  match ctx.store.exprs.find? ptr with
  | none => throw s!"Pointer not found on the store:\n  {ptr}"
  | some expr => match (ptr.tag, expr) with
    | (.nil, .sym ptr') => match ctx.memo.find? ptr' with
      | some "nil" => return .lit .nil
      | _ => throw s!"Pointer incompatible with nil:\n  {ptr'}"
    | (.num, .num x) => return .lit $ .num x
    | (.char, .char x) => return .lit $ .char (Char.ofNat x)
    | (.sym, .sym x) => match ← decodeExpr x with
      | .lit $ .str s => return .sym s
      | _ => throw s!"Invalid pointer for a symbol:\n  {x}"
    | (.str, .strCons h t) => match (← decodeExpr h, ← decodeExpr t) with
      | (.lit $ .char h, .lit $ .str t) => return .lit $ .str ⟨h :: t.data⟩
      | _ => throw "Error when decoding string"
    | (.str, .strNil) =>
      if ptr.val == F.zero then return .lit $ .str ""
      else throw "Invalid pointer for empty string:\n  {ptr}"
    | (.cons, .cons car cdr) => sorry
    | _ => throw s!"Pointer tag {ptr.tag} incompatible with expression:\n  {expr}"

def enhanceStore (store : ScalarStore) : DecodeContext :=
  let state := ⟨store.exprs, default, default, default⟩
  let (state, memo) : HashState × Std.RBMap ScalarPtr String compare :=
    knownSymbols.foldl (init := (state, default)) fun (state, memo) s =>
      let (ptr, state) := hashString' s.toUpper state
      (state, memo.insert ptr s)
  ⟨state.store, memo⟩

def decode (ptr : ScalarPtr) (store : ScalarStore) : Except String Expr :=
  ReaderT.run (decodeExpr ptr) (enhanceStore store)

end Lurk.Hashing
