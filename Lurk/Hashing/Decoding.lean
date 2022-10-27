import Lurk.Hashing.Hashing

namespace Lurk.Hashing

open Lurk.Syntax

def hashSymbol (s : String) (state : HashState) : ScalarPtr × HashState :=
  StateT.run (hashString s) state

def hashExpr' (e : Expr) (state : HashState) : ScalarPtr × HashState :=
  StateT.run (hashExpr e) state

def knownSymbols := [
  "nil",
  "t",
  "quote",
  "lambda",
  -- "_",
  "let",
  "letrec",
  "mutrec",
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

structure Context where
  store : ScalarStore
  memo  : Std.RBMap ScalarPtr String compare

structure State where 
  exprs : Std.RBMap ScalarPtr Expr compare
  sexprs : Std.RBMap ScalarPtr SExpr compare
deriving Inhabited

abbrev DecodeM := ReaderT Context $ ExceptT String $ StateM State

partial def unfoldCons (ptr : ScalarPtr) (acc : Array ScalarPtr := #[]) :
    DecodeM $ Array ScalarPtr := do
  match (← read).memo.find? ptr with
  | some "nil" => return acc
  | _ => match (← read).store.exprs.find? ptr with
    | some (.cons h ⟨.nil, _⟩) => return acc.push h
    | some (.cons h t) => unfoldCons t (acc.push h)
    | some (.sym s) => return acc.push s
    | some x => throw s!"Invalid expression on a cons chain:\n  {x}"
    | none => throw s!"Pointer not found on the store:\n  {ptr}"

mutual 

partial def decodeSExpr (ptr : ScalarPtr) : DecodeM SExpr := do
  let ctx ← read
  match ctx.store.exprs.find? ptr with
  | none => throw s!"Pointer not found on the store:\n  {ptr}"
  | some expr => match (ptr.tag, expr) with
    | (.nil, .sym ptr') => match ctx.memo.find? ptr' with
      | some "nil" => return .lit .nil
      | _ => throw s!"Pointer incompatible with nil:\n  {ptr'}"
    | (.num, .num x) => return .lit $ .num x
    | (.char, .char x) => return .lit $ .char (Char.ofNat x)
    | (.sym, .sym x) => match ← getOrDecodeSExpr x with
      | .lit $ .str s => return .sym s
      | _ => throw s!"Invalid pointer for a symbol:\n  {x}"
    | (.str, .strCons h t) => match (h.tag, ← getOrDecodeSExpr t) with
      | (.char, .lit $ .str t) => return .lit $ .str ⟨Char.ofNat h.val :: t.data⟩
      | _ => throw "Error when decoding string"
    | (.str, .strNil) =>
      if ptr.val == F.zero then return .lit $ .str ""
      else throw s!"Invalid pointer for empty string:\n  {ptr}"
    | (.cons, .cons car cdr) => 
      return .cons (← getOrDecodeSExpr car) (← getOrDecodeSExpr cdr)
    | _ => throw s!"Pointer tag {ptr.tag} incompatible with expression:\n  {expr}"

partial def getOrDecodeSExpr (ptr : ScalarPtr) : DecodeM SExpr := do
  match (← get).sexprs.find? ptr with
  | some sexpr => pure sexpr
  | none =>
    let sexpr ← decodeSExpr ptr
    modifyGet fun stt => (sexpr, {stt with sexprs := stt.sexprs.insert ptr sexpr})

end

mutual

partial def decodeApp (fn : Expr) (args : ScalarPtr) : DecodeM Expr := do
  match ← unfoldCons args with
  | #[] => return .app fn none
  | args => args.foldlM (init := fn) fun fn argPtr => do
      pure $ .app fn $ some (← getOrDecodeExpr argPtr)

partial def decodeExpr (ptr : ScalarPtr) : DecodeM Expr := do
  let ctx ← read
  match ctx.store.exprs.find? ptr with
  | none => throw s!"Pointer not found on the store:\n  {ptr}"
  | some expr => match (ptr.tag, expr) with
    | (.nil, .sym ptr') => match (ctx.memo.find? ptr, ptr.val == ptr'.val) with
      | (some "nil", true) => return .lit .nil
      | _ => throw s!"Pointer incompatible with nil:\n  {ptr}"
    | (.num, .num x) => return .lit $ .num x
    | (.char, .char x) => return .lit $ .char (Char.ofNat x)
    | (.sym, .sym x) => match ← getOrDecodeExpr x with
      | .lit $ .str s => return match s with
        | "NIL" => .lit .nil
        | "T" => .lit .t
        | "CURRENT-ENV" => .currEnv
        | s => .sym s
      | _ => throw s!"Invalid pointer for a symbol:\n  {x}"
    | (.str, .strCons h t) => match (h.tag, ← getOrDecodeExpr t) with
      | (.char, .lit $ .str t) => return .lit $ .str ⟨Char.ofNat h.val :: t.data⟩
      | _ => throw "Error when decoding string"
    | (.str, .strNil) =>
      if ptr.val == F.zero then return .lit $ .str ""
      else throw s!"Invalid pointer for empty string:\n  {ptr}"
    | (.cons, .cons car cdr) => match ctx.memo.find? car with
      | some sym => match sym with
        | "nil" => decodeApp (.lit .nil) cdr
        | "t" => decodeApp (.lit .t) cdr
        | "current-env" => decodeApp (.currEnv) cdr
        | sym => decodeExprOf sym cdr
      | none => decodeApp (← getOrDecodeExpr car) cdr
    | _ => throw s!"Pointer tag {ptr.tag} incompatible with expression:\n  {expr}"

partial def decodeBinders (binders : ScalarPtr) : DecodeM $ List (Name × Expr) := do
  let binders ← unfoldCons binders
  binders.data.mapM fun ptr => do match ← unfoldCons ptr with
    | #[name, value] => do
      let name : Name ← match ← getOrDecodeExpr name with
        | .sym name => pure name
        | e => throw s!"Expected a sym for a binder name but got {e.pprint true false}"
      let value ← getOrDecodeExpr value
      pure (name, value)
    | x => throw s!"Expected a pair of name/value for a binder but got {x.size} elements"

partial def decodeExprOf (carSym : String) (cdrPtr : ScalarPtr) : DecodeM Expr := do
  match (carSym, ← unfoldCons cdrPtr) with
  | ("nil", #[]) => return .lit .nil
  | ("t", #[]) => return .lit .t
  | ("quote", #[body]) => return .quote (← getOrDecodeSExpr body)
  | ("lambda", #[args, body]) =>
    let args ← unfoldCons args
    let args ← args.data.mapM getOrDecodeExpr
    let args ← args.mapM fun e => match e with
      | .sym name => pure name
      | e => throw s!"Expected a sym for lambda arg but got {e.pprint true false}"
    return .lam args (← getOrDecodeExpr body)
  | ("let",    #[binders, body]) => return .letE (← decodeBinders binders) (← getOrDecodeExpr body)
  | ("letrec", #[binders, body]) => return .letRecE (← decodeBinders binders) (← getOrDecodeExpr body)
  | ("mutrec", #[binders, body]) => return .mutRecE (← decodeBinders binders) (← getOrDecodeExpr body)
  | ("begin", es) =>
    if es.isEmpty then return .begin (.lit .nil) (.lit .nil)
    else es.foldlM (init := .lit .nil) fun acc e => do
      pure $ .begin acc (← getOrDecodeExpr e)
  | ("hide", #[a, b]) => return .hide (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("cons", #[a, b]) => return .cons (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("strcons", #[a, b]) => return .strcons (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("car", #[e]) => return .car (← getOrDecodeExpr e)
  | ("cdr", #[e]) => return .cdr (← getOrDecodeExpr e)
  | ("commit", #[e]) => return .commit (← getOrDecodeExpr e)
  -- | ("num", _) => sorry
  | ("comm", #[e]) => return .comm (← getOrDecodeExpr e)
  -- | ("char", _) => sorry
  -- | ("open", _) => sorry
  -- | ("secret", _) => sorry
  | ("atom", #[e]) => return .atom (← getOrDecodeExpr e)
  | ("emit", #[e]) => return .emit (← getOrDecodeExpr e)
  | ("+", #[a, b]) => return .binaryOp .sum (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("-", #[a, b]) => return .binaryOp .diff (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("*", #[a, b]) => return .binaryOp .prod (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("/", #[a, b]) => return .binaryOp .quot (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("=", #[a, b]) => return .binaryOp .numEq (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("<", #[a, b]) => return .binaryOp .lt (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | (">", #[a, b]) => return .binaryOp .gt (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("<=", #[a, b]) => return .binaryOp .le (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | (">=", #[a, b]) => return .binaryOp .ge (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("eq", #[a, b]) => return .binaryOp .eq (← getOrDecodeExpr a) (← getOrDecodeExpr b)
  | ("if", #[a, b, c]) =>
    return .ifE (← getOrDecodeExpr a) (← getOrDecodeExpr b) (← getOrDecodeExpr c)
  -- | ("terminal", _) => sorry
  -- | ("dummy", _) => sorry
  -- | ("outermost", _) => sorry
  -- | ("error", _) => sorry
  | (x, y) => throw s!"Invalid tail length for {x}: {y.size}"

partial def getOrDecodeExpr (ptr : ScalarPtr) : DecodeM Expr := do
  match (← get).exprs.find? ptr with
  | some expr => pure expr
  | none =>
    let expr ← decodeExpr ptr
    modifyGet fun stt => (expr, {stt with exprs := stt.exprs.insert ptr expr})

end

def enhanceStore (store : ScalarStore) : Context :=
  let state := ⟨store.exprs, default, default, default, default⟩
  let (state, memo) : HashState × Std.RBMap ScalarPtr String compare :=
    knownSymbols.foldl (init := (state, default)) fun (state, memo) s =>
      let expr := if s == "nil" then .lit .nil else .sym s.toUpper
      let (ptr, state) := hashExpr' expr state
      (state, memo.insert ptr s)
  ⟨state.store, memo⟩

def decode (ptr : ScalarPtr) (store : ScalarStore) : Except String Expr :=
  (StateT.run (ReaderT.run (decodeExpr ptr) (enhanceStore store)) default).1

end Lurk.Hashing
