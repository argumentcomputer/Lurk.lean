import Lurk.Hashing.HashM
import Poseidon.ForLurk

namespace Lurk.Hashing

open Lurk.Syntax

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

def destructSExpr : SExpr → List Expr
  | .lit l => [.lit l]
  | .sym s => [.sym s]
  | .cons a (.lit .nil) => destructSExpr a
  | .cons a b => destructSExpr a ++ destructSExpr b

-- def hashLit (l : Literal) : HashM ScalarPtr := do
--   _

def hashChar (c : Char) : HashM ScalarPtr := do
  match (← get).charCache.find? c with
  | some ptr => pure ptr
  | none =>
    let ptr := ⟨Tag.char, .ofNat c.toNat⟩
    modifyGet fun stt =>
      (ptr, { stt with charCache := stt.charCache.insert c ptr })

partial def hashString (s : String) : HashM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => 
    let ptr ← match s.data with
    | c :: cs => do
      let headPtr ← hashChar c
      let tailPtr ← hashString ⟨cs⟩
      let ptr := ⟨Tag.str, hashPtrPair headPtr tailPtr⟩
      let expr := .strCons headPtr tailPtr
      addToStore ptr expr 
    | [] => addToStore ⟨Tag.str, F.zero⟩ .strNil
    modifyGet fun stt =>
      (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def hashSym (s : Name) : HashM ScalarPtr := do 
  let ptr ← hashString (s.toString false).toUpper
  addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)

open Lurk.Syntax.SExpr in
partial def hashSExpr (s : SExpr) : HashM ScalarPtr := do 
  match (← get).sexprCache.find? s with 
  | some ptr => pure ptr
  | none => 
    let ptr ← match s with 
    | .lit .nil =>
      let ptr ← hashString "NIL"
      addToStore ⟨Tag.nil, ptr.val⟩ (.sym ptr)
    | .lit .t => hashSym `t
    | .lit (.num n) => addToStore ⟨Tag.num, n⟩ (.num n)
    | .lit (.str s) => hashString s
    | .lit (.char c) => do
      let ptr ← hashChar c
      addToStore ptr (.char ptr.val)
    | .sym s => hashSym s
    | .cons e₁ e₂ => 
      let carPtr ← hashSExpr e₁
      let cdrPtr ← hashSExpr e₂
      let ptr := ⟨Tag.cons, hashPtrPair carPtr cdrPtr⟩
      let expr := .cons carPtr cdrPtr
      addToStore ptr expr
    modifyGet fun stt =>
      (ptr, { stt with sexprCache := stt.sexprCache.insert s ptr })

mutual

partial def hashPtrList (ps : List ScalarPtr) : HashM ScalarPtr := do
  ps.foldrM (init := ← hashExpr $ .lit .nil) fun ptr acc =>
    addToStore ⟨.cons, hashPtrPair ptr acc⟩ (.cons ptr acc)

partial def hashExprList (es : List Expr) : HashM ScalarPtr := do
  hashPtrList (← es.mapM hashExpr)

partial def hashBlock (kind : Name) (binders : List (Name × Expr)) (body : Expr) :
    HashM ScalarPtr := do
  let bodyPtr ← hashExpr body
  let bindersPtr ← hashPtrList
    (← binders.mapM fun b => hashExprList [.sym b.1, b.2])
  let headPtr ← hashExpr $ .sym kind
  hashPtrList [headPtr, bindersPtr, bodyPtr]

/-- note on caching:
  `hashExpr` doesn't have the best caching behavior with strings.
  Currently, when we hash a string `s`, we will first try to find `s`
  in `exprCache`, and call `hashString` if we fail. In `hashString`,
  we try to find `s` again, but in `stringCache` instead. Accessing 
  `exprCache` is somewhat expensive, since 1. we must do a full `Expr`-`Expr`
  comparison at each node and 2. `exprCache` dwarfs the size of `stringCache`.
  However, this is probably still much faster than the extremely expensive 
  Posideon hash that we do to generate fresh scalar pointers, so we are 
  seeing speedup. 

  The ideal solution would be to take advantage of `charCache` and
  `stringCache` fully by checking them first, and only defaulting to
  `exprCache` for non-string/char/symbol `Expr`s.
-/
partial def hashExpr (e : Expr) : HashM ScalarPtr := do
  match (← get).exprCache.find? e with
  | some ptr => pure ptr
  | none =>
    let ptr ← match e with
      | .lit .nil => do
        -- `nil` has its own tag instead of `.sym`. Thus we need to manually
        -- hash it as a string and make a `.nil` pointer with it
        let ptr ← hashString "NIL"
        addToStore ⟨Tag.nil, ptr.val⟩ (.sym ptr)
      | .lit .t => hashSym `t
      | .lit (.num n) => addToStore ⟨Tag.num, n⟩ (.num n)
      | .lit (.str s) => hashString s
      | .lit (.char c) => hashChar c
      | .sym name => hashSym name
      | .currEnv => hashExpr $ .sym "current-env"
      | .app fn none       => hashExprList [fn]
      | e@(.app ..) => hashExprList e.appTelescope
      | .quote (.lit l) => hashExprList [.sym `quote, .lit l]
      | .quote se => do
        let quote ← hashSym `quote
        let sexpr ← hashSExpr se
        hashPtrList [quote, sexpr]
      | .cons    a b => hashExprList [.sym `cons,    a, b]
      | .strcons a b => hashExprList [.sym `strcons, a, b]
      | .hide    a b => hashExprList [.sym `hide,    a, b]
      | .ifE   a b c => hashExprList [.sym `if,   a, b, c]
      | .comm   expr => hashExprList [.sym `comm,   expr]
      | .atom   expr => hashExprList [.sym `atom,   expr]
      | .car    expr => hashExprList [.sym `car,    expr]
      | .cdr    expr => hashExprList [.sym `cdr,    expr]
      | .emit   expr => hashExprList [.sym `emit,   expr]
      | .commit expr => hashExprList [.sym `commit, expr]
      | e@(.begin ..) => hashExprList $ (.sym `begin) :: e.beginTelescope
      | .binaryOp op a b => hashExprList [.sym (toString op), a, b]
      | .lam args body => do
        let lambda ← hashExpr $ .sym `lambda
        let args ← hashExprList (args.map .sym)
        let body ← hashExpr body
        hashPtrList [lambda, args, body]
      | .letE    binders body => hashBlock `let    binders body
      | .letRecE binders body => hashBlock `letrec binders body
      | .mutRecE binders body => hashBlock `mutrec binders body
    modifyGet fun stt =>
      (ptr, { stt with exprCache := stt.exprCache.insert e ptr })

end

end Lurk.Hashing

open Lurk.Hashing in
def Lurk.Syntax.Expr.hash (e : Expr) : ScalarPtr × ScalarStore :=
  match StateT.run (hashExpr e) default with
  | (ptr, stt) => (ptr, stt.store)
