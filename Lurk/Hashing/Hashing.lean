import Lurk.Hashing.HashM
import Poseidon.ForLurk

namespace Lurk.Hashing

open Lurk.Syntax

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

def destructSExpr : SExpr → List Expr
  | .lit  l   => [.lit l]
  | .cons a (.lit .nil) => destructSExpr a
  | .cons a b => destructSExpr a ++ destructSExpr b

def hashChar (c : Char) : HashM ScalarPtr := do
  match (← get).charCache.find? c with
  | some ptr => pure ptr
  | none =>
    let ptr := ⟨Tag.char, .ofNat c.val.toNat⟩
    modifyGet fun stt =>
      (ptr, { stt with charCache := stt.charCache.insert c ptr })

mutual

partial def hashString (s : String) : HashM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none =>
    let ptr ← hashExpr (.lit $ .str s)
    modifyGet fun stt =>
      (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

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
      | .lit .t => hashExpr $ .sym `t
      | .lit (.num n) => addToStore ⟨Tag.num, n⟩ (.num n)
      | .lit (.str s) => match s.data with
        | c :: cs => do
          let headPtr ← hashChar c
          let tailPtr ← hashString ⟨cs⟩
          let ptr := ⟨Tag.str, hashPtrPair headPtr tailPtr⟩
          let expr := .strCons headPtr tailPtr
          addToStore ptr expr
        | [] => addToStore ⟨Tag.str, F.zero⟩ .strNil
      | .lit (.char c) => do
        let ptr ← hashChar c
        addToStore ptr (.char ptr.val)
      | .sym name => do
        let ptr ← hashString (name.toString false).toUpper
        addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
      | .currEnv => hashExpr $ .sym "current-env"
      | .app fn none       => hashExprList [fn]
      | e@(.app ..) => hashExprList e.appTelescope
      | .quote (.lit l) => hashExprList [.sym `quote, .lit l]
      | .quote se => do
        let quote ← hashExpr $ .sym `quote
        let sexpr ← hashExprList $ destructSExpr se
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
        let ptr ← hashExpr body
        hashPtrList [lambda, args, ptr]
      | .letE    binders body => hashBlock `let    binders body
      | .letRecE binders body => hashBlock `letrec binders body
      | .mutRecE binders body => hashBlock `mutrec binders body
    modifyGet fun stt =>
      (ptr, { stt with exprCache := stt.exprCache.insert e ptr })

end

end Lurk.Hashing

open Lurk.Hashing in
def Lurk.Syntax.Expr.hash (e : Expr) : ScalarStore × ScalarPtr := Id.run do
  match ← StateT.run (hashExpr e) default with
  | (ptr, stt) => (stt.store, ptr)
