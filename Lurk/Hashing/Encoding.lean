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

def encodeChar (c : Char) : HashM ScalarPtr := do
  match (← get).charCache.find? c with
  | some ptr => pure ptr
  | none =>
    let ptr := ⟨Tag.char, .ofNat c.toNat⟩
    modifyGet fun stt =>
      (ptr, { stt with charCache := stt.charCache.insert c ptr })

partial def encodeString (s : String) : HashM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => 
    let ptr ← match s.data with
    | c :: cs => do
      let headPtr ← encodeChar c
      let tailPtr ← encodeString ⟨cs⟩
      let ptr := ⟨Tag.str, hashPtrPair headPtr tailPtr⟩
      let expr := .strCons headPtr tailPtr
      addToStore ptr expr 
    | [] => addToStore ⟨Tag.str, F.zero⟩ .strNil
    modifyGet fun stt =>
      (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def encodeSym (s : Name) : HashM ScalarPtr := do 
  let ptr ← encodeString (s.toString false).toUpper
  addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)

open Lurk.Syntax.SExpr in
partial def encodeSExpr (s : SExpr) : HashM ScalarPtr := do 
  match (← get).sexprCache.find? s with 
  | some ptr => pure ptr
  | none => 
    let ptr ← match s with 
    | .lit .nil =>
      let ptr ← encodeString "NIL"
      addToStore ⟨Tag.nil, ptr.val⟩ (.sym ptr)
    | .lit .t => encodeSym `t
    | .lit (.num n) => addToStore ⟨Tag.num, n⟩ (.num n)
    | .lit (.str s) => encodeString s
    | .lit (.char c) => do
      let ptr ← encodeChar c
      addToStore ptr (.char ptr.val)
    | .sym s => encodeSym s
    | .cons e₁ e₂ => 
      let carPtr ← encodeSExpr e₁
      let cdrPtr ← encodeSExpr e₂
      let ptr := ⟨Tag.cons, hashPtrPair carPtr cdrPtr⟩
      let expr := .cons carPtr cdrPtr
      addToStore ptr expr
    modifyGet fun stt =>
      (ptr, { stt with sexprCache := stt.sexprCache.insert s ptr })

mutual

partial def encodePtrList (ps : List ScalarPtr) : HashM ScalarPtr := do
  ps.foldrM (init := ← encodeExpr $ .lit .nil) fun ptr acc =>
    addToStore ⟨.cons, hashPtrPair ptr acc⟩ (.cons ptr acc)

partial def encodeExprList (es : List Expr) : HashM ScalarPtr := do
  encodePtrList (← es.mapM encodeExpr)

partial def encodeBlock (kind : Name) (binders : List (Name × Expr)) (body : Expr) :
    HashM ScalarPtr := do
  let bodyPtr ← encodeExpr body
  let bindersPtr ← encodePtrList
    (← binders.mapM fun b => encodeExprList [.sym b.1, b.2])
  let headPtr ← encodeExpr $ .sym kind
  encodePtrList [headPtr, bindersPtr, bodyPtr]

/-- note on caching:
  `encodeExpr` doesn't have the best caching behavior with strings.
  Currently, when we hash a string `s`, we will first try to find `s`
  in `exprCache`, and call `encodeString` if we fail. In `encodeString`,
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
partial def encodeExpr (e : Expr) : HashM ScalarPtr := do
  match (← get).exprCache.find? e with
  | some ptr => pure ptr
  | none =>
    let ptr ← match e with
      | .lit .nil => do
        -- `nil` has its own tag instead of `.sym`. Thus we need to manually
        -- hash it as a string and make a `.nil` pointer with it
        let ptr ← encodeString "NIL"
        addToStore ⟨Tag.nil, ptr.val⟩ (.sym ptr)
      | .lit .t => encodeSym `t
      | .lit (.num n) => addToStore ⟨Tag.num, n⟩ (.num n)
      | .lit (.str s) => encodeString s
      | .lit (.char c) => encodeChar c
      | .sym name => encodeSym name
      | .currEnv => encodeExpr $ .sym "current-env"
      | .app fn none       => encodeExprList [fn]
      | e@(.app ..) => encodeExprList e.appTelescope
      | .quote (.lit l) => encodeExprList [.sym `quote, .lit l]
      | .quote se => do
        let quote ← encodeSym `quote
        let sexpr ← encodeSExpr se
        encodePtrList [quote, sexpr]
      | .cons    a b => encodeExprList [.sym `cons,    a, b]
      | .strcons a b => encodeExprList [.sym `strcons, a, b]
      | .hide    a b => encodeExprList [.sym `hide,    a, b]
      | .ifE   a b c => encodeExprList [.sym `if,   a, b, c]
      | .comm   expr => encodeExprList [.sym `comm,   expr]
      | .atom   expr => encodeExprList [.sym `atom,   expr]
      | .car    expr => encodeExprList [.sym `car,    expr]
      | .cdr    expr => encodeExprList [.sym `cdr,    expr]
      | .emit   expr => encodeExprList [.sym `emit,   expr]
      | .commit expr => encodeExprList [.sym `commit, expr]
      | e@(.begin ..) => encodeExprList $ (.sym `begin) :: e.beginTelescope
      | .binaryOp op a b => encodeExprList [.sym (toString op), a, b]
      | .lam args body => do
        let lambda ← encodeExpr $ .sym `lambda
        let args ← encodeExprList (args.map .sym)
        let body ← encodeExpr body
        encodePtrList [lambda, args, body]
      | .letE    binders body => encodeBlock `let    binders body
      | .letRecE binders body => encodeBlock `letrec binders body
      | .mutRecE binders body => encodeBlock `mutrec binders body
    modifyGet fun stt =>
      (ptr, { stt with exprCache := stt.exprCache.insert e ptr })

end

end Lurk.Hashing

open Lurk.Hashing in
def Lurk.Syntax.Expr.encode (e : Expr) : ScalarPtr × ScalarStore :=
  match StateT.run (encodeExpr e) default with
  | (ptr, stt) => (ptr, stt.store)
