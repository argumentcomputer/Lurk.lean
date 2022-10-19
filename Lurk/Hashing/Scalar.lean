import Lurk.AST
import Lurk.Utils
import Lurk.Hashing.Markers

namespace Lurk

/-- Use Poseidon -/
def hash4 : F → F → F → F → F := sorry

structure ScalarPtr where
  kind : F
  val  : F
  deriving Inhabited, Ord

inductive ScalarExpr
  | nil
  | cons (car : ScalarPtr) (cdr : ScalarPtr)
  | comm (x : F) (ptr : ScalarPtr)
  | sym (sym : ScalarPtr)
  | «fun» (arg : ScalarPtr) (body : ScalarPtr) (env : ScalarPtr)
  | num (val : F)
  | str (head : ScalarPtr) (tail : ScalarPtr)
  | char (x : F)

def hashPtrPair (x y : ScalarPtr) : F :=
  hash4 x.kind x.val y.kind y.val

open Std in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  deriving Inhabited

open Std in
structure HashState where
  exprs       : RBMap ScalarPtr ScalarExpr compare
  charCache   : RBMap Char   ScalarPtr compare
  stringCache : RBMap String ScalarPtr compare
  deriving Inhabited

def HashState.store (stt : HashState) : ScalarStore :=
  ⟨stt.exprs⟩

abbrev HashM := StateM HashState

def hashChar (c : Char) : HashM ScalarPtr := do
  match (← get).charCache.find? c with
  | some ptr => pure ptr
  | none =>
    let ptr := ⟨Tag.char, .ofNat c.val.toNat⟩
    modifyGet fun stt =>
      (ptr, { stt with charCache := stt.charCache.insert c ptr })

def hashString (s : String) : HashM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => match s with
    | ⟨[]⟩ => return ⟨Tag.str, F.zero⟩
    | ⟨c :: cs⟩ => do
      let head ← hashChar c
      let tail ← hashString ⟨cs⟩
      let ptr := ⟨Tag.str, hashPtrPair head tail⟩
      modifyGet fun stt =>
        (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def addToStore (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt =>
    (ptr, { stt with exprs := stt.exprs.insert ptr expr })

def BinaryOp.toString : BinaryOp → String
  | sum   => "+"
  | diff  => "-"
  | prod  => "*"
  | quot  => "/"
  | numEq => "="
  | lt    => "<"
  | gt    => ">"
  | le    => "<="
  | ge    => ">="
  | eq    => "eq"

partial def hashExpr : Expr → HashM ScalarPtr
  | .lit .nil => do addToStore ⟨Tag.nil, (← hashString "nil").val⟩ .nil
  | .lit .t => do
    let ptr ← hashString "t"
    addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | .lit (.num n) => addToStore ⟨Tag.num, n⟩ (.num n)
  | .lit (.str ⟨s⟩) => do
    let (headPtr, tailPtr) ← match s with
      | c :: cs => pure (← hashChar c, ← hashString ⟨cs⟩)
      | [] => pure (← hashString "", ⟨Tag.str, F.zero⟩)
    let ptr := ⟨Tag.str, hashPtrPair headPtr tailPtr⟩
    let expr := .str headPtr tailPtr
    addToStore ptr expr
  | .lit (.char c) => do
    let ptr ← hashChar c
    addToStore ptr (.char ptr.val)
  | .sym name => do
    let ptr ← hashString (name.toString false)
    addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | .binaryOp op a b => hashExpr $ .mkList [.sym $ .mkSimple op.toString, a, b]
  | .cons    a b => hashExpr $ .mkList [.sym `cons,    a, b]
  | .strcons a b => hashExpr $ .mkList [.sym `strcons, a, b]
  | .hide    a b => hashExpr $ .mkList [.sym `hide,    a, b]
  | .begin   a b => hashExpr $ .mkList [.sym `begin,   a, b]
  | .comm   expr => hashExpr $ .mkList [.sym `comm,   expr]
  | .atom   expr => hashExpr $ .mkList [.sym `atom,   expr]
  | .car    expr => hashExpr $ .mkList [.sym `car,    expr]
  | .cdr    expr => hashExpr $ .mkList [.sym `cdr,    expr]
  | .emit   expr => hashExpr $ .mkList [.sym `emit,   expr]
  | .commit expr => hashExpr $ .mkList [.sym `commit, expr]
  | .currEnv => do
    let ptr ← hashString "current-env"
    addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | _ => sorry

def Expr.hash (e : Expr) : ScalarStore × ScalarPtr := Id.run do
  match ← StateT.run (hashExpr e) default with
  | (ptr, stt) => (stt.store, ptr)

end Lurk
