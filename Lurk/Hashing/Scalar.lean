import Lurk.AST
import Lurk.Utils
import Lurk.Hashing.Markers
import Poseidon.ForLurk

namespace Lurk

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Inhabited, Ord, BEq

def ScalarPtr.toString : ScalarPtr → String
  | ⟨.char, val⟩ => s!"⟪Char|{Char.ofNat val}⟫"
  | ptr => s!"⟪{ptr.tag}|{ptr.val}⟫"

instance : ToString ScalarPtr := ⟨ScalarPtr.toString⟩

inductive ScalarExpr
  | cons (car : ScalarPtr) (cdr : ScalarPtr)
  | comm (x : F) (ptr : ScalarPtr)
  | sym (sym : ScalarPtr)
  | «fun» (arg : ScalarPtr) (body : ScalarPtr) (env : ScalarPtr)
  | num (val : F)
  | strNil
  | strCons (head : ScalarPtr) (tail : ScalarPtr)
  | char (x : F)
  deriving BEq

def ScalarExpr.toString : ScalarExpr → String
  | .cons car cdr => s!"Cons {car} {cdr}"
  | .comm x   ptr => s!"Comm {x} {ptr}"
  | .sym ptr => s!"Sym {ptr}"
  | .fun arg body env => s!"Fun {arg} {body} {env}"
  | .num x => s!"Num {x}"
  | .strNil => "StrNil"
  | .strCons head tail => s!"StrCons {head} {tail}"
  | .char x => s!"Char {x}"

instance : ToString ScalarExpr := ⟨ScalarExpr.toString⟩

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Hash x.tag x.val y.tag y.val

open Std in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  deriving Inhabited

def ScalarStore.toString (s : ScalarStore) : String :=
  "\n\n".intercalate $ s.exprs.toList.map fun (k, v) => s!"{k}\n  ↳{v}"

instance : ToString ScalarStore := ⟨ScalarStore.toString⟩

open Std in
structure HashState where
  exprs       : RBMap ScalarPtr ScalarExpr compare
  charCache   : RBMap Char   ScalarPtr compare
  stringCache : RBMap String ScalarPtr compare
  deriving Inhabited

def HashState.store (stt : HashState) : ScalarStore :=
  ⟨stt.exprs⟩

abbrev HashM := StateM HashState

def addToStore (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr expr })

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
  | eq    => "EQ"

def SExpr.toExpr : SExpr → Expr
  | .lit l => .lit l
  | .cons a b => .cons a.toExpr (.cons b.toExpr (.lit .nil))

def mkExprFromBinders (binders : List (Name × Expr)) : Expr :=
  .mkList $ binders.map fun (n, e) => .mkList [.sym n, e]

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

partial def hashExpr : Expr → HashM ScalarPtr
  | .lit .nil => do
    let ptr ← hashString "NIL"
    addToStore ⟨Tag.nil, ptr.val⟩ (.sym ptr)
  | .lit .t => do
    let ptr ← hashString "T"
    addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | .lit (.num n) => addToStore ⟨Tag.num, n⟩ (.num n)
  | .lit (.str ⟨s⟩) => match s with
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
    let ptr ← hashString (name.toString false)
    addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | .cons    a b => do
    let aPtr ← hashExpr a
    let bPtr ← hashExpr b
    let ptr := ⟨Tag.cons, hashPtrPair aPtr bPtr⟩
    addToStore ptr (.cons aPtr bPtr)
  | .app fn none       => hashExpr $ .mkList [fn]
  | .app fn (some arg) => hashExpr $ .mkList [fn, arg]
  | .binaryOp op a b => hashExpr $ .mkList [.sym op.toString, a, b]
  | .quote se => hashExpr $ .mkList [.sym `QUOTE, se.toExpr]
  | .strcons a b => hashExpr $ .mkList [.sym `STRCONS, a, b]
  | .hide    a b => hashExpr $ .mkList [.sym `HIDE,    a, b]
  | .begin   a b => hashExpr $ .mkList [.sym `BEGIN,   a, b]
  | .comm   expr => hashExpr $ .mkList [.sym `COMM,   expr]
  | .atom   expr => hashExpr $ .mkList [.sym `ATOM,   expr]
  | .car    expr => hashExpr $ .mkList [.sym `CAR,    expr]
  | .cdr    expr => hashExpr $ .mkList [.sym `CDR,    expr]
  | .emit   expr => hashExpr $ .mkList [.sym `EMIT,   expr]
  | .commit expr => hashExpr $ .mkList [.sym `COMMIT, expr]
  | .currEnv => hashExpr $ .sym "CURRENT-ENV"
  | .ifE a b c => hashExpr $ .mkList [.sym `IF, a, b, c]
  | .lam args body => hashExpr $ .mkList [.sym `LAMBDA, .mkList $ args.map .sym, body]
  | .letE    binders body => hashExpr $ .mkList [.sym `LET,    mkExprFromBinders binders, body]
  | .letRecE binders body => hashExpr $ .mkList [.sym `LETREC, mkExprFromBinders binders, body]
  | .mutRecE binders body => hashExpr $ .mkList [.sym `MUTREC, mkExprFromBinders binders, body]

end

def Expr.hash (e : Expr) : ScalarStore × ScalarPtr := Id.run do
  match ← StateT.run (hashExpr e) default with
  | (ptr, stt) => (stt.store, ptr)

end Lurk
