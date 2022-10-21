import Lurk.Syntax.ExprUtils
import Lurk.Hashing.Markers
import Poseidon.ForLurk

namespace Lurk.Hashing

open Lurk.Syntax

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Inhabited, Ord, BEq

def ScalarPtr.toString : ScalarPtr → String
  | ⟨.num, n⟩ => s!"(num, {n.asHex})"
  | ⟨.char, val⟩ => s!"(char, \'{Char.ofNat val}\')"
  | ⟨tag, val⟩ => s!"({tag}, Scalar({val.asHex}))"

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
  | .cons car cdr => s!"Cons({car}, {cdr})"
  | .comm x   ptr => s!"Comm({x}, {ptr})"
  | .sym ptr => s!"Sym({ptr})"
  | .fun arg body env => s!"Fun({arg}, {body}, {env})"
  | .num x => s!"Num({x.asHex})"
  | .strNil => "StrNil"
  | .strCons head tail => s!"StrCons({head}, {tail})"
  | .char x => s!"Char({x})"

instance : ToString ScalarExpr := ⟨ScalarExpr.toString⟩

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Hash x.tag x.val y.tag y.val

open Std in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  deriving Inhabited

def ScalarStore.ofList (exprs : List (ScalarPtr × ScalarExpr)) : ScalarStore := 
  ⟨.ofList exprs⟩

def ScalarStore.toString (s : ScalarStore) : String :=
  "\n".intercalate $ s.exprs.toList.map fun (k, v) => s!"{k}: {v}"

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

def binOpToString : BinaryOp → String
  | .sum   => "+"
  | .diff  => "-"
  | .prod  => "*"
  | .quot  => "/"
  | .numEq => "="
  | .lt    => "<"
  | .gt    => ">"
  | .le    => "<="
  | .ge    => ">="
  | .eq    => "eq"

def destructSExpr : SExpr → List Expr
  | .lit l => [.lit l]
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

partial def hashBinder (binder : Name × Expr) : HashM ScalarPtr :=
  hashExprList [.sym binder.1, binder.2]

partial def hashBlock (kind : Name) (binders : List (Name × Expr)) (body : Expr) :
    HashM ScalarPtr := do
  let bodyPtr ← hashExpr body
  let bindersPtr ← hashPtrList (← binders.mapM hashBinder)
  let headPtr ← hashExpr $ .sym kind
  hashPtrList [headPtr, bindersPtr, bodyPtr]

partial def hashExpr : Expr → HashM ScalarPtr
  | .lit .nil => do
    -- `nil` has its own tag instead of `.sym`
    let ptr ← hashString "NIL"
    addToStore ⟨Tag.nil, ptr.val⟩ (.sym ptr)
  | .lit .t => hashExpr $ .sym `t
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
    let ptr ← hashString (name.toString false).toUpper
    addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | .currEnv => hashExpr $ .sym "current-env"
  | .app fn none       => hashExprList [fn]
  | .app fn (some arg) => hashExprList [fn, arg]
  | .quote    se => hashExprList $ (.sym `quote) :: (destructSExpr se)
  | .cons    a b => hashExprList [.sym `cons,    a, b]
  | .strcons a b => hashExprList [.sym `strcons, a, b]
  | .hide    a b => hashExprList [.sym `hide,    a, b]
  | .begin   a b => hashExprList [.sym `begin,   a, b]
  | .ifE   a b c => hashExprList [.sym `if,   a, b, c]
  | .comm   expr => hashExprList [.sym `comm,   expr]
  | .atom   expr => hashExprList [.sym `atom,   expr]
  | .car    expr => hashExprList [.sym `car,    expr]
  | .cdr    expr => hashExprList [.sym `cdr,    expr]
  | .emit   expr => hashExprList [.sym `emit,   expr]
  | .commit expr => hashExprList [.sym `commit, expr]
  | .binaryOp op a b => hashExprList [.sym (binOpToString op), a, b]
  | .lam args body => hashExprList $
    -- the `.lit .nil` compensates for the last cons element that should be in `args`
    (.sym `lambda) :: (args.map .sym) ++ [.lit .nil, body]
  | .letE    binders body => hashBlock `let    binders body
  | .letRecE binders body => hashBlock `letrec binders body
  | .mutRecE binders body => hashBlock `mutrec binders body

end

end Lurk.Hashing

open Lurk.Hashing in
def Lurk.Syntax.Expr.hash (e : Expr) : ScalarStore × ScalarPtr := Id.run do
  match ← StateT.run (hashExpr e) default with
  | (ptr, stt) => (stt.store, ptr)
