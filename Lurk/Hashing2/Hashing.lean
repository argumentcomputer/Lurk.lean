import Lurk.Arithmetic
import Lurk.Syntax2.DSL
import Std.Data.RBMap
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Lurk.Hashing

inductive Tag
  | nil | cons | sym | «fun» | num | thunk | str | char | comm
  deriving Ord, BEq, Inhabited

def Tag.toString : Tag → String
  | nil   => "nil"
  | cons  => "cons"
  | sym   => "sym"
  | .fun  => "fun"
  | num   => "num"
  | thunk => "thunk"
  | str   => "str"
  | char  => "char"
  | comm  => "comm"

instance : ToString Tag := ⟨Tag.toString⟩

def Tag.toF : Tag → F
  | .nil   => .ofNat 0
  | .cons  => .ofNat 1
  | .sym   => .ofNat 2
  | .fun   => .ofNat 3
  | .num   => .ofNat 4
  | .thunk => .ofNat 5
  | .str   => .ofNat 6
  | .char  => .ofNat 7
  | .comm  => .ofNat 8

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Ord, BEq, Inhabited

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

open Std (RBMap) in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  deriving Inhabited

instance : BEq ScalarStore where
  beq x y := x.exprs == y.exprs

def ScalarStore.ofList (exprs : List (ScalarPtr × ScalarExpr)) : ScalarStore :=
  ⟨.ofList exprs _⟩

open Std (RBMap) in
structure HashState where
  exprs       : RBMap ScalarPtr  ScalarExpr compare
  stringCache : RBMap String     ScalarPtr  compare
  astCache    : RBMap Syntax.AST ScalarPtr  compare
  deriving Inhabited

def HashState.store (stt : HashState) : ScalarStore :=
  ⟨stt.exprs⟩

def ScalarStore.toString (s : ScalarStore) : String :=
  let body := ",\n".intercalate $ s.exprs.toList.map fun (k, v) => s!"  {k}: {v}"
  "scalar_store: {\n" ++ body ++ "\n}"

instance : ToString ScalarStore := ⟨ScalarStore.toString⟩

abbrev HashM := StateM HashState

def addToStore (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr expr })

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

partial def hashString (s : String) : HashM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => 
    let ptr ← match s.data with
    | c :: cs => do
      let headPtr := ⟨.char, .ofNat c.toNat⟩
      let tailPtr ← hashString ⟨cs⟩
      let ptr := ⟨Tag.str, hashPtrPair headPtr tailPtr⟩
      let expr := .strCons headPtr tailPtr
      addToStore ptr expr 
    | [] => addToStore ⟨Tag.str, F.zero⟩ .strNil
    modifyGet fun stt =>
      (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def hashAST (x : Syntax.AST) : HashM ScalarPtr := do
  match (← get).astCache.find? x with
  | some ptr => pure ptr
  | none =>
    let ptr ← match x with
      | .nil
      | .sym "NIL" => do
        -- `nil` has its own tag instead of `.sym`. Thus we need to manually
        -- hash it as a string and make a `.nil` pointer with it
        let ptr ← hashString "NIL"
        addToStore ⟨Tag.nil, ptr.val⟩ (.sym ptr)
      | .num n => let n := .ofNat n; addToStore ⟨Tag.num, n⟩ (.num n)
      | .char c => return ⟨.char, .ofNat c.toNat⟩
      | .str s => hashString s
      | .sym s =>
        let ptr ← hashString s
        addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
      | .cons car cdr =>
        let car ← hashAST car
        let cdr ← hashAST cdr
        addToStore ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with astCache := stt.astCache.insert x ptr })

end Lurk.Hashing

open Lurk.Hashing in
def Lurk.Syntax.AST.hash (x : Syntax.AST) : ScalarPtr × ScalarStore :=
  match StateT.run (hashAST x.upper) default with
  | (ptr, stt) => (ptr, stt.store)
