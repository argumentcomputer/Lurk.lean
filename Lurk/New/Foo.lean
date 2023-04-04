import Std.Data.RBMap
import Lurk.Field

open Lurk (F)

def hash2 : F → F → F := sorry
def hash3 : F → F → F → F := sorry
def hash4 : F → F → F → F → F := sorry
def hash5 : F → F → F → F → F → F := sorry
def hash6 : F → F → F → F → F → F → F := sorry
def hash7 : F → F → F → F → F → F → F → F := sorry
def hash8 : F → F → F → F → F → F → F → F → F := sorry

inductive ExprTag
  | cons | nil | num | u64 | char | str | comm | sym | «fun»
  deriving Ord, BEq

inductive ContTag
  | contEnd | contAdd₁ | contAdd₂
  deriving Ord, BEq

def ExprTag.toF : ExprTag → F := sorry

def ContTag.toF : ContTag → F := sorry

structure ExprPtr where
  tag : ExprTag
  val : F
  deriving Ord

inductive ExprPtrImg
  | cons : ExprPtr → ExprPtr → ExprPtrImg
  | strCons : ExprPtr → ExprPtr → ExprPtrImg
  | symCons : ExprPtr → ExprPtr → ExprPtrImg
  | «fun» : ExprPtr → ExprPtr → ExprPtr → ExprPtrImg
  | comm : F → ExprPtr → ExprPtrImg

structure ContPtr where
  tag : ContTag
  val : F
  deriving Ord

inductive ContPtrImg
  | cont1 : ExprPtr → ContPtr → ContPtrImg
  | cont2 : ExprPtr → ExprPtr → ContPtr → ContPtrImg

open Std (RBMap RBSet)

inductive Symbol
  | root
  | cons : String → Symbol → Symbol
  deriving Ord

def Symbol.toString : Symbol → String := sorry

instance : ToString Symbol := ⟨Symbol.toString⟩

@[inline] def Symbol.nil : Symbol :=
  .cons "nil" .root

@[inline] def Symbol.t : Symbol :=
  .cons "t" .root

@[match_pattern, inline] def sym! (s : String) : Symbol :=
  .cons s .root

structure Cache where
  exprStore : RBMap ExprPtr ExprPtrImg compare
  strs : RBMap ExprPtr String compare
  syms : RBMap ExprPtr Symbol compare
  strsMemo : RBMap String ExprPtr compare
  symsMemo : RBMap Symbol ExprPtr compare

  contStore : RBMap ContPtr ContPtrImg compare
  deriving Inhabited

abbrev Env := RBMap Symbol ExprPtr compare

abbrev EvalM := ReaderT Env $ EStateM String Cache

def getStr : ExprPtr → EvalM String := sorry
def getSym : ExprPtr → EvalM Symbol := sorry

def putStr : String → EvalM ExprPtr := sorry
def putSym : Symbol → EvalM ExprPtr := sorry

def unfold1 : ExprPtr → EvalM ExprPtr := sorry
def unfold2 : ExprPtr → EvalM (ExprPtr × ExprPtr) := sorry

def getCont2 (contPtr : ContPtr) : EvalM (ExprPtr × ExprPtr × ContPtr) := do
  match (← get).contStore.find? contPtr with
  | some $ .cont2 a b c => return (a, b, c)
  | _ => throw ""

def getCont1 (contPtr : ContPtr) : EvalM (ExprPtr × ContPtr) := do
  match (← get).contStore.find? contPtr with
  | some $ .cont1 a b => return (a, b)
  | _ => throw ""

@[inline] def addToExprStore (ptr : ExprPtr) (img : ExprPtrImg) : EvalM ExprPtr :=
  modifyGet fun c => (ptr, { c with exprStore := c.exprStore.insert ptr img })

@[inline] def addToContStore (ptr : ContPtr) (img : ContPtrImg) : EvalM ContPtr :=
  modifyGet fun c => (ptr, { c with contStore := c.contStore.insert ptr img })

structure State where
  expr : ExprPtr
  env  : ExprPtr
  cont : ContPtr

def State.intoBinOp (stt : State) (tag : ContTag) (tailPtr: ExprPtr) : EvalM State := do
  let (x, y) ← unfold2 tailPtr
  let (envPtr, contPtr) := (stt.env, stt.cont)
  let contPtr ← addToContStore
    ⟨tag, hash6 y.tag.toF y.val envPtr.tag.toF envPtr.val contPtr.tag.toF contPtr.val⟩
    (.cont2 y envPtr contPtr)
  return ⟨x, envPtr, contPtr⟩

def State.continue (stt : State) (valPtr? : Option ExprPtr) : EvalM State := do
  let valPtr := valPtr?.getD stt.expr
  match stt.cont.tag with
  | .contEnd => return { stt with expr := valPtr}
  | .contAdd₁ =>
    let (y, envPtr, contPtr) ← getCont2 stt.cont
    let contPtr ← addToContStore
      ⟨.contAdd₂, hash4 valPtr.tag.toF valPtr.val contPtr.tag.toF contPtr.val⟩
      (.cont1 valPtr contPtr)
    return ⟨y, envPtr, contPtr⟩
  | .contAdd₂ =>
    let (x, contPtr) ← getCont1 stt.cont
    return ⟨sorry, stt.env, contPtr⟩

def State.step (stt : State) : EvalM State :=
  match stt.expr.tag with
  | .nil => do stt.continue (some $ ← putSym .nil)
  | .num | .u64 | .char | .str | .comm | .fun => stt.continue none
  | .sym => do match ← getSym stt.expr with
    | .nil | .t => stt.continue none
    | sym => match (← read).find? sym with
      | some valPtr => stt.continue (some valPtr)
      | none => throw s!"{sym} not found"
  | .cons => do match (← get).exprStore.find? stt.expr with
    | some $ .cons head tail =>
      if head.tag == .sym then match ← getSym head with
        | sym! "+" => stt.intoBinOp .contAdd₁ tail
        | sym => sorry
      else sorry
    | _ => throw ""

def State.run (stt : State) : EvalM State := do
  let mut stt' := stt
  while stt'.cont.tag != .contEnd do
    stt' ← stt'.step
  return stt'
