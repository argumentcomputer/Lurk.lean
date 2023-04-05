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
  | num | u64 | char | str | comm | «fun» | sym | cons
  deriving Ord, BEq

inductive ContTag
  | done
  | car
  | add₁ | add₂
  | app₁ | app₂
  deriving Ord, BEq

def ExprTag.toF : ExprTag → F := sorry

def ContTag.toF : ContTag → F := sorry

structure ExprPtr where
  tag : ExprTag
  val : F
  deriving Ord, BEq

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
  | cont0 : ContPtr → ContPtrImg
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

def ExprPtr.isNil (ptr : ExprPtr) : EvalM Bool :=
  return ptr == (← putSym .nil)

def ExprPtr.add : ExprPtr → ExprPtr → EvalM ExprPtr
  | ⟨.num, x⟩, ⟨.num, y⟩
  | ⟨.u64, x⟩, ⟨.num, y⟩
  | ⟨.num, x⟩, ⟨.u64, y⟩ => return ⟨.num, x + y⟩
  | ⟨.u64, x⟩, ⟨.u64, y⟩ => return ⟨.u64, .ofNat $ (x + y).val.toUInt64.toNat⟩
  | _, _ => throw ""

def unfold1 : ExprPtr → EvalM ExprPtr := sorry
def unfold2 : ExprPtr → EvalM (ExprPtr × ExprPtr) := sorry

def getExprPtrImg (ptr : ExprPtr) : EvalM ExprPtrImg := do
  match (← get).exprStore.find? ptr with
  | some img => pure img
  | none => throw ""

def getCont0 (contPtr : ContPtr) : EvalM ContPtr := do
  match (← get).contStore.find? contPtr with
  | some $ .cont0 a => return a
  | _ => throw ""

def getCont1 (contPtr : ContPtr) : EvalM (ExprPtr × ContPtr) := do
  match (← get).contStore.find? contPtr with
  | some $ .cont1 a b => return (a, b)
  | _ => throw ""

def getCont2 (contPtr : ContPtr) : EvalM (ExprPtr × ExprPtr × ContPtr) := do
  match (← get).contStore.find? contPtr with
  | some $ .cont2 a b c => return (a, b, c)
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

def State.intoUnOp (stt : State) (tag : ContTag) (tailPtr: ExprPtr) : EvalM State := do
  let x ← unfold1 tailPtr
  let contPtr := stt.cont
  let contPtr ← addToContStore
    ⟨tag, hash2 contPtr.tag.toF contPtr.val⟩
    (.cont0 contPtr)
  return ⟨x, stt.env, contPtr⟩

def State.intoApp (stt : State) (fnPtr argPtr : ExprPtr) : EvalM State := do
  let (envPtr, contPtr) := (stt.env, stt.cont)
  let contPtr ← addToContStore
    ⟨.app₁, hash6 argPtr.tag.toF argPtr.val envPtr.tag.toF envPtr.val contPtr.tag.toF contPtr.val⟩
    (.cont2 argPtr envPtr contPtr)
  return ⟨fnPtr, envPtr, contPtr⟩

def State.continue (stt : State) (valPtr? : Option ExprPtr := none) : EvalM State := do
  let valPtr := valPtr?.getD stt.expr
  match stt.cont.tag with
  | .done => return { stt with expr := valPtr}
  | .car =>
    let res ← match ← getExprPtrImg valPtr with
      | .cons x _ => pure x
      | _ => if ← valPtr.isNil then pure valPtr else throw ""
    return ⟨res, stt.env, ← getCont0 stt.cont⟩
  | .add₁ =>
    let (y, envPtr, contPtr) ← getCont2 stt.cont
    let contPtr ← addToContStore
      ⟨.add₂, hash4 valPtr.tag.toF valPtr.val contPtr.tag.toF contPtr.val⟩
      (.cont1 valPtr contPtr)
    return ⟨y, envPtr, contPtr⟩
  | .add₂ =>
    let (x, contPtr) ← getCont1 stt.cont
    return ⟨← x.add valPtr, stt.env, contPtr⟩
  | .app₁ => match ← getExprPtrImg valPtr with
    | .fun argsPtr funEnvPtr funBodyPtr =>
      let (argPtr, envPtr, contPtr) ← getCont2 stt.cont
      sorry
    | _ => throw ""
  | .app₂ => sorry

def State.step (stt : State) : EvalM State :=
  match stt.expr.tag with
  | .num | .u64 | .char | .str | .comm | .fun => stt.continue
  | .sym => do match ← getSym stt.expr with
    | .nil | .t => stt.continue
    | sym => match (← read).find? sym with
      | some valPtr => stt.continue (some valPtr)
      | none => throw s!"{sym} not found"
  | .cons => do match ← getExprPtrImg stt.expr with
    | .cons head tail =>
      -- check if tail is nil for app₀
      if head.tag == .sym then match ← getSym head with
        | sym! "car" => stt.intoUnOp .car tail
        | sym! "+" => stt.intoBinOp .add₁ tail
        | _ => stt.intoApp head tail
      else stt.intoApp head tail
    | _ => throw ""

def State.run (stt : State) : EvalM State := do
  let mut stt' := stt
  while stt'.cont.tag != .done do
    stt' ← stt'.step
  return stt'
