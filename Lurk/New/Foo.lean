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

inductive UnOp
  | car
  deriving Ord, BEq

inductive BinOp
  | add
  deriving Ord, BEq

inductive ContTag
  | done
  | unOp : UnOp → ContTag
  | binOp₁ : BinOp → ContTag
  | binOp₂ : BinOp → ContTag
  | appFn | appArg
  deriving Ord, BEq

def ContTag.unOp? : ContTag → Option UnOp
  | .unOp op => some op
  | _ => none

def ContTag.binOp? : ContTag → Option BinOp
  | .binOp₁ op | .binOp₂ op => some op
  | _ => none

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

abbrev EvalM := EStateM String Cache

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
def cadr : ExprPtr → EvalM (ExprPtr × ExprPtr) := sorry

def getExprPtrImg (ptr : ExprPtr) : EvalM ExprPtrImg := do
  match (← get).exprStore.find? ptr with
  | some img => pure img
  | none => throw ""

def find? (envPtr symPtr : ExprPtr) : EvalM (Option ExprPtr) := sorry
def insert (envPtr symPtr valPtr : ExprPtr) : EvalM ExprPtr := sorry

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

def State.trivial? (stt : State) : EvalM $ Option State :=
  match stt.expr.tag with
  | .num | .u64 | .char | .str | .comm | .fun => return some stt
  | .sym => do
    let symPtr := stt.expr
    match ← getSym symPtr with
    | .nil | .t => return some stt
    | sym => match ← find? stt.env symPtr with
      | some symValPtr => return some { stt with expr := symValPtr }
      | none => throw s!"{sym} not found"
  | _ => return none

def State.finishUnOp (stt : State) : UnOp → EvalM State
  | .car => do
    let res := stt.expr
    let res ← match ← getExprPtrImg res with
      | .cons x _ => pure x
      | _ => if ← res.isNil then pure res else throw ""
    return ⟨res, stt.env, ← getCont0 stt.cont⟩

def State.finishBinOp (stt : State) : BinOp → EvalM State
  | .add => do
    let (x, contPtr) ← getCont1 stt.cont
    return ⟨← x.add stt.expr, stt.env, contPtr⟩

def State.intoUnOp (stt : State) (tag : ContTag) (tailPtr: ExprPtr) : EvalM State := do
  let contPtr := stt.cont
  let contPtr ← addToContStore
    ⟨tag, hash2 contPtr.tag.toF contPtr.val⟩
    (.cont0 contPtr)
  return ⟨← unfold1 tailPtr, stt.env, contPtr⟩

def State.intoBinOp (stt : State) (tag : ContTag) (tailPtr: ExprPtr) : EvalM State := do
  let (x, y) ← unfold2 tailPtr
  let contPtr := stt.cont
  let contPtr ← addToContStore
    ⟨tag, hash4 y.tag.toF y.val contPtr.tag.toF contPtr.val⟩
    (.cont1 y contPtr)
  return ⟨x, stt.env, contPtr⟩

def State.intoApp (stt : State) (fnPtr argsPtr : ExprPtr) : EvalM State := do
  let contPtr := stt.cont
  let contPtr ← addToContStore
    ⟨.appFn, hash4 argsPtr.tag.toF argsPtr.val contPtr.tag.toF contPtr.val⟩
    (.cont1 argsPtr contPtr)
  return ⟨fnPtr, stt.env, contPtr⟩

def State.continue (stt : State) : EvalM State := do
  match stt.cont.tag with
  | .done => return stt
  | .unOp op => stt.finishUnOp op
  | .binOp₁ op =>
    let x := stt.expr
    let (y, contPtr) ← getCont1 stt.cont
    let contPtr ← addToContStore
      ⟨.binOp₂ op, hash4 x.tag.toF x.val contPtr.tag.toF contPtr.val⟩
      (.cont1 x contPtr)
    return ⟨y, stt.env, contPtr⟩
  | .binOp₂ op => stt.finishBinOp op
  | .appFn =>
    let fnPtr := stt.expr
    let (argsPtr, contPtr) ← getCont1 stt.cont
    match ← getExprPtrImg fnPtr with
    | .fun argsSymsPtr funEnvPtr funBodyPtr =>
      match ← argsSymsPtr.isNil, ← argsPtr.isNil with
      | true,  true  => return ⟨funBodyPtr, funEnvPtr, contPtr⟩ -- fulfilled
      | false, true  => return ⟨fnPtr, stt.env, contPtr⟩        -- missing args
      | true,  false => throw "Too many arguments"
      | false, false => -- curry
        let (argPtr, argsPtr) ← cadr argsPtr
        let contPtr ← addToContStore
          ⟨.appArg, hash6 fnPtr.tag.toF fnPtr.val argsPtr.tag.toF argsPtr.val
            contPtr.tag.toF contPtr.val⟩
          (.cont2 fnPtr argsPtr contPtr)
        return ⟨argPtr, stt.env, contPtr⟩
    | _ => throw ""
  | .appArg =>
    let (fnPtr, argsPtr, contPtr) ← getCont2 stt.cont
    match ← getExprPtrImg fnPtr with
    | .fun argsSymsPtr funEnvPtr funBodyPtr =>
      let (argSymPtr, argsSymsPtr) ← cadr argsSymsPtr
      let funEnvPtr ← insert funEnvPtr argSymPtr stt.expr
      let funPtr ← addToExprStore
        ⟨.fun, hash6 argsSymsPtr.tag.toF argsSymsPtr.val funEnvPtr.tag.toF funEnvPtr.val
          funBodyPtr.tag.toF funBodyPtr.val⟩
        (.fun argsSymsPtr funEnvPtr funBodyPtr)
      let contPtr ← addToContStore
        ⟨.appFn, hash4 argsPtr.tag.toF argsPtr.val contPtr.tag.toF contPtr.val⟩
        (.cont1 argsPtr contPtr)
      return ⟨funPtr, stt.env, contPtr⟩
    | _ => throw ""

-- TODO : skip evaluation steps on before trivial cases
def State.step (stt : State) : EvalM State := do
  match ← stt.trivial? with
  | some stt => stt.continue
  | none => match stt.expr.tag with
    | .cons => do match ← getExprPtrImg stt.expr with
      | .cons head tail =>
        if head.tag == .sym then match ← getSym head with
          | sym! "car" => stt.intoUnOp (.unOp .car) tail
          | sym! "+" => stt.intoBinOp (.binOp₁ .add) tail
          | _ => stt.intoApp head tail
        else stt.intoApp head tail
      | _ => throw "Expected cons. Malformed store"
    | _ => unreachable! -- trivial

def State.run (stt : State) : EvalM State := do
  let mut stt' := stt
  while stt'.cont.tag != .done do
    stt' ← stt'.step
  return stt'
