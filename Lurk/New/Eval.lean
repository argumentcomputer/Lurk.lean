import Std.Data.RBMap
import Lurk.New.Store

open Std (RBMap)

abbrev EvalM := EStateM String Store

def getStr (exprPtr : ExprPtr) : EvalM String := do
  match (← get).getStr exprPtr with
  | .ok s => pure s
  | .error e => throw e

def getSym (exprPtr : ExprPtr) : EvalM Symbol := do
  match (← get).getSym exprPtr with
  | .ok s => pure s
  | .error e => throw e

def putStr (str : String) : EvalM ExprPtr :=
  modifyGet fun store => store.putStr str

def putSym (sym : Symbol) : EvalM ExprPtr :=
  modifyGet fun store => store.putSym sym

def ExprPtr.isNil (ptr : ExprPtr) : EvalM Bool :=
  return ptr == (← putSym .nil)

def ExprPtr.add : ExprPtr → ExprPtr → EvalM ExprPtr
  | ⟨.num, x⟩, ⟨.num, y⟩
  | ⟨.u64, x⟩, ⟨.num, y⟩
  | ⟨.num, x⟩, ⟨.u64, y⟩ => return ⟨.num, x + y⟩
  | ⟨.u64, x⟩, ⟨.u64, y⟩ => return ⟨.u64, .ofNat $ (x + y).val.toUInt64.toNat⟩
  | _, _ => throw ""

def ExprPtr.numEq : ExprPtr → ExprPtr → EvalM ExprPtr
  | ⟨.num, x⟩, ⟨.num, y⟩
  | ⟨.u64, x⟩, ⟨.num, y⟩
  | ⟨.num, x⟩, ⟨.u64, y⟩
  | ⟨.u64, x⟩, ⟨.u64, y⟩ => if x == y then putSym .t else putSym .nil
  | _, _ => throw ""

def getExprPtrImg (ptr : ExprPtr) : EvalM ExprPtrImg := do
  match (← get).exprData.find? ptr with
  | some img => pure img
  | none => throw ""

def cadr (exprPtr : ExprPtr) : EvalM (ExprPtr × ExprPtr) := do
  match ← getExprPtrImg exprPtr with
  | .cons a b => pure (a, b)
  | _ => throw ""

def unfold1 (exprPtr : ExprPtr) : EvalM ExprPtr := do
  let (car, cdr) ← cadr exprPtr
  if ← cdr.isNil then return car
  throw ""

def unfold2 (exprPtr : ExprPtr) : EvalM (ExprPtr × ExprPtr) := do
  let (car₁, cdr) ← cadr exprPtr
  let (car₂, cdr) ← cadr cdr
  if ← cdr.isNil then return (car₁, car₂)
  throw ""

def unfold3 (exprPtr : ExprPtr) : EvalM (ExprPtr × ExprPtr × ExprPtr) := do
  let (car₁, cdr) ← cadr exprPtr
  let (car₂, cdr) ← cadr cdr
  let (car₃, cdr) ← cadr cdr
  if ← cdr.isNil then return (car₁, car₂, car₃)
  throw ""

@[inline] def addToExprStore (ptr : ExprPtr) (img : ExprPtrImg) : EvalM ExprPtr :=
  modifyGet fun c => (ptr, { c with exprData := c.exprData.insert ptr img })

@[inline] def addToContStore (ptr : ContPtr) (img : ContPtrImg) : EvalM ContPtr :=
  modifyGet fun c => (ptr, { c with contData := c.contData.insert ptr img })

def insert (envPtr symPtr valPtr : ExprPtr) : EvalM ExprPtr := do
  let pair ← addToExprStore
    ⟨.cons, hash4 symPtr.tag.toF symPtr.val valPtr.tag.toF valPtr.val⟩
    (.cons symPtr valPtr)
  addToExprStore
    ⟨.cons, hash4 pair.tag.toF pair.val envPtr.tag.toF envPtr.val⟩
    (.cons pair envPtr)

-- eliminate this linear cost
partial def find? (envPtr symPtr : ExprPtr) : EvalM (Option ExprPtr) := do
  if ← envPtr.isNil then return none
  let (head, tail) ← cadr envPtr
  let (symPtr', valPtr) ← unfold2 head
  if symPtr' == symPtr then return some valPtr
  find? tail symPtr

def getCont0 (contPtr : ContPtr) : EvalM ContPtr := do
  match (← get).contData.find? contPtr with
  | some $ .cont0 a => return a
  | _ => throw ""

def getCont1 (contPtr : ContPtr) : EvalM (ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont1 a b => return (a, b)
  | _ => throw ""

def getCont2 (contPtr : ContPtr) : EvalM (ExprPtr × ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont2 a b c => return (a, b, c)
  | _ => throw ""

def getCont3 (contPtr : ContPtr) : EvalM (ExprPtr × ExprPtr × ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont3 a b c d => return (a, b, c, d)
  | _ => throw ""

@[inline] def mkFunPtr (argsSymsPtr funEnvPtr bodyPtr : ExprPtr) : EvalM ExprPtr :=
  addToExprStore
    ⟨.fun, hash6 argsSymsPtr.tag.toF argsSymsPtr.val funEnvPtr.tag.toF funEnvPtr.val
      bodyPtr.tag.toF bodyPtr.val⟩
    (.fun argsSymsPtr funEnvPtr bodyPtr)

structure State where
  expr : ExprPtr
  env  : ExprPtr
  cont : ContPtr

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
  | .numEq => do
    let (x, contPtr) ← getCont1 stt.cont
    return ⟨← x.numEq stt.expr, stt.env, contPtr⟩

abbrev StepInto := ExprPtr × ContPtr → EvalM State

def intoUnOp (tag : ContTag) (tailPtr : ExprPtr) : StepInto :=
  fun (envPtr, contPtr) => do
    let contPtr ← addToContStore
      ⟨tag, hash2 contPtr.tag.toF contPtr.val⟩
      (.cont0 contPtr)
    return ⟨← unfold1 tailPtr, envPtr, contPtr⟩

def intoBinOp (tag : ContTag) (tailPtr : ExprPtr) : StepInto :=
  fun (envPtr, contPtr) => do
    let (x, y) ← unfold2 tailPtr
    let contPtr' ← addToContStore
      ⟨tag, hash4 y.tag.toF y.val contPtr.tag.toF contPtr.val⟩
      (.cont1 y contPtr)
    return ⟨x, envPtr, contPtr'⟩

def intoApp (fnPtr argsPtr : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  let contPtr' ← addToContStore
    ⟨.appFn, hash4 argsPtr.tag.toF argsPtr.val contPtr.tag.toF contPtr.val⟩
    (.cont1 argsPtr contPtr)
  return ⟨fnPtr, envPtr, contPtr'⟩

def intoIf (tailPtr : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  let (propPtr, truePtr, falsePtr) ← unfold3 tailPtr -- TODO : handle omitted args
  let contPtr' ← addToContStore
    ⟨.if, hash6 truePtr.tag.toF truePtr.val falsePtr.tag.toF falsePtr.val
      contPtr.tag.toF contPtr.val⟩
    (.cont2 truePtr falsePtr contPtr)
  return ⟨propPtr, envPtr, contPtr'⟩

def intoLet (bindsPtr bodyPtr : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  if ← bindsPtr.isNil then return ⟨bodyPtr, envPtr, contPtr⟩
  let (bindPtr, bindsPtr) ← cadr bindsPtr
  let (bindSymPtr, bindExprPtr) ← unfold2 bindPtr
  let contPtr' ← addToContStore
    ⟨.let, hash8 bindSymPtr.tag.toF bindSymPtr.val bindsPtr.tag.toF bindsPtr.val
      bodyPtr.tag.toF bodyPtr.val contPtr.tag.toF contPtr.val⟩
    (.cont3 bindSymPtr bindsPtr bodyPtr contPtr)
  return ⟨bindExprPtr, envPtr, contPtr'⟩

def intoLetrec (bindsPtr bodyPtr : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  if ← bindsPtr.isNil then return ⟨bodyPtr, envPtr, contPtr⟩
  let (bindPtr, bindsPtr) ← cadr bindsPtr
  let (bindSymPtr, bindExprPtr) ← unfold2 bindPtr
  let contPtr' ← addToContStore
    ⟨.letrec, hash8 bindSymPtr.tag.toF bindSymPtr.val bindsPtr.tag.toF bindsPtr.val
      bodyPtr.tag.toF bodyPtr.val contPtr.tag.toF contPtr.val⟩
    (.cont3 bindSymPtr bindsPtr bodyPtr contPtr)
  let envPtr' ← insert envPtr bindSymPtr bindExprPtr
  return ⟨bindExprPtr, envPtr', contPtr'⟩

def State.continue (stt : State) : EvalM State := do
  match stt.cont.tag with
  | .done => return stt
  | .unOp op => stt.finishUnOp op
  | .binOp₁ op =>
    let x := stt.expr
    let (y, contPtr) ← getCont1 stt.cont
    let contPtr' ← addToContStore
      ⟨.binOp₂ op, hash4 x.tag.toF x.val contPtr.tag.toF contPtr.val⟩
      (.cont1 x contPtr)
    return ⟨y, stt.env, contPtr'⟩
  | .binOp₂ op => stt.finishBinOp op
  | .appFn =>
    let fnPtr := stt.expr
    let (argsPtr, contPtr) ← getCont1 stt.cont
    match ← getExprPtrImg fnPtr with
    | .fun argsSymsPtr funEnvPtr bodyPtr =>
      match ← argsSymsPtr.isNil, ← argsPtr.isNil with
      | true,  true  => return ⟨bodyPtr, funEnvPtr, contPtr⟩ -- fulfilled
      | false, true  => return ⟨fnPtr, stt.env, contPtr⟩ -- still missing args
      | true,  false => throw "Too many arguments"
      | false, false => -- currying
        let (argPtr, argsPtr) ← cadr argsPtr
        let contPtr' ← addToContStore
          ⟨.appArg, hash6 fnPtr.tag.toF fnPtr.val argsPtr.tag.toF argsPtr.val
            contPtr.tag.toF contPtr.val⟩
          (.cont2 fnPtr argsPtr contPtr)
        return ⟨argPtr, stt.env, contPtr'⟩
    | _ => throw ""
  | .appArg =>
    let (fnPtr, argsPtr, contPtr) ← getCont2 stt.cont
    match ← getExprPtrImg fnPtr with
    | .fun argsSymsPtr funEnvPtr bodyPtr =>
      let (argSymPtr, argsSymsPtr) ← cadr argsSymsPtr
      let funEnvPtr ← insert funEnvPtr argSymPtr stt.expr
      let funPtr ← mkFunPtr argsSymsPtr funEnvPtr bodyPtr
      let contPtr' ← addToContStore
        ⟨.appFn, hash4 argsPtr.tag.toF argsPtr.val contPtr.tag.toF contPtr.val⟩
        (.cont1 argsPtr contPtr)
      return ⟨funPtr, stt.env, contPtr'⟩
    | _ => throw ""
  | .if =>
    let (truePtr, falsePtr, contPtr) ← getCont2 stt.cont
    if ← stt.expr.isNil then return ⟨falsePtr, stt.env, contPtr⟩
    else return ⟨truePtr, stt.env, contPtr⟩
  | .let =>
    let (bindSymPtr, bindsPtr, bodyPtr, contPtr) ← getCont3 stt.cont
    let envPtr ← insert stt.env bindSymPtr stt.expr
    intoLet bindsPtr bodyPtr (envPtr, contPtr)
  | .letrec =>
    let (bindSymPtr, bindsPtr, bodyPtr, contPtr) ← getCont3 stt.cont
    let envPtr ← insert stt.env bindSymPtr stt.expr
    intoLetrec bindsPtr bodyPtr (envPtr, contPtr)

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

@[inline] def State.stepIntoParams (stt : State) : ExprPtr × ContPtr :=
  (stt.env, stt.cont)

@[match_pattern, inline] def sym! (s : String) : Symbol :=
  .cons s .root

def State.step (stt : State) : EvalM State := do
  match ← stt.trivial? with
  | some stt => stt.continue
  | none => match stt.expr.tag with
    | .cons =>
      let .cons head tail ← getExprPtrImg stt.expr
        | throw "Expected cons. Malformed store"
      if head.tag == .sym then match ← getSym head with
        | sym! "car" => intoUnOp (.unOp .car) tail stt.stepIntoParams
        | sym! "+" => intoBinOp (.binOp₁ .add) tail stt.stepIntoParams
        | sym! "lambda" =>
          let (argsSymsPtr, bodyPtr) ← unfold2 tail
          let envPtr := stt.env
          let funPtr ← mkFunPtr argsSymsPtr envPtr bodyPtr
          pure ⟨funPtr, envPtr, stt.cont⟩
        | sym! "if" => intoIf tail stt.stepIntoParams
        | sym! "let" =>
          let (bindsPtr, bodyPtr) ← unfold2 tail
          intoLet bindsPtr bodyPtr stt.stepIntoParams
        | sym! "letrec" =>
          let (bindsPtr, bodyPtr) ← unfold2 tail
          intoLetrec bindsPtr bodyPtr stt.stepIntoParams
        | _ => intoApp head tail stt.stepIntoParams
      else intoApp head tail stt.stepIntoParams
    | _ => unreachable! -- trivial cases have already been dealt with

def State.run (stt : State) : EvalM State := do
  let mut stt' := stt
  while stt'.cont.tag != .done do
    stt' ← stt'.step
  return stt'
