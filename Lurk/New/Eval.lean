import Lurk.New.ExprPtrArith
import Lurk.New.Store

open Std (RBMap)
open Store

def car (exprPtr : ExprPtr) : StoreM ExprPtr := do
  match ← getExprPtrImg exprPtr with
  | .cons x _ => pure x
  | _ => if ← isNil exprPtr then pure exprPtr else throw "car failed"

def cdr (exprPtr : ExprPtr) : StoreM ExprPtr := do
  match ← getExprPtrImg exprPtr with
  | .cons _ x => pure x
  | _ => if ← isNil exprPtr then pure exprPtr else throw "cdr failed"

def cadr (exprPtr : ExprPtr) : StoreM $ ExprPtr × ExprPtr := do
  match ← getExprPtrImg exprPtr with
  | .cons x y => pure (x, y)
  | _ => if ← isNil exprPtr then pure (exprPtr, exprPtr) else throw "cadr failed"

def uncons (exprPtr : ExprPtr) : StoreM (ExprPtr × ExprPtr) := do
  match ← getExprPtrImg exprPtr with
  | .cons a b => pure (a, b)
  | _ => throw "uncons failed"

def unfold1 (exprPtr : ExprPtr) : StoreM ExprPtr := do
  let (car, cdr) ← uncons exprPtr
  if ← isNil cdr then return car
  throw "unfold1 failed"

def unfold2 (exprPtr : ExprPtr) : StoreM (ExprPtr × ExprPtr) := do
  let (car₁, cdr) ← uncons exprPtr
  let (car₂, cdr) ← uncons cdr
  if ← isNil cdr then return (car₁, car₂)
  throw "unfold2 failed"

def unfold3 (exprPtr : ExprPtr) : StoreM (ExprPtr × ExprPtr × ExprPtr) := do
  let (car₁, cdr) ← uncons exprPtr
  let (car₂, cdr) ← uncons cdr
  let (car₃, cdr) ← uncons cdr
  if ← isNil cdr then return (car₁, car₂, car₃)
  throw "unfold3 failed"

def insert (envPtr symPtr valPtr : ExprPtr) : StoreM ExprPtr := do
  let pair ← addToExprStore
    ⟨.cons, hash4 symPtr.tag.toF symPtr.val valPtr.tag.toF valPtr.val⟩
    (.cons symPtr valPtr)
  addToExprStore
    ⟨.cons, hash4 pair.tag.toF pair.val envPtr.tag.toF envPtr.val⟩
    (.cons pair envPtr)

-- eliminate this linear cost
partial def find? (envPtr symPtr : ExprPtr) : StoreM (Option ExprPtr) := do
  if ← isNil envPtr then return none
  let (head, tail) ← uncons envPtr
  let (symPtr', valPtr) ← cadr head
  if symPtr' == symPtr then return some valPtr
  find? tail symPtr

def getCont0 (contPtr : ContPtr) : StoreM ContPtr := do
  match (← get).contData.find? contPtr with
  | some $ .cont0 a => return a
  | _ => throw "getCont0 failed"

def getCont1 (contPtr : ContPtr) : StoreM (ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont1 a b => return (a, b)
  | _ => throw "getCont1 failed"

def getCont2 (contPtr : ContPtr) : StoreM (ExprPtr × ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont2 a b c => return (a, b, c)
  | _ => throw "getCont2 failed"

def getCont3 (contPtr : ContPtr) : StoreM (ExprPtr × ExprPtr × ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont3 a b c d => return (a, b, c, d)
  | _ => throw "getCont3 failed"

@[inline] def mkFunPtr (argsSymsPtr funEnvPtr bodyPtr : ExprPtr) : StoreM ExprPtr :=
  addToExprStore
    ⟨.fun, hash6 argsSymsPtr.tag.toF argsSymsPtr.val funEnvPtr.tag.toF funEnvPtr.val
      bodyPtr.tag.toF bodyPtr.val⟩
    (.fun argsSymsPtr funEnvPtr bodyPtr)

structure State where
  expr : ExprPtr
  env  : ExprPtr
  cont : ContPtr
  deriving BEq

instance : ToString State where
  toString x := s!"⟨{x.expr}, {x.cont}⟩"

abbrev StepInto := ExprPtr × ContPtr → StoreM State

def intoUnOp (tag : ContTag) (tailPtr : ExprPtr) : StepInto :=
  fun (envPtr, contPtr) => do
    let contPtr' ← addToContStore
      ⟨tag, hash2 contPtr.tag.toF contPtr.val⟩
      (.cont0 contPtr)
    return ⟨← unfold1 tailPtr, envPtr, contPtr'⟩

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
  let (propPtr, tailPtr) ← cadr tailPtr
  let (truePtr, tailPtr) ← cadr tailPtr
  let (falsePtr, tailPtr) ← cadr tailPtr
  if ← isNotNil tailPtr then throw "To many if arguments"
  let contPtr' ← addToContStore
    ⟨.if, hash6 truePtr.tag.toF truePtr.val falsePtr.tag.toF falsePtr.val
      contPtr.tag.toF contPtr.val⟩
    (.cont2 truePtr falsePtr contPtr)
  return ⟨propPtr, envPtr, contPtr'⟩

def intoLet (bindsPtr bodyPtr: ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  let bindPtr ← car bindsPtr
  let (_, bindExprPtr) ← unfold2 bindPtr
  let contPtr' ← addToContStore
    ⟨.let, hash6 bindsPtr.tag.toF bindsPtr.val bodyPtr.tag.toF bodyPtr.val
      contPtr.tag.toF contPtr.val⟩
    (.cont2 bindsPtr bodyPtr contPtr)
  return ⟨bindExprPtr, envPtr, contPtr'⟩

def intoLetrec (bindsPtr bodyPtr : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  let bindPtr ← car bindsPtr
  let (bindSymPtr, bindExprPtr) ← unfold2 bindPtr
  let contPtr' ← addToContStore
    ⟨.letrec, hash6 bindsPtr.tag.toF bindsPtr.val bodyPtr.tag.toF bodyPtr.val
      contPtr.tag.toF contPtr.val⟩
    (.cont2 bindsPtr bodyPtr contPtr)
  let thunkPtr ← addToExprStore
    ⟨.thunk, hash2 bindExprPtr.tag.toF bindExprPtr.val⟩
    (.thunk bindExprPtr)
  return ⟨bindExprPtr, ← insert envPtr bindSymPtr thunkPtr, contPtr'⟩

def intoNextAppArg (fnPtr argsSymsPtr argsPtr bodyPtr : ExprPtr) : StepInto :=
  fun (envPtr, contPtr) => do match ← isNil argsSymsPtr, ← isNil argsPtr with
    | true,  true  => return ⟨bodyPtr, envPtr, contPtr⟩ -- fulfilled
    | false, true  => return ⟨fnPtr, envPtr, contPtr⟩ -- still missing args
    | true,  false => throw "Too many arguments"
    | false, false => -- currying
      let (argPtr, argsPtr) ← uncons argsPtr
      let contPtr' ← addToContStore
        ⟨.appArg, hash6 fnPtr.tag.toF fnPtr.val argsPtr.tag.toF argsPtr.val
          contPtr.tag.toF contPtr.val⟩
        (.cont2 fnPtr argsPtr contPtr)
      return ⟨argPtr, envPtr, contPtr'⟩

def State.finishUnOp (stt : State) : UnOp → StoreM State
  | .car => return ⟨← car stt.expr, stt.env, ← getCont0 stt.cont⟩

def State.finishBinOp (stt : State) (op : BinOp) : StoreM State := do
  let ((x, contPtr), y) := (← getCont1 stt.cont, stt.expr)
  match op with
  | .add => return ⟨← x.add y, stt.env, contPtr⟩
  | .numEq => return ⟨← boolToExprPtr $ ← x.numEq y, stt.env, contPtr⟩

def State.continue (stt : State) : StoreM State := do
  match stt.cont.tag with
  | .neutral => return stt
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
      intoNextAppArg fnPtr argsSymsPtr argsPtr bodyPtr (funEnvPtr, contPtr)
    | _ => throw s!"Error evaluating app function. Head function expected"
  | .appArg =>
    let (fnPtr, argsPtr, contPtr) ← getCont2 stt.cont
    match ← getExprPtrImg fnPtr with
    | .fun argsSymsPtr funEnvPtr bodyPtr =>
      let (argSymPtr, argsSymsPtr) ← uncons argsSymsPtr
      let funEnvPtr ← insert funEnvPtr argSymPtr stt.expr
      let fnPtr' ← mkFunPtr argsSymsPtr funEnvPtr bodyPtr
      intoNextAppArg fnPtr' argsSymsPtr argsPtr bodyPtr (funEnvPtr, contPtr)
    | _ => throw "Error applying app argument. Head function expected"
  | .if =>
    let (truePtr, falsePtr, contPtr) ← getCont2 stt.cont
    if ← isNil stt.expr then return ⟨falsePtr, stt.env, contPtr⟩
    else return ⟨truePtr, stt.env, contPtr⟩
  | .let =>
    let (bindsPtr, bodyPtr, contPtr) ← getCont2 stt.cont
    let (bindPtr, bindsPtr') ← uncons bindsPtr
    let (bindSymPtr, _) ← unfold2 bindPtr
    let envPtr ← insert stt.env bindSymPtr stt.expr
    if ← isNil bindsPtr' then return ⟨bodyPtr, envPtr, contPtr⟩ else
    intoLet bindsPtr' bodyPtr (envPtr, contPtr)
  | .letrec =>
    let (bindsPtr, bodyPtr, contPtr) ← getCont2 stt.cont
    let (bindPtr, bindsPtr') ← uncons bindsPtr
    let (bindSymPtr, _) ← unfold2 bindPtr
    let envPtr ← insert stt.env bindSymPtr stt.expr
    if ← isNil bindsPtr' then return ⟨bodyPtr, envPtr, contPtr⟩ else
    intoLetrec bindsPtr' bodyPtr (envPtr, contPtr)
  | .env =>
    let (envPtr₀, contPtr) ← getCont1 stt.cont
    return ⟨stt.expr, envPtr₀, contPtr⟩

@[inline] def State.stepIntoParams (stt : State) : ExprPtr × ContPtr :=
  (stt.env, stt.cont)

def State.saveEnv (stt : State) : StoreM State := do
  let (envPtr, contPtr) := (stt.env, stt.cont)
  let contPtr' ← addToContStore
    ⟨.env, hash4 envPtr.tag.toF envPtr.val contPtr.tag.toF contPtr.val⟩
    (.cont1 envPtr contPtr)
  return { stt with cont := contPtr' }

def State.step (stt : State) : StoreM State := do
  match stt.expr.tag with
  | .num | .u64 | .char | .str | .comm | .fun => stt.continue
  | .sym =>
    let symPtr := stt.expr
    match ← getSym symPtr with
    | .nil | .t => stt.continue
    | sym => match ← find? stt.env symPtr with
      | some valPtr =>
        if valPtr.tag != .thunk then State.continue { stt with expr := valPtr }
        else return ⟨valPtr, ← insert stt.env symPtr valPtr, stt.cont⟩
      | none => throw s!"{sym} not found"
  | .thunk =>
    let .thunk expr ← getExprPtrImg stt.expr | throw "Expected thunk. Malformed store"
    return { stt with expr }
  | .cons =>
    let .cons head tail ← getExprPtrImg stt.expr
      | throw "Expected cons. Malformed store"
    if head.tag == .sym then match ← getSym head with
      | .ofString "car" => intoUnOp (.unOp .car) tail stt.stepIntoParams
      | .ofString "+" => intoBinOp (.binOp₁ .add) tail stt.stepIntoParams
      | .ofString "=" => intoBinOp (.binOp₁ .numEq) tail stt.stepIntoParams
      | .ofString "lambda" =>
        let (argsSymsPtr, bodyPtr) ← unfold2 tail
        let envPtr := stt.env
        let funPtr ← mkFunPtr argsSymsPtr envPtr bodyPtr
        return ⟨funPtr, envPtr, stt.cont⟩
      | .ofString "if" => intoIf tail stt.stepIntoParams
      | .ofString "let" =>
        let (bindsPtr, bodyPtr) ← unfold2 tail
        if ← isNil bindsPtr then return { stt with expr := bodyPtr }
        let stt ← stt.saveEnv
        intoLet bindsPtr bodyPtr stt.stepIntoParams
      | .ofString "letrec" =>
        let (bindsPtr, bodyPtr) ← unfold2 tail
        if ← isNil bindsPtr then return { stt with expr := bodyPtr }
        let stt ← stt.saveEnv
        intoLetrec bindsPtr bodyPtr stt.stepIntoParams
      | _ => let stt ← stt.saveEnv; intoApp head tail stt.stepIntoParams
    else let stt ← stt.saveEnv; intoApp head tail stt.stepIntoParams

def State.eval (stt : State) : StoreM $ ExprPtr × Array State := do
  let mut stt' := stt
  dbg_trace stt'
  let mut stts := #[stt]
  while true do
    let stt := stt'
    stt' ← stt.step
    if stt' == stt then break
    dbg_trace stt'
    stts := stts.push stt'
  return (stt'.expr, stts)

def LDON.evalM (ldon : LDON) : StoreM $ ExprPtr × Array State := do
  State.eval ⟨← putLDON ldon, ← putSym .nil, ⟨.neutral, .zero⟩⟩

def LDON.eval (ldon : LDON) (store : Store := default) :
    Except String $ ExprPtr × (Array State) × Store :=
  match EStateM.run ldon.evalM store with
  | .ok (expr, stts) store => return (expr, stts, store)
  | .error err _ => throw err

def test (ldon : LDON) : Except String Nat :=
  match ldon.eval with
  | .ok x => return x.2.1.size.pred
  | .error x => throw x

open LDON.DSL
def main : IO Unit :=
  let code := ⟪
    -- (letrec ((count10 (lambda (i) (if (= i 10) i (count10 (+ i 1)))))) (count10 0))
    -- (let ((a 1) (b a)) (+ b 1))
    -- ((lambda (i) (if (= i 10) i (+ i 1))) 0)
    -- (+ (+ 1 1) (+ 1 1))
    -- (+ ((lambda (x) x) 1) 2)
    -- (if nil 1 (+ 1 2))
    ((lambda (x y) (+ x y)) (+ 1 1) 3)
    -- (let ((count10 (lambda (i) (if (= i 10) i (+ i 1))))) (count10 0))
  ⟫
  match test code with
  | .ok e | .error e => IO.println e
