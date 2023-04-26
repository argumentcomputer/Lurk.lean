import Lurk.New2.ExprPtrArith
import Lurk.New2.Store

open Std (RBMap)
open Store

structure Frame where
  expr      : ExprPtr
  env       : ExprPtr
  cont      : ContPtr
  continue? : Bool
  deriving BEq

def isTrivial (exprPtr : ExprPtr) : StoreM Bool :=
  match exprPtr.tag with
  | .num | .u64 | .char | .str | .comm | .fun => return true
  | .sym => return ((← getSym exprPtr) matches .nil | .t)
  | _ => return false

-- def mkThunk (exprPtr : ExprPtr) : StoreM ExprPtr := do
--   if exprPtr.tag == .thunk then unreachable!
--   if ← isTrivial exprPtr then return exprPtr
--   addToExprStore
--     ⟨.thunk, hash2 exprPtr.tag.toF exprPtr.val⟩
--     (.thunk exprPtr)

abbrev StepInto := ExprPtr → ContPtr → StoreM Frame

def finishUnOp (resPtr : ExprPtr) (op : UnOp) : StepInto := fun envPtr contPtr =>
  match op with
  | .car => return ⟨← car resPtr, envPtr, contPtr, false⟩
  | .emit => do dbg_trace (← printExprM resPtr); return ⟨resPtr, envPtr, contPtr, false⟩
  | .commit => return ⟨← hide .zero resPtr, envPtr, contPtr, false⟩
  | .open =>
    if resPtr.tag matches .comm | .num then
      return ⟨← openComm resPtr.val, envPtr, contPtr, false⟩
    else throw "Invalid input for open"

def finishBinOp (lPtr rPtr : ExprPtr) (op : BinOp) : StepInto := fun envPtr contPtr =>
  match op with
  | .add => return ⟨← lPtr.add rPtr, envPtr, contPtr, false⟩
  | .numEq => return ⟨← boolToExprPtr $ ← lPtr.numEq rPtr, envPtr, contPtr, false⟩

def saveEnv (envPtr : ExprPtr) (contPtr : ContPtr) : StoreM ContPtr :=
  if contPtr.tag == .env then pure contPtr
  else putCont1 .env envPtr contPtr

def intoUnOp (tag : ContTag) (tailPtr : ExprPtr) : StepInto := fun envPtr contPtr =>
  return ⟨← unfold1 tailPtr, envPtr, ← putCont0 tag contPtr, false⟩

def intoBinOp (tag : ContTag) (tailPtr : ExprPtr) : StepInto := fun envPtr contPtr => do
  let (x, y) ← unfold2 tailPtr
  let contPtr' ← putCont1 tag y contPtr
  return ⟨x, envPtr, contPtr', false⟩

def intoApp (fnPtr argsPtr : ExprPtr) : StepInto := fun envPtr contPtr =>
  return ⟨fnPtr, envPtr, ← putCont1 .appFn argsPtr contPtr, false⟩

def intoNextAppArg (fnPtr argsSymsPtr argsPtr bodyPtr funEnvPtr : ExprPtr) : StepInto :=
  fun envPtr contPtr => do match ← isNil argsSymsPtr, ← isNil argsPtr with
    | true,  true  => return ⟨bodyPtr, funEnvPtr, ← saveEnv envPtr contPtr, true⟩ -- fulfilled
    | false, true  => return ⟨fnPtr, envPtr, contPtr, true⟩ -- still missing args
    | true,  false => intoApp bodyPtr argsPtr envPtr contPtr -- auto-curry
    | false, false => -- currying
      let (argPtr, argsPtr) ← uncons argsPtr
      return ⟨argPtr, envPtr, ← putCont2 .appArg fnPtr argsPtr contPtr, true⟩

def intoIf (tailPtr : ExprPtr) : StepInto := fun envPtr contPtr => do
  let (propPtr, tailPtr) ← cadr tailPtr
  let (truePtr, tailPtr) ← cadr tailPtr
  let (falsePtr, tailPtr) ← cadr tailPtr
  if ← isNotNil tailPtr then throw "To many if arguments"
  return ⟨propPtr, envPtr, ← putCont2 .if truePtr falsePtr contPtr, false⟩

def intoLet (bindsPtr bodyPtr: ExprPtr) : StepInto := fun envPtr contPtr => do
  let bindPtr ← car bindsPtr
  let (_, bindExprPtr) ← unfold2 bindPtr
  return ⟨bindExprPtr, envPtr, ← putCont2 .let bindsPtr bodyPtr contPtr, false⟩

def intoLetrec (bindsPtr bodyPtr : ExprPtr) : StepInto := fun envPtr contPtr => do
  let bindPtr ← car bindsPtr
  let (_, bindExprPtr) ← unfold2 bindPtr
  return ⟨bindExprPtr, envPtr, ← putCont2 .letrec bindsPtr bodyPtr contPtr, false⟩

def intoLookup (symPtr envTailPtr : ExprPtr) : StepInto := fun envPtr contPtr =>
  if contPtr.tag == .lookup then -- don't stack lookup continuations
    return ⟨symPtr, envTailPtr, contPtr, false⟩
  else -- push a lookup continuation to save the original env
    return ⟨symPtr, envTailPtr, ← putCont1 .lookup envPtr contPtr, false⟩

def outOfLookup (valPtr : ExprPtr) : StepInto := fun envPtr contPtr => do
  if contPtr.tag == .lookup then
    let (envPtr₀, contPtr₀) ← getCont1 contPtr
    pure ⟨valPtr, envPtr₀, contPtr₀, false⟩
  else pure ⟨valPtr, envPtr, contPtr, false⟩

def insert (envPtr symPtr valPtr : ExprPtr) (recr : Bool := false) : StoreM ExprPtr := do
  if symPtr.tag != .sym then throw "Can't bind data to non-symbolic pointers"
  let entry ← cons symPtr valPtr
  if recr then cons (← cons entry (← putSym .nil)) envPtr
  else cons entry envPtr

def Frame.reduce (frm : Frame) : StoreM Frame := do
  match frm.expr.tag with
  | .num | .u64 | .char | .str | .comm | .fun => 
    return { frm with continue? := true }
  | .sym => do 
    if ← (isNil frm.expr <||> isT frm.expr) then
      return { frm with continue? := true }
    else if ← isNil frm.env then
       return ⟨frm.expr, frm.env, ⟨.err, .zero⟩, true⟩
    else -- look up in env
      let (car, restEnv) ← uncons frm.env
      let (x, V) ← uncons car
      let cont ← putCont3 .lookup x V restEnv frm.cont
      return ⟨frm.expr, ← putSym .nil, cont, true⟩
  | .cons =>
    let (head, tail) ← getCons frm.expr
    if head.tag == .sym then match ← getSym head with
      | .ofString "car" => intoUnOp (.unOp .car) tail frm.env frm.cont
      | .ofString "emit" => intoUnOp (.unOp .emit) tail frm.env frm.cont
      | .ofString "commit" => intoUnOp (.unOp .commit) tail frm.env frm.cont
      | .ofString "open" => intoUnOp (.unOp .open) tail frm.env frm.cont
      | .ofString "+" => intoBinOp (.binOp₁ .add) tail frm.env frm.cont
      | .ofString "=" => intoBinOp (.binOp₁ .numEq) tail frm.env frm.cont
      | .ofString "current-env" => sorry
      | .ofString "quote" =>
        return ⟨← unfold1 tail, ← putSym .nil, frm.cont, true⟩
      | .ofString "lambda" => sorry
      | .ofString "if" => intoIf tail frm.env frm.cont
      | .ofString "let" => sorry
      | .ofString "letrec" => sorry
      | _ => intoApp head tail frm.env frm.cont
    else intoApp head tail frm.env frm.cont

def Frame.continue (frm : Frame) : StoreM Frame := do
  match frm.cont.tag with
  | .halt => throw "Can't continue upon halt continuation"
  | .unOp op => finishUnOp frm.expr op frm.env (← getCont0 frm.cont)
  | .binOp₁ op =>
    let (y, contPtr) ← getCont1 frm.cont
    let x := frm.expr
    let envPtr := frm.env
    if ← isTrivial y then finishBinOp x y op envPtr contPtr -- skip trivial step
    else return ⟨y, envPtr, ← putCont1 (.binOp₂ op) x contPtr, false⟩
  | .binOp₂ op =>
    let (x, contPtr) ← getCont1 frm.cont
    finishBinOp x frm.expr op frm.env contPtr
  | .app =>
    let (fnPtr, argsPtr, contPtr) ← getCont2 frm.cont
    let (argsSymsPtr, funEnvPtr, bodyPtr) ← getFun fnPtr
    let (argSymPtr, argsSymsPtr') ← uncons argsSymsPtr
    let funEnvPtr' ← insert funEnvPtr argSymPtr frm.expr
    let fnPtr' ← mkFunPtr argsSymsPtr' funEnvPtr' bodyPtr
    intoNextAppArg fnPtr' argsSymsPtr' argsPtr bodyPtr funEnvPtr' frm.env contPtr
  | .if =>
    let (truePtr, falsePtr, contPtr) ← getCont2 frm.cont
    if ← isNil frm.expr then return ⟨falsePtr, frm.env, contPtr, false⟩
    else return ⟨truePtr, frm.env, contPtr, false⟩
  | .let =>
    let (bindsPtr, bodyPtr, contPtr) ← getCont2 frm.cont
    let (bindPtr, bindsPtr') ← uncons bindsPtr
    let (bindSymPtr, _) ← unfold2 bindPtr
    let envPtr ← insert frm.env bindSymPtr frm.expr
    if ← isNil bindsPtr' then return ⟨bodyPtr, envPtr, contPtr, false⟩
    intoLet bindsPtr' bodyPtr envPtr contPtr
  | .letrec =>
    let (bindsPtr, bodyPtr, contPtr) ← getCont2 frm.cont
    let (bindPtr, bindsPtr') ← uncons bindsPtr
    let (bindSymPtr, _) ← unfold2 bindPtr
    let envPtr ← insert frm.env bindSymPtr frm.expr true
    if ← isNil bindsPtr' then return ⟨bodyPtr, envPtr, contPtr, false⟩
    intoLetrec bindsPtr' bodyPtr envPtr contPtr
  | .err =>
    let (envPtr₀, contPtr) ← getCont1 frm.cont
    return ⟨frm.expr, envPtr₀, contPtr, false⟩
  | .lookup => unreachable! -- this is all dealt with in the step function

@[inline] def Frame.stepIntoParams (frm : Frame) : ExprPtr × ContPtr :=
  (frm.env, frm.cont)

@[inline] def Frame.withSavedEnv (frm : Frame) : StoreM Frame :=
  return { frm with cont := ← saveEnv frm.env frm.cont }

def Frame.step (frm : Frame) : StoreM Frame := do
    if frm.continue? then
      frm.continue
    else
      frm.reduce
  -- let frm' ← match frm.expr.tag with
  --   | .thunk =>
  --     let frm := { frm with expr := ← getThunk frm.expr }
  --     match frm.expr.tag with
  --     | .thunk => unreachable!
  --     | .num | .u64 | .char | .str | .comm | .fun => frm.continue
  --     | .sym =>
  --       let symPtr := frm.expr
  --       match ← getSym symPtr with
  --       | .nil | .t => frm.continue
  --       | sym =>
  --         -- make sure the env is not empty
  --         let envPtr := frm.env
  --         if ← isNil envPtr then throw s!"{sym} not found"
  --         -- unfold the head
  --         let contPtr := frm.cont
  --         let (headPtr, envTailPtr) ← uncons envPtr
  --         let (symOrEnvPtr, valPtr) ← uncons headPtr
  --         match symOrEnvPtr.tag with
  --         | .sym =>
  --           if symPtr != symOrEnvPtr then intoLookup symPtr envTailPtr envPtr contPtr
  --           else outOfLookup valPtr envPtr contPtr >>= Frame.continue
  --         | .cons => -- recursive env
  --           if ← isNotNil valPtr then throw "Malformed recursive env"
  --           let (symPtr', valPtr) ← uncons symOrEnvPtr
  --           if symPtr != symPtr' then intoLookup symPtr envTailPtr envPtr contPtr
  --           else
  --             let frm ← outOfLookup valPtr envPtr contPtr
  --             let frm ← if valPtr.tag == ExprTag.fun then
  --                 let (argsSymsPtr, funEnvPtr, bodyPtr) ← getFun valPtr
  --                 let fnPtr ← mkFunPtr argsSymsPtr (← cons headPtr funEnvPtr) bodyPtr
  --                 pure { frm with expr := fnPtr }
  --               else pure frm
  --             frm.continue
  --         | _ => throw "Malformed env"
  --     | .cons =>
  --       let (head, tail) ← getCons frm.expr
  --       if head.tag == .sym then match ← getSym head with
  --         | .ofString "car" => intoUnOp (.unOp .car) tail frm.env frm.cont
  --         | .ofString "emit" => intoUnOp (.unOp .emit) tail frm.env frm.cont
  --         | .ofString "commit" => intoUnOp (.unOp .commit) tail frm.env frm.cont
  --         | .ofString "open" => intoUnOp (.unOp .open) tail frm.env frm.cont
  --         | .ofString "+" => intoBinOp (.binOp₁ .add) tail frm.env frm.cont
  --         | .ofString "=" => intoBinOp (.binOp₁ .numEq) tail frm.env frm.cont
  --         | .ofString "current-env" =>
  --           if ← isNil tail then Frame.continue { frm with expr := frm.env }
  --           else throw ""
  --         | .ofString "quote" => Frame.continue { frm with expr := ← unfold1 tail }
  --         | .ofString "lambda" =>
  --           let (argsSymsPtr, bodyPtr) ← unfold2 tail
  --           let envPtr := frm.env
  --           let funPtr ← mkFunPtr argsSymsPtr envPtr bodyPtr
  --           pure ⟨funPtr, envPtr, frm.cont⟩ >>= Frame.continue
  --         | .ofString "if" => intoIf tail frm.env frm.cont
  --         | .ofString "let" =>
  --           let (bindsPtr, bodyPtr) ← unfold2 tail
  --           if ← isNil bindsPtr then pure { frm with expr := bodyPtr } else
  --           let frm ← frm.withSavedEnv; intoLet bindsPtr bodyPtr frm.env frm.cont
  --         | .ofString "letrec" =>
  --           let (bindsPtr, bodyPtr) ← unfold2 tail
  --           if ← isNil bindsPtr then pure { frm with expr := bodyPtr } else
  --           let frm ← frm.withSavedEnv; intoLetrec bindsPtr bodyPtr frm.env frm.cont
  --         | _ => intoApp head tail frm.env frm.cont
  --       else intoApp head tail frm.env frm.cont
  --   | _ => frm.continue
  -- else return frm'

def printFrame (i : Nat) (frm : Frame) : StoreM String := do
  let expr ← printExprM frm.expr
  let env ← printExprM frm.env
  let cont ← printCont frm.cont
  return s!"\nFrame {i}\nExpr: {expr}\nEnv:  {env}\nCont: {cont}"

def Frame.eval (frm : Frame) : StoreM $ ExprPtr × Array Frame := do
  let mut i := 0
  let mut frm := frm
  let mut frms := #[frm]
  dbg_trace ← printFrame i frm
  while true do
    i := i.succ
    frm ← frm.step
    frms := frms.push frm
    dbg_trace ← printFrame i frm
    if frm.cont.tag == .halt then break
  return (frm.expr, frms)

def LDON.evalM (ldon : LDON) : StoreM $ ExprPtr × Array Frame := do
  Frame.eval ⟨← putLDON ldon, ← putSym .nil, ⟨.halt, .zero⟩, false⟩

def LDON.eval (ldon : LDON) (store : Store := default) :
    Except String $ ExprPtr × (Array Frame) × Store :=
  match EStateM.run ldon.evalM store with
  | .ok (expr, frms) store => return (expr, frms, store)
  | .error err _ => throw err

open LDON.DSL
def main : IO Unit :=
  let code := ⟪
    -- (emit 123)
    -- (current-env)
    -- (car (current-env))
    (let ((a 1) (b a)) (current-env))
    -- (car (quote hi))
    -- (quote a)
    -- (quote (lambda (x) x))
    -- (let ((current_env (lambda () (current-env)))) (current_env))
    -- (let ((a 1) (b a)) (car (current-env)))
    -- (let ((a 1) (b a)) (current-env))
    -- (letrec ((rec (lambda (x) (if x t (rec t))))) (rec nil))
    -- (letrec ((count10 (lambda (i) (if (= i 10) i (count10 (+ i 1)))))) (count10 0))
    -- (letrec ((countX (lambda (i) (if (= i 3) i (countX (+ i 1)))))) (countX 0))
    -- (letrec ((countX (lambda (i j) (if (= i 5) i (countX (+ i 1) j))))) (countX 0 nil))
    -- (let ((a 1) (b a)) (+ b 1))
    -- (let ((a 1) (a 2)) a)
    -- ((lambda (i) (if (= i 10) i (+ i 1))) 0)
    -- ((lambda (a b c) nil) 1 2 3)
    -- ((((lambda (a b c) nil) 1) 2) 3)
    -- (+ (+ 1 1) (+ 1 1))
    -- 1
    -- (+ 1 1)
    -- (car nil)
    -- (if nil 1 (+ 1 2))
    -- (let () 2)
    -- ((lambda (x y) (+ x y)) (+ 1 1) 3)
    -- (((lambda (x y) (+ x y)) (+ 1 1)) 3)
    -- (let ((count10 (lambda (i) (if (= i 10) i (+ i 1))))) (count10 0))
    -- (let ((a 1) (b 2) (c 3)) a)
    -- (letrec ((a (+ 1 1))) a)
    -- (+ ((lambda (x) x) 1) x)
    -- (+ (let ((a 1)) a) a)
  ⟫
  match code.eval with
  | .ok (e, frms, store) => match store.printExpr e with
    | .ok res => IO.println s!"[{frms.size.pred} iterations] => {res}"
    | .error e => IO.println s!"Printing error: {e}"
  | .error e => IO.println s!"Error: {e}"

#eval main
