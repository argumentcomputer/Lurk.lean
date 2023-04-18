import Std.Data.RBMap
import Poseidon.ForLurk
import Lurk.New.Pointers
import Lurk.New.LDON

open Lurk (F)

def hash2 : F → F → F := -- FIX
  fun a b => .ofNat $ (Poseidon.Lurk.hash3 a 256 b).norm

def hash3 : F → F → F → F :=
  fun a b c => .ofNat $ (Poseidon.Lurk.hash3 a b c).norm

def hash4 : F → F → F → F → F :=
  fun a b c d => .ofNat $ (Poseidon.Lurk.hash4 a b c d).norm

def hash6 : F → F → F → F → F → F → F := -- FIX
  fun a b c d e f => hash2 (hash3 a b c) (hash3 d e f)

inductive ExprPtrImg
  | cons : ExprPtr → ExprPtr → ExprPtrImg
  | «fun» : ExprPtr → ExprPtr → ExprPtr → ExprPtrImg

inductive ContPtrImg
  | cont0 : ContPtr → ContPtrImg
  | cont1 : ExprPtr → ContPtr → ContPtrImg
  | cont2 : ExprPtr → ExprPtr → ContPtr → ContPtrImg

open Std (RBMap)

structure Store where
  exprData : RBMap ExprPtr ExprPtrImg compare
  contData : RBMap ContPtr ContPtrImg compare

  chrsCache : RBMap (List Char) ExprPtr compare
  strsCache : RBMap (List String) ExprPtr compare

  ptrToStr : RBMap ExprPtr String compare
  strToPtr : RBMap String ExprPtr compare

  ptrToSym : RBMap ExprPtr Symbol compare
  symToPtr : RBMap Symbol ExprPtr compare

  comms : RBMap F ExprPtr compare
  deriving Inhabited

namespace Store

abbrev StoreM := EStateM String Store

instance : MonadLift (ExceptT String Id) StoreM where monadLift
  | .ok a => pure a
  | .error e => throw e

@[inline] def addToExprStore (ptr : ExprPtr) (img : ExprPtrImg) : StoreM ExprPtr :=
  modifyGet fun c => (ptr, { c with exprData := c.exprData.insert ptr img })

@[inline] def addToContStore (ptr : ContPtr) (img : ContPtrImg) : StoreM ContPtr :=
  modifyGet fun c => (ptr, { c with contData := c.contData.insert ptr img })

section Expressions

def putChars (cs : List Char) : StoreM ExprPtr := do
  match (← get).chrsCache.find? cs with
  | some ptr => pure ptr
  | none =>
    let ptr ← match cs with
      | [] => pure ⟨.str, F.zero⟩
      | c :: cs =>
        let headPtr := ⟨.char, .ofNat c.toNat⟩
        let tailPtr ← putChars cs
        addToExprStore
          ⟨.str, hash4 headPtr.tag.toF headPtr.val tailPtr.tag.toF tailPtr.val⟩
          (.cons headPtr tailPtr)
    modifyGet fun stt =>
      (ptr, { stt with chrsCache := stt.chrsCache.insert cs ptr })

def putStrings (ss : List String) : StoreM ExprPtr := do
  match (← get).strsCache.find? ss with
  | some ptr => return ptr
  | none =>
    let ptr ← ss.foldrM (init := ⟨.sym, F.zero⟩) fun s acc => do
      let strPtr ← putChars s.data
      addToExprStore
        ⟨.sym, hash4 strPtr.tag.toF strPtr.val acc.tag.toF acc.val⟩
        (.cons strPtr acc)
    modifyGet fun stt =>
      (ptr, { stt with strsCache := stt.strsCache.insert ss ptr })

def putStr (str : String) : StoreM ExprPtr := do
  match (← get).strToPtr.find? str with
  | some ptr => return ptr
  | none =>
    let ptr ← putChars str.data
    modifyGet fun store => (ptr, { store with
      ptrToStr := store.ptrToStr.insert ptr str
      strToPtr := store.strToPtr.insert str ptr })

def putSym (sym : Symbol) : StoreM ExprPtr := do
  match (← get).symToPtr.find? sym with
  | some ptr => return ptr
  | none =>
    let ptr ← putStrings sym.telescope
    modifyGet fun store => (ptr, { store with
      ptrToSym := store.ptrToSym.insert ptr sym
      symToPtr := store.symToPtr.insert sym ptr })

def putLDON : LDON → StoreM ExprPtr
  | .num n => pure ⟨.num, n⟩
  | .u64 n => pure ⟨.u64, .ofNat n.val⟩
  | .char n => pure ⟨.char, .ofNat n.toNat⟩
  | .str s => putStr s
  | .sym s => putSym s
  | .cons car cdr => do
    let car ← putLDON car
    let cdr ← putLDON cdr
    addToExprStore
      ⟨.cons, hash4 car.tag.toF car.val cdr.tag.toF cdr.val⟩
      (.cons car cdr)

def getExprPtrImg (ptr : ExprPtr) : StoreM ExprPtrImg := do
  match (← get).exprData.find? ptr with
  | some img => pure img
  | none => throw s!"Img not found for pointer {ptr}"

def getCons (ptr : ExprPtr) : StoreM $ ExprPtr × ExprPtr := do
  match ← getExprPtrImg ptr with
  | .cons x y => return (x, y)
  | _ => throw "Expected cons. Malformed store"

partial def getStr (ptr : ExprPtr) : StoreM String := do
  match (← get).ptrToStr.find? ptr with
  | some str => return str
  | none =>
    if ptr.tag != .str then throw "Invalid tag to retrieve a string"
    let str ← if ptr.val == .zero then pure "" else
      let (⟨.char, c⟩, ptr') ← getCons ptr
        | throw "Can't unfold str pointer correctly. Malformed store"
      let str' ← getStr ptr'
      pure ⟨.ofNat c.val :: str'.data⟩
    modifyGet fun store => (str, { store with
      ptrToStr := store.ptrToStr.insert ptr str
      strToPtr := store.strToPtr.insert str ptr })

partial def getSym (ptr : ExprPtr) : StoreM Symbol := do
  match (← get).ptrToSym.find? ptr with
  | some sym => return sym
  | none =>
    if ptr.tag != .sym then throw "Invalid tag to retrieve a symbol"
    let sym ← if ptr.val == .zero then pure .root else
      let (strPtr, ptr') ← getCons ptr
      let sym' ← getSym ptr'
      pure $ .cons (← getStr strPtr) sym'
    modifyGet fun store => (sym, { store with
      ptrToSym := store.ptrToSym.insert ptr sym
      symToPtr := store.symToPtr.insert sym ptr })

def getFun (ptr : ExprPtr) : StoreM $ ExprPtr × ExprPtr × ExprPtr := do
  match ← getExprPtrImg ptr with
  | .fun x y z => return (x, y, z)
  | _ => throw "Expected fun. Malformed store"

def hide (secret : F) (ptr : ExprPtr) : StoreM ExprPtr := do
  let hash := hash3 secret ptr.tag.toF ptr.val
  modifyGet fun store =>
    (⟨.comm, hash⟩, { store with comms := store.comms.insert hash ptr })

def openComm (hash : F) : StoreM ExprPtr := do
  match (← get).comms.find? hash with
  | some e => pure e
  | none => throw s!"Can't find commitment for {hash.asHex}"

@[inline] def isNil (ptr : ExprPtr) : StoreM Bool :=
  return ptr == (← putSym .nil)

@[inline] def isNotNil (ptr : ExprPtr) : StoreM Bool :=
  return ptr != (← putSym .nil)

@[inline] def boolToExprPtr (b : Bool) : StoreM ExprPtr :=
  if b then putSym .t else putSym .nil

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

@[inline] def cons (headPtr tailPtr : ExprPtr) : StoreM ExprPtr := do
  addToExprStore
    ⟨.cons, hash4 headPtr.tag.toF headPtr.val tailPtr.tag.toF tailPtr.val⟩
    (.cons headPtr tailPtr)

@[inline] def mkFunPtr (argsSymsPtr funEnvPtr bodyPtr : ExprPtr) : StoreM ExprPtr :=
  addToExprStore
    ⟨.fun, hash6 argsSymsPtr.tag.toF argsSymsPtr.val funEnvPtr.tag.toF funEnvPtr.val
      bodyPtr.tag.toF bodyPtr.val⟩
    (.fun argsSymsPtr funEnvPtr bodyPtr)

partial def telescopeCons (exprPtr : ExprPtr) (acc : Array ExprPtr := #[]) :
    StoreM $ Array ExprPtr × ExprPtr :=
  match exprPtr.tag with
  | .cons => do
    let (x, y) ← getCons exprPtr
    telescopeCons y (acc.push x)
  | _ => return (acc, exprPtr)

partial def printExprM (exprPtr : ExprPtr) : StoreM String :=
  match exprPtr.tag with
  | .num => return exprPtr.val.asHex
  | .u64 => return s!"{exprPtr.val.val}u64"
  | .char => return s!"\'{Char.ofNat exprPtr.val}\'"
  | .str => return s!"\"{← getStr exprPtr}\""
  | .sym => return ToString.toString $ ← getSym exprPtr
  | .cons => do
    let (es, e) ← telescopeCons exprPtr
    let esStr ← es.data.mapM printExprM
    let esStr := " ".intercalate esStr
    if ← isNil e then return s!"({esStr})" else return s!"({esStr} . {← printExprM e})"
  | .comm => return s!"<comm {exprPtr.val.asHex}>"
  | .fun => do
    let (args, _, body) ← getFun exprPtr
    return s!"<fun {← printExprM args} {← printExprM body}>"

def printExpr (store : Store) (exprPtr : ExprPtr) : Except String String :=
  match EStateM.run (printExprM exprPtr) store with
  | .error x _ => return s!"Error: {x}"
  | .ok x _ => return x

end Expressions

section Continuations

@[inline] def putCont0 (tag : ContTag) (contPtr : ContPtr) : StoreM ContPtr :=
  addToContStore ⟨tag, hash2 contPtr.tag.toF contPtr.val⟩ (.cont0 contPtr)

@[inline] def putCont1 (tag : ContTag) (e : ExprPtr) (contPtr : ContPtr) : StoreM ContPtr :=
  addToContStore
    ⟨tag, hash4 e.tag.toF e.val contPtr.tag.toF contPtr.val⟩
    (.cont1 e contPtr)

@[inline] def putCont2 (tag : ContTag) (e₁ e₂ : ExprPtr) (contPtr : ContPtr) : StoreM ContPtr :=
  addToContStore
    ⟨tag, hash6 e₁.tag.toF e₁.val e₂.tag.toF e₂.val contPtr.tag.toF contPtr.val⟩
    (.cont2 e₁ e₂ contPtr)

def getCont0 (contPtr : ContPtr) : StoreM ContPtr := do
  match (← get).contData.find? contPtr with
  | some $ .cont0 a => return a
  | _ => throw "Expected cont0. Malformed store"

def getCont1 (contPtr : ContPtr) : StoreM $ ExprPtr × ContPtr := do
  match (← get).contData.find? contPtr with
  | some $ .cont1 a b => return (a, b)
  | _ => throw "Expected cont1. Malformed store"

def getCont2 (contPtr : ContPtr) : StoreM $ ExprPtr × ExprPtr × ContPtr := do
  match (← get).contData.find? contPtr with
  | some $ .cont2 a b c => return (a, b, c)
  | _ => throw "Expected cont2. Malformed store"

def printCont (contPtr : ContPtr) : StoreM String :=
  if contPtr.tag == .halt then return "halt" else do
  match (← get).contData.find? contPtr with
  | some $ .cont0 c => return s!"{contPtr.tag} => {c.tag}"
  | some $ .cont1 e c => return s!"{contPtr.tag} | {← printExprM e} => {c.tag}"
  | some $ .cont2 e₁ e₂ c =>
    return s!"{contPtr.tag} | {← printExprM e₁} | {← printExprM e₂} => {c.tag}"
  | none => throw "Couldn't find continuation. Malformed store"

end Continuations

end Store
