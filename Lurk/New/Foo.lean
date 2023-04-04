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

inductive Tag
  | cons | nil | num | u64 | char | str | comm | sym | «fun» | contRes
  | contAdd₁ | contAdd₂
  deriving Ord, BEq

def Tag.toF : Tag → F := sorry
--   | .cons  => .ofNat 0
--   | .nil   => .ofNat 1
--   | .num   => .ofNat 2
--   | .u64   => .ofNat 3
--   | .char  => .ofNat 4
--   | .str   => .ofNat 5
--   | .sym   => .ofNat 6
--   | .fun   => .ofNat 7
--   | .comm  => .ofNat 8

structure Ptr where
  tag : Tag
  val : F
  deriving Ord

inductive PtrImg
  -- expressions
  | cons : Ptr → Ptr → PtrImg
  | strCons : Ptr → Ptr → PtrImg
  | symCons : Ptr → Ptr → PtrImg
  | «fun» : Ptr → Ptr → Ptr → PtrImg
  | comm : F → Ptr → PtrImg
  | contRes : Ptr → PtrImg
  -- continuations
  | contUnOp : Ptr → Ptr → PtrImg
  | contBinOp₁ : Ptr → Ptr → Ptr → PtrImg
  | contBinOp₂ : Ptr → Ptr → Ptr → PtrImg

open Std (RBMap RBSet)

abbrev Store := RBMap Ptr PtrImg compare

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

def Store.getStr : Store → Ptr → String := sorry
def Store.getSym : Store → Ptr → Symbol := sorry

structure Cache where
  store : Store
  strs : RBMap Ptr String compare
  syms : RBMap Ptr Symbol compare
  strsMemo : RBMap String Ptr compare
  symsMemo : RBMap Symbol Ptr compare

abbrev Env := RBMap Symbol Ptr compare

abbrev EvalM := ReaderT Env $ EStateM String Cache

def getStr : Ptr → EvalM String := sorry
def getSym : Ptr → EvalM Symbol := sorry

def putStr : String → EvalM Ptr := sorry
def putSym : Symbol → EvalM Ptr := sorry

def unfold1 : Ptr → EvalM Ptr := sorry
def unfold2 : Ptr → EvalM (Ptr × Ptr) := sorry

def cdr : Ptr → EvalM Ptr := sorry

@[inline] def addToStore (ptr : Ptr) (img : PtrImg) : EvalM Ptr :=
  modifyGet fun c => (ptr, { c with store := c.store.insert ptr img })

structure State where
  expr : Ptr
  env  : Ptr
  cont : Ptr

def State.stepBinOp₁ (stt : State) (tag : Tag) (tailPtr: Ptr) : EvalM State := do
  let (x, y) ← unfold2 tailPtr
  let (envPtr, contPtr) := (stt.env, stt.cont)
  let contPtr ← addToStore
    ⟨tag, hash6 y.tag.toF y.val envPtr.tag.toF envPtr.val contPtr.tag.toF contPtr.val⟩
    (.contBinOp₁ y envPtr contPtr)
  return ⟨x, envPtr, contPtr⟩

def State.finish (stt : State) (valPtr? : Option Ptr) : EvalM State := do
  let valPtr := valPtr?.getD stt.expr
  let contPtr ← addToStore ⟨.contRes, hash2 valPtr.tag.toF valPtr.val⟩ (.contRes valPtr)
  return ⟨contPtr, stt.env, stt.cont⟩

def evalStep (stt : State) : EvalM State :=
  match stt.expr.tag with
  | .nil => do stt.finish (some $ ← putSym .nil)
  | .num | .u64 | .char | .str | .comm | .fun => stt.finish none
  | .sym => do match ← getSym stt.expr with
    | .nil | .t => stt.finish none
    | sym => match (← read).find? sym with
      | some valPtr => stt.finish (some valPtr)
      | none => throw s!"{sym} not found"
  | .cons => do match (← get).store.find? stt.expr with
    | some $ .cons head tail =>
      if head.tag == .sym then match ← getSym head with
        | sym! "+" => stt.stepBinOp₁ .contAdd₁ tail
        | sym => sorry
      else sorry
    | _ => throw ""
  | .contRes => do match (← get).store.find? stt.expr with
    | some $ .contRes valPtr => match stt.cont.tag with
      | _ => sorry
    | _ => throw ""
  | _ => throw ""
