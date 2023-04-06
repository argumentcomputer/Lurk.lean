import Std.Data.RBMap
import Lurk.New.Tag

open Lurk (F)

def hash2 : F → F → F :=
  fun a b => a * b * b

def hash3 : F → F → F → F :=
  fun a b c => a * b * b * c * c * c

def hash4 : F → F → F → F → F :=
  fun a b c d => a * b * b * c * c * c * d * d * d * d
 
def hash6 : F → F → F → F → F → F → F :=
  fun a b c d e f => a * b * b * c * c * c * d * d * d * d * e * e * e * e * e
    * f * f * f * f * f * f

def hash8 : F → F → F → F → F → F → F → F → F :=
  fun a b c d e f g h => a * b * b * c * c * c * d * d * d * d * e * e * e * e * e
    * f * f * f * f * f * f * g * g * g * g * g * g * g
    * h * h * h * h * h * h * h * h

structure ExprPtr where
  tag : ExprTag
  val : F
  deriving Ord, BEq

structure ContPtr where
  tag : ContTag
  val : F
  deriving Ord

inductive ExprPtrImg
  | cons : ExprPtr → ExprPtr → ExprPtrImg
  | strCons : ExprPtr → ExprPtr → ExprPtrImg
  | symCons : ExprPtr → ExprPtr → ExprPtrImg
  | «fun» : ExprPtr → ExprPtr → ExprPtr → ExprPtrImg
  | comm : F → ExprPtr → ExprPtrImg

inductive ContPtrImg
  | cont0 : ContPtr → ContPtrImg
  | cont1 : ExprPtr → ContPtr → ContPtrImg
  | cont2 : ExprPtr → ExprPtr → ContPtr → ContPtrImg
  | cont3 : ExprPtr → ExprPtr → ExprPtr → ContPtr → ContPtrImg

open Std (RBMap)

inductive Symbol
  | root
  | cons : String → Symbol → Symbol
  deriving Ord

namespace Symbol

def telescope (acc : List String := []) : Symbol → List String
  | root => acc
  | cons str sym => sym.telescope $ str :: acc

def toString (sym : Symbol) : String :=
  ".".intercalate sym.telescope

instance : ToString Symbol := ⟨Symbol.toString⟩

@[inline] def nil : Symbol :=
  .cons "nil" .root

@[inline] def t : Symbol :=
  .cons "t" .root

end Symbol

structure Store where
  exprData : RBMap ExprPtr ExprPtrImg compare
  strs : RBMap ExprPtr String compare
  syms : RBMap ExprPtr Symbol compare
  strsMemo : RBMap String ExprPtr compare
  symsMemo : RBMap Symbol ExprPtr compare

  contData : RBMap ContPtr ContPtrImg compare

namespace Store

def getStr (store : Store) : ExprPtr → Except String String := sorry
def getSym (store : Store) : ExprPtr → Except String Symbol := sorry

def putStr (store : Store) : String → (ExprPtr × Store) := sorry
def putSym (store : Store) : Symbol → (ExprPtr × Store) := sorry

end Store
