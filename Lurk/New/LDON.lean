import Lurk.Field

inductive Symbol
  | root
  | cons : String → Symbol → Symbol
  deriving Ord, BEq, Repr

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

inductive LDON
  | num : Lurk.F → LDON
  | u64 : UInt64 → LDON
  | char : Char → LDON
  | str : String → LDON
  | sym : Symbol → LDON
  | cons : LDON → LDON → LDON
  deriving Ord, BEq, Repr, Inhabited
