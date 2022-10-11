import Lean

open Lean Elab Meta Term

open Std
namespace Lurk

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

abbrev F := Fin N

def F.zero : F :=
  .ofNat 0

/-- Basic Lurk primitives -/
inductive Literal
  -- `t` `nil`
  | t | nil
  -- Numerical values
  | num  : Fin N → Literal
  -- Strings
  | str  : String → Literal
  -- Characters
  | char : Char → Literal
  deriving Repr, BEq, Inhabited

namespace Literal 

def pprintLit : Literal → Format
  | .nil        => "nil"
  | .t          => "t"
  | .num ⟨n, _⟩ => if n < USize.size then toString n else List.asString (Nat.toDigits 16 n)
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

instance : ToFormat Literal where
  format := pprintLit

end Literal

def mkNumLit (n : Nat) : Literal :=
  .num (Fin.ofNat n)

end Lurk
