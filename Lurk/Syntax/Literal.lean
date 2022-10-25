import Lurk.Arithmetic

open Std

namespace Lurk.Syntax

/-- Basic Lurk primitives -/
inductive Literal
  -- `t` `nil`
  | t | nil
  -- Numerical values
  | num  : F → Literal
  -- Strings
  | str  : String → Literal
  -- Characters
  | char : Char → Literal
  deriving Repr, BEq, Inhabited, Ord

namespace Literal 

def pprintLit : Literal → Format
  | .nil        => "nil"
  | .t          => "t"
  | .num n      => n.asHex
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

instance : ToFormat Literal where
  format := pprintLit

end Literal

def mkF (n : Nat) : F :=
  Fin.ofNat n

def mkNumLit (n : Nat) : Literal :=
  .num (Fin.ofNat n)

end Lurk.Syntax
