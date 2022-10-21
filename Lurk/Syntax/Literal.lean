open Std

-- TODO: move
def Nat.asHex (n : Nat) : String := 
  if n < USize.size then 
    toString n 
  else 
    let tail := (Nat.toDigits 16 n)
    let pad := List.replicate (64 - tail.length) '0'
    "0x" ++  List.asString (pad ++ tail)

namespace Lurk

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

abbrev F := Fin N

instance : Inhabited F := ⟨.ofNat 0⟩

def F.zero : F :=
  .ofNat 0

def _root_.Fin.asHex (n : F) : String := n.val.asHex

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
  deriving Repr, BEq, Inhabited

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
