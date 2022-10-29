import YatimaStdLib.Nat

namespace Lurk

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

abbrev F := Fin N

def F.ofNat (n : Nat) : F :=
  .ofNat n

def F.asHex (n : F) : String :=
  n.val.asHex 64

instance : Inhabited F := ⟨.ofNat 0⟩

def F.zero : F :=
  .ofNat 0

end Lurk
